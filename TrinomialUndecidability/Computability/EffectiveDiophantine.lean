import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Executable effective Diophantine relations

Mathlib's proposition-valued `Dioph` API is an important semantic reference, but it does
not expose polynomial syntax or a computed finite witness arity.  This module starts a
parallel data-bearing API.  Polynomials are finite sparse lists with integer coefficients,
and every relation stores its auxiliary-variable count explicitly.

The representation intentionally permits duplicate monomials and zero coefficients.  Its
semantics collects them by integer addition; normalization is a later compiler layer.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability

open scoped BigOperators

/-- A dense exponent vector for a polynomial in exactly `n` variables. -/
abbrev IntExponent (n : ℕ) := Fin n → ℕ

/-- Executable sparse syntax for an integer polynomial in exactly `n` variables. -/
abbrev IntPolynomialCode (n : ℕ) := List (IntExponent n × ℤ)

/-- A finite system of integer-polynomial equations, each understood as `p = 0`. -/
abbrev IntPolynomialSystem (n : ℕ) := List (IntPolynomialCode n)

/-- Evaluate one monomial at an integer assignment. -/
def evalMonomial {n : ℕ} (e : IntExponent n) (x : Fin n → ℤ) : ℤ :=
  ∏ i, x i ^ e i

/-- Evaluate sparse integer-polynomial syntax.  The empty list denotes zero. -/
def evalPolynomial {n : ℕ} : IntPolynomialCode n → (Fin n → ℤ) → ℤ
  | [], _ => 0
  | (e, c) :: p, x => c * evalMonomial e x + evalPolynomial p x

/-- An assignment satisfies a system when every encoded polynomial evaluates to zero. -/
def Satisfies {n : ℕ} (system : IntPolynomialSystem n) (x : Fin n → ℤ) : Prop :=
  ∀ p ∈ system, evalPolynomial p x = 0

/-- Syntax-bearing Diophantine relation data with a computed auxiliary-variable count. -/
structure EffDiophRel (free : ℕ) where
  aux : ℕ
  eqs : IntPolynomialSystem (free + aux)

namespace EffDiophRel

/-- The integer relation denoted by effective Diophantine data. -/
def Realizes {free : ℕ} (R : EffDiophRel free) (x : Fin free → ℤ) : Prop :=
  ∃ y : Fin R.aux → ℤ, Satisfies R.eqs (Fin.append x y)

/-- Extend a left-system exponent into the shared conjunction layout.

The target layout is `free | left auxiliaries | right auxiliaries`.
-/
def liftLeftExponent {free leftAux rightAux : ℕ}
    (e : IntExponent (free + leftAux)) : IntExponent (free + (leftAux + rightAux)) :=
  Fin.addCases
    (fun i ↦ e (Fin.castAdd leftAux i))
    (Fin.addCases (fun i ↦ e (Fin.natAdd free i)) (fun _ ↦ 0))

/-- Extend a right-system exponent into the shared conjunction layout.

The target layout is `free | left auxiliaries | right auxiliaries`.
-/
def liftRightExponent {free leftAux rightAux : ℕ}
    (e : IntExponent (free + rightAux)) : IntExponent (free + (leftAux + rightAux)) :=
  Fin.addCases
    (fun i ↦ e (Fin.castAdd rightAux i))
    (Fin.addCases (fun _ ↦ 0) (fun i ↦ e (Fin.natAdd free i)))

/-- Rename a left-system polynomial into the shared conjunction layout. -/
def liftLeftPolynomial {free leftAux rightAux : ℕ}
    (p : IntPolynomialCode (free + leftAux)) :
    IntPolynomialCode (free + (leftAux + rightAux)) :=
  p.map fun term ↦ (liftLeftExponent (rightAux := rightAux) term.1, term.2)

/-- Rename a right-system polynomial into the shared conjunction layout. -/
def liftRightPolynomial {free leftAux rightAux : ℕ}
    (p : IntPolynomialCode (free + rightAux)) :
    IntPolynomialCode (free + (leftAux + rightAux)) :=
  p.map fun term ↦ (liftRightExponent (leftAux := leftAux) term.1, term.2)

theorem evalMonomial_liftLeft {free leftAux rightAux : ℕ}
    (e : IntExponent (free + leftAux)) (x : Fin free → ℤ)
    (y : Fin leftAux → ℤ) (z : Fin rightAux → ℤ) :
    evalMonomial (liftLeftExponent (rightAux := rightAux) e)
        (Fin.append x (Fin.append y z)) =
      evalMonomial e (Fin.append x y) := by
  simp [evalMonomial, liftLeftExponent, Fin.prod_univ_add]

theorem evalMonomial_liftRight {free leftAux rightAux : ℕ}
    (e : IntExponent (free + rightAux)) (x : Fin free → ℤ)
    (y : Fin leftAux → ℤ) (z : Fin rightAux → ℤ) :
    evalMonomial (liftRightExponent (leftAux := leftAux) e)
        (Fin.append x (Fin.append y z)) =
      evalMonomial e (Fin.append x z) := by
  simp [evalMonomial, liftRightExponent, Fin.prod_univ_add]

theorem evalPolynomial_liftLeft {free leftAux rightAux : ℕ}
    (p : IntPolynomialCode (free + leftAux)) (x : Fin free → ℤ)
    (y : Fin leftAux → ℤ) (z : Fin rightAux → ℤ) :
    evalPolynomial (liftLeftPolynomial (rightAux := rightAux) p)
        (Fin.append x (Fin.append y z)) =
      evalPolynomial p (Fin.append x y) := by
  induction p with
  | nil => simp [evalPolynomial, liftLeftPolynomial]
  | cons term p ih =>
      rcases term with ⟨e, c⟩
      change
        c * evalMonomial (liftLeftExponent (rightAux := rightAux) e)
              (Fin.append x (Fin.append y z)) +
            evalPolynomial (liftLeftPolynomial (rightAux := rightAux) p)
              (Fin.append x (Fin.append y z)) =
          c * evalMonomial e (Fin.append x y) + evalPolynomial p (Fin.append x y)
      rw [evalMonomial_liftLeft, ih]

theorem evalPolynomial_liftRight {free leftAux rightAux : ℕ}
    (p : IntPolynomialCode (free + rightAux)) (x : Fin free → ℤ)
    (y : Fin leftAux → ℤ) (z : Fin rightAux → ℤ) :
    evalPolynomial (liftRightPolynomial (leftAux := leftAux) p)
        (Fin.append x (Fin.append y z)) =
      evalPolynomial p (Fin.append x z) := by
  induction p with
  | nil => simp [evalPolynomial, liftRightPolynomial]
  | cons term p ih =>
      rcases term with ⟨e, c⟩
      change
        c * evalMonomial (liftRightExponent (leftAux := leftAux) e)
              (Fin.append x (Fin.append y z)) +
            evalPolynomial (liftRightPolynomial (leftAux := leftAux) p)
              (Fin.append x (Fin.append y z)) =
          c * evalMonomial e (Fin.append x z) + evalPolynomial p (Fin.append x z)
      rw [evalMonomial_liftRight, ih]

/-- The always-true relation, represented by the single equation `0 = 0`. -/
def zeroEquation (free : ℕ) : EffDiophRel free where
  aux := 0
  eqs := [[]]

@[simp]
theorem realizes_zeroEquation {free : ℕ} (x : Fin free → ℤ) :
    (zeroEquation free).Realizes x := by
  refine ⟨Fin.elim0, ?_⟩
  change Satisfies ([[]] : IntPolynomialSystem (free + 0)) (Fin.append x Fin.elim0)
  simp [Satisfies, evalPolynomial]

/-- Split a combined auxiliary assignment into its two blocks and append it back. -/
theorem append_aux_split {leftAux rightAux : ℕ} (z : Fin (leftAux + rightAux) → ℤ) :
    Fin.append (fun i ↦ z (Fin.castAdd rightAux i))
        (fun i ↦ z (Fin.natAdd leftAux i)) = z := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> simp

end EffDiophRel

end TrinomialUndecidability.Computability
