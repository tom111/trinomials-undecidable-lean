import Mathlib.Algebra.Order.Ring.Int
import TrinomialUndecidability.Computability.EffectiveDiophantineArithmetic

/-!
# Combining effective Diophantine systems into one equation

Sparse polynomial addition and multiplication deliberately retain duplicate monomials and
zero coefficients.  Their list semantics is exact, and a finite system is combined by a
sum of squares over `ℤ`.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability

namespace EffDiophRel

/-- Sparse polynomial addition before collection of duplicate monomials. -/
def addPolynomial {n : ℕ} (p q : IntPolynomialCode n) : IntPolynomialCode n :=
  p ++ q

/-- Multiply every term of `q` by one encoded monomial. -/
def monomialMulPolynomial {n : ℕ} (e : IntExponent n) (c : ℤ)
    (q : IntPolynomialCode n) : IntPolynomialCode n :=
  q.map fun term ↦ (addExponent e term.1, c * term.2)

/-- Sparse polynomial multiplication before collection of duplicate monomials. -/
def mulPolynomial {n : ℕ} : IntPolynomialCode n → IntPolynomialCode n → IntPolynomialCode n
  | [], _ => []
  | (e, c) :: p, q => addPolynomial (monomialMulPolynomial e c q) (mulPolynomial p q)

/-- The square of an executable sparse polynomial. -/
def squarePolynomial {n : ℕ} (p : IntPolynomialCode n) : IntPolynomialCode n :=
  mulPolynomial p p

/-- Sparse addition has exact additive evaluation semantics. -/
theorem eval_addPolynomial {n : ℕ} (p q : IntPolynomialCode n) (x : Fin n → ℤ) :
    evalPolynomial (addPolynomial p q) x = evalPolynomial p x + evalPolynomial q x := by
  induction p with
  | nil => simp [addPolynomial, evalPolynomial]
  | cons term p ih =>
      rcases term with ⟨e, c⟩
      simp only [addPolynomial, List.cons_append, evalPolynomial]
      rw [show evalPolynomial (p ++ q) x = evalPolynomial p x + evalPolynomial q x by
        simpa [addPolynomial] using ih]
      exact (add_assoc _ _ _).symm

/-- Multiplication by one encoded monomial has exact evaluation semantics. -/
theorem eval_monomialMulPolynomial {n : ℕ} (e : IntExponent n) (c : ℤ)
    (q : IntPolynomialCode n) (x : Fin n → ℤ) :
    evalPolynomial (monomialMulPolynomial e c q) x =
      (c * evalMonomial e x) * evalPolynomial q x := by
  induction q with
  | nil => simp [monomialMulPolynomial, evalPolynomial]
  | cons term q ih =>
      rcases term with ⟨f, d⟩
      change
        (c * d) * evalMonomial (addExponent e f) x +
            evalPolynomial (monomialMulPolynomial e c q) x =
          (c * evalMonomial e x) *
            (d * evalMonomial f x + evalPolynomial q x)
      rw [evalMonomial_addExponent, ih, mul_add]
      congr 1
      ac_rfl

/-- Sparse multiplication has exact multiplicative evaluation semantics. -/
theorem eval_mulPolynomial {n : ℕ} (p q : IntPolynomialCode n) (x : Fin n → ℤ) :
    evalPolynomial (mulPolynomial p q) x = evalPolynomial p x * evalPolynomial q x := by
  induction p with
  | nil => simp [mulPolynomial, evalPolynomial]
  | cons term p ih =>
      rcases term with ⟨e, c⟩
      rw [mulPolynomial, eval_addPolynomial, eval_monomialMulPolynomial, ih]
      rw [evalPolynomial, add_mul]

/-- Sparse squaring evaluates to the square of the original value. -/
theorem eval_squarePolynomial {n : ℕ} (p : IntPolynomialCode n) (x : Fin n → ℤ) :
    evalPolynomial (squarePolynomial p) x = evalPolynomial p x * evalPolynomial p x := by
  exact eval_mulPolynomial p p x

/-- Combine a finite system into the single equation given by its sum of squares. -/
def sumSquares {n : ℕ} : IntPolynomialSystem n → IntPolynomialCode n
  | [] => []
  | p :: system => addPolynomial (squarePolynomial p) (sumSquares system)

/-- Evaluation of the encoded sum of squares is nonnegative over the integers. -/
theorem eval_sumSquares_nonneg {n : ℕ} (x : Fin n → ℤ) :
    ∀ system : IntPolynomialSystem n, 0 ≤ evalPolynomial (sumSquares system) x
  | [] => le_rfl
  | p :: system => by
      rw [sumSquares, eval_addPolynomial, eval_squarePolynomial]
      exact add_nonneg (mul_self_nonneg _) (eval_sumSquares_nonneg x system)

/-- Over `ℤ`, the combined equation vanishes exactly when every source equation does. -/
theorem eval_sumSquares_eq_zero_iff_satisfies {n : ℕ}
    (system : IntPolynomialSystem n) (x : Fin n → ℤ) :
    evalPolynomial (sumSquares system) x = 0 ↔ Satisfies system x := by
  induction system with
  | nil => simp [sumSquares, evalPolynomial, Satisfies]
  | cons p system ih =>
      rw [sumSquares, eval_addPolynomial, eval_squarePolynomial]
      rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (eval_sumSquares_nonneg x system)]
      rw [mul_self_eq_zero, ih]
      simp [Satisfies]

end EffDiophRel

end TrinomialUndecidability.Computability
