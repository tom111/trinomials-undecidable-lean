import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import TrinomialUndecidability.Computability.EffectiveDiophantineArithmetic

/-!
# Executable reindexing for effective Diophantine relations

Variable maps may identify source variables.  Reindexing therefore adds the exponents of
all variables in one fiber.  The executable definition uses only finite sums; finitely
supported functions occur solely in the semantic proof.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability

open scoped BigOperators

namespace EffDiophRel

/-- Push an exponent vector along an arbitrary finite variable map. -/
def reindexExponent {source target : ℕ} (index : Fin source → Fin target)
    (e : IntExponent source) : IntExponent target :=
  fun j ↦ ∑ i, if index i = j then e i else 0

/-- Reindex every monomial of an integer polynomial. -/
def reindexPolynomial {source target : ℕ} (index : Fin source → Fin target)
    (p : IntPolynomialCode source) : IntPolynomialCode target :=
  p.map fun term ↦ (reindexExponent index term.1, term.2)

/-- Reindexing a monomial is substitution by coordinate projections. -/
theorem evalMonomial_reindexExponent {source target : ℕ}
    (index : Fin source → Fin target) (e : IntExponent source) (x : Fin target → ℤ) :
    evalMonomial (reindexExponent index e) x = evalMonomial e (fun i ↦ x (index i)) := by
  classical
  let sourceFinsupp : Fin source →₀ ℕ := Finsupp.equivFunOnFinite.symm e
  let targetFinsupp : Fin target →₀ ℕ := Finsupp.mapDomain index sourceFinsupp
  have hsource (i : Fin source) : sourceFinsupp i = e i := rfl
  have htarget (j : Fin target) : targetFinsupp j = reindexExponent index e j := by
    simp [targetFinsupp, sourceFinsupp, Finsupp.mapDomain, Finsupp.sum_fintype,
      Finsupp.single_apply, reindexExponent]
  calc
    evalMonomial (reindexExponent index e) x =
        targetFinsupp.prod (fun j power ↦ x j ^ power) := by
      rw [Finsupp.prod_fintype]
      · simp [evalMonomial, htarget]
      · intro
        exact pow_zero _
    _ = sourceFinsupp.prod (fun i power ↦ x (index i) ^ power) := by
      exact Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _)
        (fun _ _ _ ↦ pow_add _ _ _)
    _ = evalMonomial e (fun i ↦ x (index i)) := by
      rw [Finsupp.prod_fintype]
      · simp [evalMonomial, hsource]
      · intro
        exact pow_zero _

/-- Polynomial evaluation commutes with executable variable reindexing. -/
theorem evalPolynomial_reindexPolynomial {source target : ℕ}
    (index : Fin source → Fin target) (p : IntPolynomialCode source)
    (x : Fin target → ℤ) :
    evalPolynomial (reindexPolynomial index p) x =
      evalPolynomial p (fun i ↦ x (index i)) := by
  induction p with
  | nil => simp [reindexPolynomial, evalPolynomial]
  | cons term p ih =>
      rcases term with ⟨e, c⟩
      change
        c * evalMonomial (reindexExponent index e) x +
            evalPolynomial (reindexPolynomial index p) x =
          c * evalMonomial e (fun i ↦ x (index i)) +
            evalPolynomial p (fun i ↦ x (index i))
      rw [evalMonomial_reindexExponent, ih]

/-- The exponent vector of the constant monomial `1`. -/
def zeroExponent (n : ℕ) : IntExponent n :=
  fun _ ↦ 0

@[simp]
theorem evalMonomial_zeroExponent {n : ℕ} (x : Fin n → ℤ) :
    evalMonomial (zeroExponent n) x = 1 := by
  simp [evalMonomial, zeroExponent]

end EffDiophRel

end TrinomialUndecidability.Computability
