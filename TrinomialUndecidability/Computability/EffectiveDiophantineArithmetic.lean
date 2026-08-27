import TrinomialUndecidability.Computability.EffectiveDiophantine

/-!
# Exponent arithmetic for effective Diophantine syntax

This module supplies the exponent operations used by executable sparse polynomial
construction.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability

open scoped BigOperators

namespace EffDiophRel

/-- The exponent vector of a single source variable. -/
def variableExponent {n : ℕ} (i : Fin n) : IntExponent n :=
  fun j ↦ if j = i then 1 else 0

/-- Add exponent vectors, as used by multiplication of monomials. -/
def addExponent {n : ℕ} (e f : IntExponent n) : IntExponent n :=
  fun i ↦ e i + f i

@[simp]
theorem evalMonomial_variableExponent {n : ℕ} (i : Fin n) (x : Fin n → ℤ) :
    evalMonomial (variableExponent i) x = x i := by
  simp [evalMonomial, variableExponent]

theorem evalMonomial_addExponent {n : ℕ} (e f : IntExponent n) (x : Fin n → ℤ) :
    evalMonomial (addExponent e f) x = evalMonomial e x * evalMonomial f x := by
  simp [evalMonomial, addExponent, pow_add, Finset.prod_mul_distrib]

end EffDiophRel

end TrinomialUndecidability.Computability
