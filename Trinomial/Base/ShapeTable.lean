import Mathlib.Tactic

/-!
# The integer solution table for the trinomial classification

[proof of Proposition 2.4, Case 2].  The elimination ideal of the affine prime
contains `s₁² − s₁s₂ + s₂² − 1` and (as the combination `v₁ − v₃ + v₆` of its
generators) `r₁² − r₁r₂ + r₂² − 3`.  Completing squares bounds integer solutions by
`|rᵢ| ≤ 2`, `|sᵢ| ≤ 1`, and enumeration of the box yields exactly the paper's six
solutions.
-/

set_option autoImplicit false

namespace Trinomial.ShapeCert

/-- The sum-of-squares bounds `|rᵢ| ≤ 2`, `|sᵢ| ≤ 1` for integer solutions
[the paper: "The sum-of-squares parts confine the possible integer solutions"]. -/
theorem solution_bounds (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (e4 : σ₁*σ₁ - σ₁*σ₂ + σ₂*σ₂ - 1 = 0)
    (esos : ρ₁*ρ₁ - ρ₁*ρ₂ + ρ₂*ρ₂ - 3 = 0) :
    -2 ≤ ρ₁ ∧ ρ₁ ≤ 2 ∧ -1 ≤ σ₁ ∧ σ₁ ≤ 1 ∧ -2 ≤ ρ₂ ∧ ρ₂ ≤ 2 ∧ -1 ≤ σ₂ ∧ σ₂ ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg (2*ρ₁ - ρ₂), sq_nonneg (2*ρ₂ - ρ₁), sq_nonneg (2*σ₁ - σ₂),
      sq_nonneg (2*σ₂ - σ₁), sq_nonneg (ρ₁ + ρ₂), sq_nonneg (ρ₁ - ρ₂),
      sq_nonneg (σ₁ + σ₂), sq_nonneg (σ₁ - σ₂)]

/-- Enumeration of the integer solutions of the elimination ideal: exactly the six
`(r₁, s₁, r₂, s₂)` of the paper's table  [proof of Proposition 2.4]. -/
theorem solution_table (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (e1 : ρ₂*ρ₂ + 2*σ₁ - σ₂ - 2 = 0)
    (e2 : σ₁*ρ₂ + ρ₁*σ₂ - ρ₂*σ₂ + ρ₂ = 0)
    (e3 : ρ₁*ρ₂ + σ₁ + σ₂ - 1 = 0)
    (e4 : σ₁*σ₁ - σ₁*σ₂ + σ₂*σ₂ - 1 = 0)
    (e5 : ρ₁*σ₁ - ρ₂*σ₂ - ρ₁ + ρ₂ = 0)
    (e6 : ρ₁*ρ₁ - σ₁ + 2*σ₂ - 2 = 0) :
    (ρ₁ = -2 ∧ σ₁ = 0 ∧ ρ₂ = -1 ∧ σ₂ = -1) ∨
    (ρ₁ = -1 ∧ σ₁ = -1 ∧ ρ₂ = -2 ∧ σ₂ = 0) ∨
    (ρ₁ = -1 ∧ σ₁ = 1 ∧ ρ₂ = 1 ∧ σ₂ = 1) ∨
    (ρ₁ = 1 ∧ σ₁ = 1 ∧ ρ₂ = -1 ∧ σ₂ = 1) ∨
    (ρ₁ = 1 ∧ σ₁ = -1 ∧ ρ₂ = 2 ∧ σ₂ = 0) ∨
    (ρ₁ = 2 ∧ σ₁ = 0 ∧ ρ₂ = 1 ∧ σ₂ = -1) := by
  have esos : ρ₁*ρ₁ - ρ₁*ρ₂ + ρ₂*ρ₂ - 3 = 0 := by linear_combination e1 - e3 + e6
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := solution_bounds ρ₁ σ₁ ρ₂ σ₂ e4 esos
  interval_cases ρ₁ <;> interval_cases σ₁ <;> interval_cases ρ₂ <;> interval_cases σ₂ <;>
    omega

end Trinomial.ShapeCert
