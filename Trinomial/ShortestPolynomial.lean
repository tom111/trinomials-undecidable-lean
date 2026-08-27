import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

/-!
# The number of terms and the invariant `t(I)`

[§1].  A polynomial `f = Σ_{a ∈ supp f} c_a x^a` has `|supp f|` terms.  For an
ideal `I ⊆ K[x₁, …, x_m]`,

  `t(I) = min { |supp f| : 0 ≠ f ∈ I }`,   `t(0) = ∞`,

is the length of the shortest nonzero polynomial in `I`, and the decision problem
`t(I) ≤ k` asks for a nonzero element with at most `k` terms.  The paper's ideals live in
`ℚ[S, T, D₁, …, D_N]`; the definitions here are for an arbitrary polynomial ring
`MvPolynomial σ K`, exactly as in the paper's introduction.

* `HasShortPoly k I` — the problem `t(I) ≤ k`: `I` contains a nonzero polynomial with at
  most `k` terms.  Support means `MvPolynomial.support`, so equal monomials are collected
  and "the same monomial never appears in two or more terms".
* `tinv I` — the invariant `t(I) ∈ ℕ ∪ {∞}`.
* `tinv_le_iff` — `t(I) ≤ k ↔ HasShortPoly k I`; `tinv_bot` — `t(0) = ∞`;
  `tinv_eq_succ` — if `I` has no nonzero element with `≤ k` terms but one with `k + 1`
  terms, then `t(I) = k + 1`.
-/

set_option autoImplicit false

namespace Trinomial

variable {σ K : Type*} [CommSemiring K]

/-- The decision problem `t(I) ≤ k` of the paper [§1]: the ideal `I` contains a
nonzero polynomial with at most `k` (collected) terms. -/
def HasShortPoly (k : ℕ) (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∃ p ∈ I, p ≠ 0 ∧ p.support.card ≤ k

/-- The length `t(I) = min {|supp f| : 0 ≠ f ∈ I}` of the shortest nonzero polynomial of
`I`, with `t(0) = ∞` [§1]. -/
noncomputable def tinv (I : Ideal (MvPolynomial σ K)) : ℕ∞ :=
  ⨅ p : {p : MvPolynomial σ K // p ∈ I ∧ p ≠ 0}, (p.1.support.card : ℕ∞)

/-- `t(0) = ∞`. -/
theorem tinv_bot : tinv (⊥ : Ideal (MvPolynomial σ K)) = ⊤ := by
  rw [tinv, iInf_eq_top]
  rintro ⟨p, hp, hp0⟩
  exact absurd (Ideal.mem_bot.mp hp) hp0

/-- `t(I) ≤ k` iff `I` contains a nonzero polynomial with at most `k` terms. -/
theorem tinv_le_iff {I : Ideal (MvPolynomial σ K)} {k : ℕ} :
    tinv I ≤ k ↔ HasShortPoly k I := by
  constructor
  · intro h
    have h' : tinv I < (k + 1 : ℕ) := lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self k)
    rw [tinv, iInf_lt_iff] at h'
    obtain ⟨⟨p, hp, hp0⟩, hpk⟩ := h'
    exact ⟨p, hp, hp0, Nat.lt_succ_iff.mp (by exact_mod_cast hpk)⟩
  · rintro ⟨p, hp, hp0, hpk⟩
    exact (iInf_le _ ⟨p, hp, hp0⟩).trans (by exact_mod_cast hpk)

/-- If `I` has no nonzero element with at most `k` terms but one with `k + 1` terms, then
`t(I) = k + 1`. -/
theorem tinv_eq_succ {I : Ideal (MvPolynomial σ K)} (k : ℕ)
    (hk : ¬ HasShortPoly k I) (hk' : HasShortPoly (k + 1) I) : tinv I = k + 1 := by
  apply le_antisymm
  · exact_mod_cast tinv_le_iff.mpr hk'
  · rw [tinv, le_iInf_iff]
    rintro ⟨p, hp, hp0⟩
    have : k + 1 ≤ p.support.card := by
      by_contra h
      exact hk ⟨p, hp, hp0, by omega⟩
    exact_mod_cast this

theorem tinv_eq_three {I : Ideal (MvPolynomial σ K)}
    (h2 : ¬ HasShortPoly 2 I) (h3 : HasShortPoly 3 I) : tinv I = 3 :=
  tinv_eq_succ 2 h2 h3

theorem tinv_eq_four {I : Ideal (MvPolynomial σ K)}
    (h3 : ¬ HasShortPoly 3 I) (h4 : HasShortPoly 4 I) : tinv I = 4 :=
  tinv_eq_succ 3 h3 h4

/-- The value of `t(I)` on an ideal with no element of at most two terms, a quadrinomial,
and a trinomial exactly under a condition `c`: `t(I) = 3` if `c` holds and `4` otherwise.
This is the shape of the displayed formula of the introduction. -/
theorem tinv_eq_ite {I : Ideal (MvPolynomial σ K)} {c : Prop} [Decidable c]
    (h2 : ¬ HasShortPoly 2 I) (h3 : HasShortPoly 3 I ↔ c) (h4 : HasShortPoly 4 I) :
    tinv I = if c then 3 else 4 := by
  split_ifs with hc
  · exact tinv_eq_three h2 (h3.mpr hc)
  · exact tinv_eq_four (fun h => hc (h3.mp h)) h4

end Trinomial
