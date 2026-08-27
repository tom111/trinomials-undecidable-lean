import Trinomial.Base.BaseIdeal

/-!
# Proposition 2.4: the short polynomials in `J₀`

[Proposition 2.4].  The base ideal contains no monomial and no binomial, and up to
units its trinomials are exactly the affine family `τ_d` and the infinite family
`θ_e^{p,q}`.  (Membership of the families and of the quadrinomial `Ω` is proved in
`Trinomial/Base/BaseIdeal.lean`.)

Everything runs through the membership criterion `mem_baseIdeal_iff`: an element lies in
`J₀` iff the `N+5` coordinates of its normal form vanish.  For a candidate short
polynomial `Σ cᵢ·mono xᵢ` these coordinates are, in the notation of the paper's proof
(`λᵢ = cᵢ 2^{−aᵢ−bᵢ}`, `rᵢ = aᵢ−bᵢ`, `sᵢ = aᵢ+bᵢ`):

* `(k=0)`  `Σ λᵢ = 0`   (after moving the paper's `1` to the left-hand side),
* `(k=1)`  `Σ λᵢ rᵢ = 0`,
* `(k=2)…(k=4)`  the higher coefficient equations,
* `(C_j)`  `Σ λᵢ dᵢⱼ = 0`.

For one or two terms these equations force the terms to collide — `no_monomial`,
`no_binomial`.  The three-term classification (`trinomial_in_baseIdeal`, proved in
`ShapeClassification.lean`) follows the paper's saturation/decomposition argument.
-/

set_option autoImplicit false

namespace Trinomial

open BaseAlgebra

variable {N : ℕ}

/-- No monomial lies in `J₀`  [Proposition 2.4 (i)]. -/
theorem no_monomial_in_baseIdeal {x : Exponent N} {c : ℚ} (hc : c ≠ 0) :
    AddMonoidAlgebra.single x c ∉ baseIdeal N := by
  rw [mem_baseIdeal_iff, baseEval_single, baseMonoUnit_val]
  intro h
  have h0 := congrArg BaseAlgebra.b0 h
  simp only [smul_b0, zero_b0, mul_one] at h0
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact hc h'
  · exact zpow_ne_zero _ (by norm_num : (1/2 : ℚ) ≠ 0) h'

/-- A nonzero element of `J₀` has at least two terms. -/
theorem one_lt_supportCard_of_mem_baseIdeal {f : Laurent N} (hf : f ∈ baseIdeal N)
    (hf0 : f ≠ 0) : 2 ≤ f.support.card := by
  by_contra h
  push_neg at h
  rcases (by omega : f.support.card = 0 ∨ f.support.card = 1) with h0 | h1
  · exact hf0 (Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp h0))
  · obtain ⟨x, hx, hf_eq⟩ := Finsupp.card_support_eq_one.mp h1
    rw [hf_eq] at hf
    exact no_monomial_in_baseIdeal hx hf

section Binomial

/-- The scale factor `λ = c·2^{−a−b}` attached to a term `c·S^aT^bD^d`
[proof of Proposition 2.4].  (An `abbrev`, so that `ring`-based tactics see
through it.) -/
abbrev lam (c : ℚ) (x : Exponent N) : ℚ := c * (1/2 : ℚ) ^ (x.s + x.t)

lemma lam_ne_zero {c : ℚ} (hc : c ≠ 0) (x : Exponent N) : lam c x ≠ 0 :=
  mul_ne_zero hc (zpow_ne_zero _ (by norm_num))

/-- The coordinatewise equations satisfied by a two-term element of `J₀` force its two
exponent vectors to coincide.  This is the computation behind Proposition 2.4 (i).
Only `cx ≠ 0` is needed: for `cy = 0` the equation `(k=0)` already contradicts `hmem`. -/
theorem exponents_eq_of_binomial_mem {x y : Exponent N} {cx cy : ℚ} (hcx : cx ≠ 0)
    (hmem : AddMonoidAlgebra.single x cx + AddMonoidAlgebra.single y cy ∈ baseIdeal N) :
    x = y := by
  rw [mem_baseIdeal_iff, map_add, baseEval_single, baseEval_single, baseMonoUnit_val,
    baseMonoUnit_val] at hmem
  -- coordinate equations
  have E0 : lam cx x + lam cy y = 0 := by
    have h := congrArg BaseAlgebra.b0 hmem
    simp only [add_b0, smul_b0, zero_b0, mul_one] at h
    linear_combination h
  have E1 : lam cx x * ((x.s : ℚ) - x.t) + lam cy y * ((y.s : ℚ) - y.t) = 0 := by
    have h := congrArg BaseAlgebra.b1 hmem
    simp only [add_b1, smul_b1, zero_b1, w1] at h
    linear_combination h
  have E2 : lam cx x * (((x.s : ℚ) - x.t) ^ 2 - ((x.s : ℚ) + x.t))
      + lam cy y * (((y.s : ℚ) - y.t) ^ 2 - ((y.s : ℚ) + y.t)) = 0 := by
    have h := congrArg BaseAlgebra.b2 hmem
    simp only [add_b2, smul_b2, zero_b2, w2] at h
    linear_combination 2 * h
  have Ec : ∀ j, lam cx x * (x.d j : ℚ) + lam cy y * (y.d j : ℚ) = 0 := by
    intro j
    have h := congrArg (fun z => BaseAlgebra.c z j) hmem
    simp only [add_c, smul_c, zero_c] at h
    linear_combination h
  have hlx := lam_ne_zero hcx x
  -- from (k=0) and (k=1): r_x = r_y
  have hr : (x.s : ℚ) - x.t = (y.s : ℚ) - y.t := by
    have h := mul_eq_zero.mp (show lam cx x * (((x.s : ℚ) - x.t) - ((y.s : ℚ) - y.t)) = 0
      by linear_combination E1 - ((y.s : ℚ) - y.t) * E0)
    rcases h with h | h
    · exact absurd h hlx
    · linarith [sub_eq_zero.mp h]
  -- from (k=0), (k=2) and r_x = r_y: s_x = s_y
  have hs : (x.s : ℚ) + x.t = (y.s : ℚ) + y.t := by
    have h := mul_eq_zero.mp
      (show lam cx x * (((y.s : ℚ) + y.t) - ((x.s : ℚ) + x.t)) = 0 by
        linear_combination E2 - (((y.s : ℚ) - y.t) ^ 2 - ((y.s : ℚ) + y.t)) * E0
          - lam cx x * (((x.s : ℚ) - x.t) + ((y.s : ℚ) - y.t)) * hr)
    rcases h with h | h
    · exact absurd h hlx
    · linarith [sub_eq_zero.mp h]
  -- from (C_j): d_x = d_y
  have hd : ∀ j, x.d j = y.d j := by
    intro j
    have h := mul_eq_zero.mp (show lam cx x * ((x.d j : ℚ) - (y.d j : ℚ)) = 0 by
      linear_combination Ec j - (y.d j : ℚ) * E0)
    rcases h with h | h
    · exact absurd h hlx
    · exact_mod_cast sub_eq_zero.mp h
  -- assemble
  have hxs : x.s = y.s := by
    have : (x.s : ℚ) = y.s := by linarith
    exact_mod_cast this
  have hxt : x.t = y.t := by
    have : (x.t : ℚ) = y.t := by linarith
    exact_mod_cast this
  ext
  · exact hxs
  · exact hxt
  · exact hd _

/-- No binomial lies in `J₀`  [Proposition 2.4 (i)]. -/
theorem no_binomial_in_baseIdeal {f : Laurent N} (hf : f ∈ baseIdeal N)
    (h2 : f.support.card = 2) : False := by
  obtain ⟨x, y, hxy, hsupp⟩ := Finset.card_eq_two.mp h2
  have hx : f x ≠ 0 := by
    rw [← Finsupp.mem_support_iff, hsupp]
    exact Finset.mem_insert_self x _
  have hf_eq : f = AddMonoidAlgebra.single x (f x) + AddMonoidAlgebra.single y (f y) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [Finsupp.sum, hsupp, Finset.sum_pair hxy]
  rw [hf_eq] at hf
  exact hxy (exponents_eq_of_binomial_mem hx hf)

end Binomial

end Trinomial
