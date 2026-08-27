import Trinomial.Base.Shape
import Trinomial.Base.ShapeTable
import Trinomial.Base.ShapeCertificates

/-!
# Proposition 2.4 (ii): classification of the trinomials in `J₀`

[Proposition 2.4].  Up to a nonzero scalar and a Laurent monomial, every
three-term element of `J₀` is an affine trinomial `τ_d` or an infinite trinomial
`θ_e^{p,q}` (`e ≠ 0`, `p ≠ q` both nonzero).

The proof follows the paper.  A trinomial with support `{x₀, x₁, x₂}` is normalized by
the unit `(f x₀)⁻¹ · mono (−x₀)` to the form `1 − c₁·mono y₁ − c₂·mono y₂`; membership
in `J₀` then reads off the equations `(k=0) … (k=4)` and `(C_j)` via the normal form
(`mem_baseIdeal_iff`).  The saturation of these equations at `λ₁λ₂` decomposes into two
primes:

* **Case 1** (`r₁ = s₁ = r₂ = s₂ = 0`): both non-constant terms are pure `D`-monomials;
  the `(C_j)` equations force their exponents collinear, and writing the ratio in
  lowest terms produces the infinite trinomial.  (The paper takes `e` primitive via a
  gcd; here `e, p, q` are produced from `Rat.num`/`Rat.den` of the coefficient ratio,
  which avoids Bézout for families and is enough for everything downstream.)
* **Case 2** (some `rᵢ, sᵢ ≠ 0`): the Macaulay2 certificates
  (`Trinomial/Base/ShapeCertificates.lean`, auto-generated) force the six elimination-ideal
  equations; the sum-of-squares bounds and integer enumeration
  (`Trinomial/Base/ShapeTable.lean`) leave the paper's six solutions, each of which is an
  affine trinomial times a unit.
-/

set_option autoImplicit false

namespace Trinomial

open BaseAlgebra

variable {N : ℕ}

/-! ### Unit multiples of `τ_d`, in coordinates -/

theorem finsuppSingle_eq (a : Exponent N) (r : ℚ) :
    Finsupp.single a r = AddMonoidAlgebra.single a r := rfl

/-- `Finsupp.single_neg` in the `AddMonoidAlgebra` spelling, which is the one `rw` and
`abel` cooperate with here. -/
theorem singleNeg_eq (a : Exponent N) (r : ℚ) :
    AddMonoidAlgebra.single a (-r) = -AddMonoidAlgebra.single a r :=
  Finsupp.single_neg a r

theorem mono_mul_single (z x : Exponent N) (c : ℚ) :
    mono z * AddMonoidAlgebra.single x c = AddMonoidAlgebra.single (z + x) c := by
  rw [mono, AddMonoidAlgebra.single_mul_single, one_mul]

/-- A scalar multiple of a monomial multiple of `τ_d`, written out in singles. -/
theorem smul_mono_mul_tau (c : ℚ) (z : Exponent N) (d : Fin N → ℤ) :
    c • (mono z * tau d) = AddMonoidAlgebra.single z c
      - AddMonoidAlgebra.single (z + ⟨1, 0, d⟩) c
      - AddMonoidAlgebra.single (z + ⟨0, 1, -d⟩) c := by
  rw [tau_eq_singles, mul_add, mul_add, mono_mul_single, mono_mul_single, mono_mul_single,
    add_zero, smul_add, smul_add, Finsupp.smul_single', Finsupp.smul_single',
    Finsupp.smul_single', mul_one, mul_neg_one, Finsupp.single_neg,
    Finsupp.single_neg]
  abel

/-- The conclusion of the classification, for a fixed element `g`. -/
def IsUnitMultipleOfFamily (g : Laurent N) : Prop :=
  (∃ (c : ℚ) (z : Exponent N) (d : Fin N → ℤ), c ≠ 0 ∧ g = c • (mono z * tau d)) ∨
  (∃ (c : ℚ) (z : Exponent N) (e : Fin N → ℤ) (p q : ℤ), c ≠ 0 ∧ e ≠ 0 ∧
    p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ g = c • (mono z * theta e p q))

private abbrev IsAffineTableEntry (ρ₁ σ₁ ρ₂ σ₂ : ℤ) : Prop :=
  (ρ₁ = -2 ∧ σ₁ = 0 ∧ ρ₂ = -1 ∧ σ₂ = -1) ∨
  (ρ₁ = -1 ∧ σ₁ = -1 ∧ ρ₂ = -2 ∧ σ₂ = 0) ∨
  (ρ₁ = -1 ∧ σ₁ = 1 ∧ ρ₂ = 1 ∧ σ₂ = 1) ∨
  (ρ₁ = 1 ∧ σ₁ = 1 ∧ ρ₂ = -1 ∧ σ₂ = 1) ∨
  (ρ₁ = 1 ∧ σ₁ = -1 ∧ ρ₂ = 2 ∧ σ₂ = 0) ∨
  (ρ₁ = 2 ∧ σ₁ = 0 ∧ ρ₂ = 1 ∧ σ₂ = -1)

/-- The six rows of the affine solution table differ only by a permutation of the
three support points.  This lemma selects the translated base point and the two
vertices uniformly, then recovers their coefficients and `D`-coordinates from the
linear equations of the normal form. -/
private theorem normalized_affine_of_table {y₁ y₂ : Exponent N} {b₁ b₂ : ℚ}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (G0 : lam b₁ y₁ + lam b₂ y₂ - 1 = 0)
    (G1 : lam b₁ y₁ * ((y₁.s : ℚ) - y₁.t)
      + lam b₂ y₂ * ((y₂.s : ℚ) - y₂.t) = 0)
    (GC : ∀ j, lam b₁ y₁ * (y₁.d j : ℚ) + lam b₂ y₂ * (y₂.d j : ℚ) = 0)
    (table : IsAffineTableEntry (y₁.s - y₁.t) (y₁.s + y₁.t)
      (y₂.s - y₂.t) (y₂.s + y₂.t)) :
    IsUnitMultipleOfFamily
      ((1 : Laurent N) - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂) := by
  rcases table with
    ⟨hρ1, hσ1, hρ2, hσ2⟩ | ⟨hρ1, hσ1, hρ2, hσ2⟩ | ⟨hρ1, hσ1, hρ2, hσ2⟩ |
      ⟨hρ1, hσ1, hρ2, hσ2⟩ | ⟨hρ1, hσ1, hρ2, hσ2⟩ | ⟨hρ1, hσ1, hρ2, hσ2⟩
  all_goals
    let z : Exponent N :=
      if y₁.s + y₁.t = -1 then y₁ else if y₂.s + y₂.t = -1 then y₂ else 0
    let ρz : ℤ :=
      if y₁.s + y₁.t = -1 then y₁.s - y₁.t
      else if y₂.s + y₂.t = -1 then y₂.s - y₂.t else 0
    let xS : Exponent N :=
      if y₁.s - y₁.t = ρz + 1 then y₁
      else if y₂.s - y₂.t = ρz + 1 then y₂ else 0
    let xT : Exponent N :=
      if y₁.s - y₁.t = ρz - 1 then y₁
      else if y₂.s - y₂.t = ρz - 1 then y₂ else 0
    let β₁ : ℚ := if (y₁.s - y₁.t) ^ 2 = 4 then -1 else 1
    let β₂ : ℚ := if (y₂.s - y₂.t) ^ 2 = 4 then -1 else 1
    let c : ℚ :=
      if y₁.s + y₁.t = -1 then -b₁ else if y₂.s + y₂.t = -1 then -b₂ else 1
    have hR1 : ((y₁.s : ℚ) - y₁.t) = ((y₁.s - y₁.t : ℤ) : ℚ) := by
      push_cast
      rfl
    have hR2 : ((y₂.s : ℚ) - y₂.t) = ((y₂.s - y₂.t : ℤ) : ℚ) := by
      push_cast
      rfl
    have hG0 := G0
    have hG1 := G1
    rw [show lam b₁ y₁ = b₁ * (1 / 2 : ℚ) ^ (y₁.s + y₁.t) from rfl,
      show lam b₂ y₂ = b₂ * (1 / 2 : ℚ) ^ (y₂.s + y₂.t) from rfl,
      hσ1, hσ2] at hG0
    rw [show lam b₁ y₁ = b₁ * (1 / 2 : ℚ) ^ (y₁.s + y₁.t) from rfl,
      show lam b₂ y₂ = b₂ * (1 / 2 : ℚ) ^ (y₂.s + y₂.t) from rfl,
      hσ1, hσ2, hR1, hR2, hρ1, hρ2] at hG1
    norm_num at hG0 hG1
    have hb1v : b₁ = β₁ := by
      dsimp [β₁]
      simp only [hρ1]
      norm_num
      linarith
    have hb2v : b₂ = β₂ := by
      dsimp [β₂]
      simp only [hρ2]
      norm_num
      linarith
    have hGC := GC
    rw [show lam b₁ y₁ = b₁ * (1 / 2 : ℚ) ^ (y₁.s + y₁.t) from rfl,
      show lam b₂ y₂ = b₂ * (1 / 2 : ℚ) ^ (y₂.s + y₂.t) from rfl,
      hσ1, hσ2, hb1v, hb2v] at hGC
    dsimp [β₁, β₂] at hGC
    simp only [hρ1, hρ2] at hGC
    norm_num at hGC
    have hc : c ≠ 0 := by
      dsimp [c]
      simp only [hσ1, hσ2]
      norm_num [hb₁, hb₂]
    have hS : z + (⟨1, 0, xS.d - z.d⟩ : Exponent N) = xS := by
      ext
      · simp only [Exponent.add_s]
        dsimp [xS, ρz, z]
        simp only [hρ1, hσ1, hρ2, hσ2]
        norm_num
        omega
      · simp only [Exponent.add_t]
        dsimp [xS, ρz, z]
        simp only [hρ1, hσ1, hρ2, hσ2]
        norm_num
        omega
      · rename_i j
        simp [xS, ρz, z, hρ1, hσ1, hρ2, hσ2]
    have hT : z + (⟨0, 1, -(xS.d - z.d)⟩ : Exponent N) = xT := by
      ext
      · simp only [Exponent.add_s]
        dsimp [xT, ρz, z]
        simp only [hρ1, hσ1, hρ2, hσ2]
        norm_num
        omega
      · simp only [Exponent.add_t]
        dsimp [xT, ρz, z]
        simp only [hρ1, hσ1, hρ2, hσ2]
        norm_num
        omega
      · rename_i j
        have hj := hGC j
        dsimp [xS, xT, ρz, z]
        simp only [hρ1, hσ1, hρ2, hσ2]
        norm_num
        apply Int.cast_injective (α := ℚ)
        push_cast
        linarith
    refine Or.inl ⟨c, z, xS.d - z.d, hc, ?_⟩
    rw [smul_mono_mul_tau, hS, hT]
    dsimp [c, z, xS, xT, ρz, β₁, β₂]
    simp only [hρ1, hσ1, hρ2, hσ2]
    rw [hb1v, hb2v]
    dsimp [β₁, β₂]
    simp only [hρ1, hρ2]
    norm_num [AddMonoidAlgebra.one_def, singleNeg_eq]
    rw [AddMonoidAlgebra.one_def] <;> abel

/-! ### The normalized classification -/

set_option maxHeartbeats 1600000 in
theorem normalized_classification {y₁ y₂ : Exponent N} {b₁ b₂ : ℚ}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hy₁ : y₁ ≠ 0) (hy : y₁ ≠ y₂)
    (hmem : (1 : Laurent N) - AddMonoidAlgebra.single y₁ b₁
      - AddMonoidAlgebra.single y₂ b₂ ∈ baseIdeal N) :
    IsUnitMultipleOfFamily
      ((1 : Laurent N) - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂) := by
  -- read off the coordinate equations of the normal form
  rw [mem_baseIdeal_iff, map_sub, map_sub, map_one, baseEval_single, baseEval_single,
    baseMonoUnit_val, baseMonoUnit_val] at hmem
  have G0 : lam b₁ y₁ + lam b₂ y₂ - 1 = 0 := by
    have h := congrArg BaseAlgebra.b0 hmem
    simp only [sub_eq_add_neg, add_b0, neg_b0, one_b0, smul_b0, zero_b0, mul_one] at h
    linear_combination -h
  have G1 : lam b₁ y₁ * ((y₁.s : ℚ) - y₁.t) + lam b₂ y₂ * ((y₂.s : ℚ) - y₂.t) = 0 := by
    have h := congrArg BaseAlgebra.b1 hmem
    simp only [sub_eq_add_neg, add_b1, neg_b1, one_b1, smul_b1, zero_b1, w1] at h
    linear_combination -h
  have G2 : lam b₁ y₁ * (((y₁.s : ℚ) - y₁.t)^2 - ((y₁.s : ℚ) + y₁.t))
      + lam b₂ y₂ * (((y₂.s : ℚ) - y₂.t)^2 - ((y₂.s : ℚ) + y₂.t)) = 0 := by
    have h := congrArg BaseAlgebra.b2 hmem
    simp only [sub_eq_add_neg, add_b2, neg_b2, one_b2, smul_b2, zero_b2, w2] at h
    linear_combination -2 * h
  have G3 : lam b₁ y₁ * ((y₁.s : ℚ) - y₁.t) * (((y₁.s : ℚ) - y₁.t)^2
        - 3*((y₁.s : ℚ) + y₁.t) + 2)
      + lam b₂ y₂ * ((y₂.s : ℚ) - y₂.t) * (((y₂.s : ℚ) - y₂.t)^2
        - 3*((y₂.s : ℚ) + y₂.t) + 2) = 0 := by
    have h := congrArg BaseAlgebra.b3 hmem
    simp only [sub_eq_add_neg, add_b3, neg_b3, one_b3, smul_b3, zero_b3, w3] at h
    linear_combination -6 * h
  have G4 : lam b₁ y₁ * (((y₁.s : ℚ) - y₁.t)^4
        - 6*((y₁.s : ℚ) - y₁.t)^2*((y₁.s : ℚ) + y₁.t) + 8*((y₁.s : ℚ) - y₁.t)^2
        + 3*((y₁.s : ℚ) + y₁.t)^2 - 6*((y₁.s : ℚ) + y₁.t))
      + lam b₂ y₂ * (((y₂.s : ℚ) - y₂.t)^4
        - 6*((y₂.s : ℚ) - y₂.t)^2*((y₂.s : ℚ) + y₂.t) + 8*((y₂.s : ℚ) - y₂.t)^2
        + 3*((y₂.s : ℚ) + y₂.t)^2 - 6*((y₂.s : ℚ) + y₂.t)) = 0 := by
    have h := congrArg BaseAlgebra.b4 hmem
    simp only [sub_eq_add_neg, add_b4, neg_b4, one_b4, smul_b4, zero_b4, w4] at h
    linear_combination -24 * h
  have GC : ∀ j, lam b₁ y₁ * (y₁.d j : ℚ) + lam b₂ y₂ * (y₂.d j : ℚ) = 0 := by
    intro j
    have h := congrArg (fun v => BaseAlgebra.c v j) hmem
    simp only [sub_eq_add_neg, add_c, neg_c, one_c, smul_c, zero_c] at h
    linear_combination -h
  have hl1 : lam b₁ y₁ ≠ 0 := lam_ne_zero hb₁ y₁
  have hl2 : lam b₂ y₂ ≠ 0 := lam_ne_zero hb₂ y₂
  by_cases hzero : y₁.s = 0 ∧ y₁.t = 0 ∧ y₂.s = 0 ∧ y₂.t = 0
  · -- ===== Case 1: both non-constant terms are pure D-monomials → infinite type =====
    obtain ⟨hs1, ht1, hs2, ht2⟩ := hzero
    have hL1 : lam b₁ y₁ = b₁ := by
      rw [show lam b₁ y₁ = b₁ * (1/2 : ℚ)^(y₁.s + y₁.t) from rfl, hs1, ht1]
      norm_num
    have hL2 : lam b₂ y₂ = b₂ := by
      rw [show lam b₂ y₂ = b₂ * (1/2 : ℚ)^(y₂.s + y₂.t) from rfl, hs2, ht2]
      norm_num
    rw [hL1, hL2] at G0 GC
    -- the coefficient ratio in lowest terms
    set ρ : ℚ := -b₁ / b₂ with hρdef
    have hρ0 : ρ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb₁) hb₂
    have hratio : ∀ j, (y₂.d j : ℚ) = ρ * (y₁.d j : ℚ) := by
      intro j
      have h := GC j
      rw [hρdef]
      field_simp
      linarith
    set p : ℤ := (ρ.den : ℤ) with hpdef
    set q : ℤ := ρ.num with hqdef
    have hp0 : p ≠ 0 := by
      rw [hpdef]
      exact_mod_cast ρ.den_nz
    have hq0 : q ≠ 0 := Rat.num_ne_zero.mpr hρ0
    have hpρ : ρ * (p : ℚ) = (q : ℚ) := by
      rw [hpdef, hqdef]
      push_cast
      nth_rewrite 1 [← Rat.num_div_den ρ]
      rw [div_mul_cancel₀]
      exact_mod_cast ρ.den_nz
    have hkey : ∀ j, q * y₁.d j = p * y₂.d j := by
      intro j
      have : (q : ℚ) * (y₁.d j : ℚ) = (p : ℚ) * (y₂.d j : ℚ) := by
        rw [hratio j, ← hpρ]
        ring
      exact_mod_cast this
    have hcop : IsCoprime (p : ℤ) q := by
      rw [Int.isCoprime_iff_gcd_eq_one, hpdef, hqdef]
      simpa [Int.gcd, Int.natAbs_natCast] using
        (Nat.Coprime.symm ρ.reduced : Nat.Coprime ρ.den ρ.num.natAbs)
    have hdvd : ∀ j, p ∣ y₁.d j := by
      intro j
      exact hcop.dvd_of_dvd_mul_left ⟨y₂.d j, (hkey j).symm ▸ rfl⟩
    set e : Fin N → ℤ := fun j => y₁.d j / p with hedef
    have he1 : ∀ j, y₁.d j = p * e j := by
      intro j
      rw [hedef]
      exact (Int.mul_ediv_cancel' (hdvd j)).symm
    have he2 : ∀ j, y₂.d j = q * e j := by
      intro j
      have h := hkey j
      rw [he1 j] at h
      have : p * y₂.d j = p * (q * e j) := by linarith [h]
      exact mul_left_cancel₀ hp0 this
    have hd₁0 : y₁.d ≠ 0 := by
      intro h
      exact hy₁ (by ext <;> simp [hs1, ht1, h])
    have he0 : e ≠ 0 := by
      intro h
      apply hd₁0
      funext j
      rw [he1 j, congrFun h j]
      simp
    have hpq : p ≠ q := by
      intro h
      apply hy
      ext
      · rw [hs1, hs2]
      · rw [ht1, ht2]
      · rw [he1 _, he2 _, h]
    -- the coefficients are the paper's −q/(p−q) and p/(p−q)
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp he0
    have hej₀ : (e j₀ : ℚ) ≠ 0 := by exact_mod_cast hj₀
    have hbpq : b₁ * (p : ℚ) + b₂ * (q : ℚ) = 0 := by
      have h := GC j₀
      rw [he1 j₀, he2 j₀] at h
      push_cast at h
      have : (b₁ * (p : ℚ) + b₂ * (q : ℚ)) * (e j₀ : ℚ) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hej₀
    have hΔ : ((p : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
    have hb1v : b₁ * ((p : ℚ) - q) = -q := by linear_combination hbpq - (q : ℚ) * G0
    have hb2v : b₂ * ((p : ℚ) - q) = (p : ℚ) := by linear_combination (p : ℚ) * G0 - hbpq
    refine Or.inr ⟨((p : ℚ) - q)⁻¹, 0, e, p, q, inv_ne_zero hΔ, he0, hp0, hq0, hpq, ?_⟩
    have hy₁eq : y₁ = (⟨0, 0, p • e⟩ : Exponent N) := by
      ext
      · exact hs1
      · exact ht1
      · rename_i j
        rw [he1 j]
        simp
    have hy₂eq : y₂ = (⟨0, 0, q • e⟩ : Exponent N) := by
      ext
      · exact hs2
      · exact ht2
      · rename_i j
        rw [he2 j]
        simp
    rw [hy₁eq, hy₂eq, mono_zero, one_mul, theta_eq_singles, smul_add, smul_add,
      Finsupp.smul_single', Finsupp.smul_single', Finsupp.smul_single',
      AddMonoidAlgebra.one_def]
    have hb1v' : b₁ = -(q : ℚ) / ((p : ℚ) - q) := by
      rw [eq_div_iff hΔ]
      exact hb1v
    have hb2v' : b₂ = (p : ℚ) / ((p : ℚ) - q) := by
      rw [eq_div_iff hΔ]
      exact hb2v
    rw [show ((p : ℚ) - q)⁻¹ * ((p : ℚ) - (q : ℚ)) = 1 from inv_mul_cancel₀ hΔ,
      show ((p : ℚ) - q)⁻¹ * (q : ℚ) = -b₁ by
        rw [hb1v', neg_div, neg_neg, inv_mul_eq_div],
      show ((p : ℚ) - q)⁻¹ * (-(p : ℚ)) = -b₂ by
        rw [hb2v', mul_neg, inv_mul_eq_div]]
    simp only [finsuppSingle_eq, singleNeg_eq]
    abel
  · -- ===== Case 2: the certificates force the six-solution table → affine type =====
    have hne : ¬(((y₁.s : ℚ) - y₁.t) = 0 ∧ ((y₁.s : ℚ) + y₁.t) = 0
        ∧ ((y₂.s : ℚ) - y₂.t) = 0 ∧ ((y₂.s : ℚ) + y₂.t) = 0) := by
      rintro ⟨h1, h2, h3, h4⟩
      refine hzero ⟨?_, ?_, ?_, ?_⟩
      · have : (y₁.s : ℚ) = 0 := by linarith
        exact_mod_cast this
      · have : (y₁.t : ℚ) = 0 := by linarith
        exact_mod_cast this
      · have : (y₂.s : ℚ) = 0 := by linarith
        exact_mod_cast this
      · have : (y₂.t : ℚ) = 0 := by linarith
        exact_mod_cast this
    obtain ⟨v1, v2, v3, v4, v5, v6⟩ :=
      ShapeCert.elimination_of_ne_zero _ _ _ _ _ _ hl1 hl2 hne ⟨G0, G1, G2, G3, G4⟩
    -- integer forms of the elimination equations
    have E1 : (y₂.s - y₂.t)*(y₂.s - y₂.t) + 2*(y₁.s + y₁.t) - (y₂.s + y₂.t) - 2 = 0 := by
      have h : (((y₂.s - y₂.t)*(y₂.s - y₂.t) + 2*(y₁.s + y₁.t) - (y₂.s + y₂.t) - 2 : ℤ)
          : ℚ) = 0 := by
        push_cast
        linear_combination v1
      exact_mod_cast h
    have E2 : (y₁.s + y₁.t)*(y₂.s - y₂.t) + (y₁.s - y₁.t)*(y₂.s + y₂.t)
        - (y₂.s - y₂.t)*(y₂.s + y₂.t) + (y₂.s - y₂.t) = 0 := by
      have h : (((y₁.s + y₁.t)*(y₂.s - y₂.t) + (y₁.s - y₁.t)*(y₂.s + y₂.t)
          - (y₂.s - y₂.t)*(y₂.s + y₂.t) + (y₂.s - y₂.t) : ℤ) : ℚ) = 0 := by
        push_cast
        linear_combination v2
      exact_mod_cast h
    have E3 : (y₁.s - y₁.t)*(y₂.s - y₂.t) + (y₁.s + y₁.t) + (y₂.s + y₂.t) - 1 = 0 := by
      have h : (((y₁.s - y₁.t)*(y₂.s - y₂.t) + (y₁.s + y₁.t) + (y₂.s + y₂.t) - 1 : ℤ)
          : ℚ) = 0 := by
        push_cast
        linear_combination v3
      exact_mod_cast h
    have E4 : (y₁.s + y₁.t)*(y₁.s + y₁.t) - (y₁.s + y₁.t)*(y₂.s + y₂.t)
        + (y₂.s + y₂.t)*(y₂.s + y₂.t) - 1 = 0 := by
      have h : (((y₁.s + y₁.t)*(y₁.s + y₁.t) - (y₁.s + y₁.t)*(y₂.s + y₂.t)
          + (y₂.s + y₂.t)*(y₂.s + y₂.t) - 1 : ℤ) : ℚ) = 0 := by
        push_cast
        linear_combination v4
      exact_mod_cast h
    have E5 : (y₁.s - y₁.t)*(y₁.s + y₁.t) - (y₂.s - y₂.t)*(y₂.s + y₂.t)
        - (y₁.s - y₁.t) + (y₂.s - y₂.t) = 0 := by
      have h : (((y₁.s - y₁.t)*(y₁.s + y₁.t) - (y₂.s - y₂.t)*(y₂.s + y₂.t)
          - (y₁.s - y₁.t) + (y₂.s - y₂.t) : ℤ) : ℚ) = 0 := by
        push_cast
        linear_combination v5
      exact_mod_cast h
    have E6 : (y₁.s - y₁.t)*(y₁.s - y₁.t) - (y₁.s + y₁.t) + 2*(y₂.s + y₂.t) - 2 = 0 := by
      have h : (((y₁.s - y₁.t)*(y₁.s - y₁.t) - (y₁.s + y₁.t) + 2*(y₂.s + y₂.t) - 2 : ℤ)
          : ℚ) = 0 := by
        push_cast
        linear_combination v6
      exact_mod_cast h
    have table := ShapeCert.solution_table _ _ _ _ E1 E2 E3 E4 E5 E6
    exact normalized_affine_of_table hb₁ hb₂ G0 G1 GC table

/-! ### The classification for arbitrary trinomials -/

/-- **Proposition 2.4 (ii)**: up to a nonzero scalar and a Laurent monomial, every
three-term element of `J₀` is an affine trinomial `τ_d` or an infinite trinomial
`θ_e^{p,q}` with `e ≠ 0` and `p, q` distinct nonzero integers.

(The paper normalizes `e` to be primitive; see `trinomial_in_baseIdeal_primitive` in
`Trinomial/Base/PrimitiveNormalization.lean`.) -/
theorem trinomial_in_baseIdeal {f : Laurent N} (hf : f ∈ baseIdeal N)
    (h3 : f.support.card = 3) : IsUnitMultipleOfFamily f := by
  obtain ⟨x₀, x₁, x₂, h01, h02, h12, hsupp⟩ := Finset.card_eq_three.mp h3
  have hc₀ : f x₀ ≠ 0 := by
    rw [← Finsupp.mem_support_iff, hsupp]
    exact Finset.mem_insert_self _ _
  have hc₁ : f x₁ ≠ 0 := by
    rw [← Finsupp.mem_support_iff, hsupp]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hc₂ : f x₂ ≠ 0 := by
    rw [← Finsupp.mem_support_iff, hsupp]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hf_eq : f = AddMonoidAlgebra.single x₀ (f x₀)
      + (AddMonoidAlgebra.single x₁ (f x₁) + AddMonoidAlgebra.single x₂ (f x₂)) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [Finsupp.sum, hsupp, Finset.sum_insert (by simp [h01, h02]),
      Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
  set y₁ : Exponent N := -x₀ + x₁ with hy₁def
  set y₂ : Exponent N := -x₀ + x₂ with hy₂def
  set b₁ : ℚ := -((f x₀)⁻¹ * f x₁) with hb₁def
  set b₂ : ℚ := -((f x₀)⁻¹ * f x₂) with hb₂def
  have hprod : mono (-x₀) * f = AddMonoidAlgebra.single 0 (f x₀)
      + (AddMonoidAlgebra.single y₁ (f x₁) + AddMonoidAlgebra.single y₂ (f x₂)) := by
    conv_lhs => rw [hf_eq]
    rw [mul_add, mul_add, mono_mul_single, mono_mul_single, mono_mul_single,
      neg_add_cancel]
  have hf' : (f x₀)⁻¹ • (mono (-x₀) * f)
      = 1 - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂ := by
    rw [hprod, smul_add, smul_add, Finsupp.smul_single', Finsupp.smul_single',
      Finsupp.smul_single', inv_mul_cancel₀ hc₀, AddMonoidAlgebra.one_def, hb₁def, hb₂def]
    simp only [finsuppSingle_eq, singleNeg_eq]
    abel
  have hmem' : (1 : Laurent N) - AddMonoidAlgebra.single y₁ b₁
      - AddMonoidAlgebra.single y₂ b₂ ∈ baseIdeal N := by
    rw [← hf', Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hf)
  have hb₁ : b₁ ≠ 0 := by
    rw [hb₁def]
    exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hc₀) hc₁)
  have hb₂ : b₂ ≠ 0 := by
    rw [hb₂def]
    exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hc₀) hc₂)
  have hy₁ : y₁ ≠ 0 := by
    rw [hy₁def]
    intro h
    exact h01 (neg_add_eq_zero.mp h)
  have hyy : y₁ ≠ y₂ := by
    rw [hy₁def, hy₂def]
    intro h
    exact h12 (add_left_cancel h)
  have hback : f = (f x₀) • (mono x₀ * ((1 : Laurent N)
      - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂)) := by
    rw [← hf', mul_smul_comm, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← mul_assoc,
      mono_mul, add_neg_cancel, mono_zero, one_mul]
  rcases normalized_classification hb₁ hb₂ hy₁ hyy hmem' with
    ⟨c, z, d, hc, heq⟩ | ⟨c, z, e, p, q, hc, he, hp, hq, hpq, heq⟩
  · refine Or.inl ⟨f x₀ * c, x₀ + z, d, mul_ne_zero hc₀ hc, ?_⟩
    calc f = (f x₀) • (mono x₀ * ((1 : Laurent N)
          - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂)) := hback
    _ = (f x₀) • (mono x₀ * (c • (mono z * tau d))) := by rw [heq]
    _ = (f x₀ * c) • (mono (x₀ + z) * tau d) := by
        rw [mul_smul_comm, smul_smul, ← mul_assoc, mono_mul]
  · refine Or.inr ⟨f x₀ * c, x₀ + z, e, p, q, mul_ne_zero hc₀ hc, he, hp, hq, hpq, ?_⟩
    calc f = (f x₀) • (mono x₀ * ((1 : Laurent N)
          - AddMonoidAlgebra.single y₁ b₁ - AddMonoidAlgebra.single y₂ b₂)) := hback
    _ = (f x₀) • (mono x₀ * (c • (mono z * theta e p q))) := by rw [heq]
    _ = (f x₀ * c) • (mono (x₀ + z) * theta e p q) := by
        rw [mul_smul_comm, smul_smul, ← mul_assoc, mono_mul]

end Trinomial
