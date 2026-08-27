import Trinomial.Base.ShapeClassification

/-!
# Primitive exponent vectors, and Proposition 2.4 (ii) as stated

[Definition 2.3; Proposition 2.4 (ii)].  The infinite trinomials
`θ_e^{p,q} = (p−q) + q·D^{pe} − p·D^{qe}` are indexed by a *primitive* vector `e ∈ ℤ^N`
(the gcd of its coordinates is `1`) and distinct nonzero integers `p, q`.  The
classification `trinomial_in_baseIdeal` (`Trinomial/Base/ShapeClassification.lean`) delivers
the infinite family only with `e ≠ 0`.  This module adds the paper's normalization
("every nonzero integer vector is an integer multiple of a primitive one", proof of
Proposition 2.4):

* `IsPrimitive e` — the coordinates of `e` have gcd `1`;
* `exists_primitive_smul` — a nonzero `e` is `g • e'` with `g ≥ 1` and `e'` primitive;
* `theta_smul` — `θ_{ge}^{p,q} = g⁻¹ · θ_e^{gp,gq}`, the rescaling that also appears in
  Remark 4.4 (`2 − D^e − D^{−e} = g⁻¹ θ_{e'}^{g,−g}` for `e = g e'`);
* `trinomial_in_baseIdeal_primitive` — **Proposition 2.4 (ii)** with `e` primitive.
-/

set_option autoImplicit false

namespace Trinomial

variable {N : ℕ}

/-! ### Primitive vectors -/

/-- A vector `e ∈ ℤ^N` is *primitive* when the gcd of its coordinates is `1`
[Definition 2.3].  (`Finset.gcd` over `ℤ` is the nonnegative
gcd, so this is the usual notion; for `N = 0` no vector is primitive.) -/
def IsPrimitive (e : Fin N → ℤ) : Prop :=
  Finset.univ.gcd e = 1

instance (e : Fin N → ℤ) : Decidable (IsPrimitive e) :=
  inferInstanceAs (Decidable (Finset.univ.gcd e = 1))

/-- A primitive vector is nonzero. -/
theorem IsPrimitive.ne_zero {e : Fin N → ℤ} (he : IsPrimitive e) : e ≠ 0 := by
  rintro rfl
  have h : Finset.univ.gcd (0 : Fin N → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr fun _ _ => rfl
  rw [IsPrimitive, h] at he
  exact zero_ne_one he

/-- "Every nonzero integer vector is an integer multiple of a primitive one"
[proof of Proposition 2.4]: `e = g • e'` with `g ≥ 1` the gcd of the coordinates
of `e` and `e' = e / g` primitive. -/
theorem exists_primitive_smul {e : Fin N → ℤ} (he : e ≠ 0) :
    ∃ (g : ℕ) (e' : Fin N → ℤ), 0 < g ∧ IsPrimitive e' ∧ e = (g : ℤ) • e' := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp he
  have hd0 : Finset.univ.gcd e ≠ 0 := fun h =>
    hj ((Finset.gcd_eq_zero_iff.mp h) j (Finset.mem_univ j))
  have hdnn : 0 ≤ Finset.univ.gcd e :=
    Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  refine ⟨(Finset.univ.gcd e).natAbs, fun i => e i / Finset.univ.gcd e,
    Int.natAbs_pos.mpr hd0, Finset.gcd_div_eq_one (Finset.mem_univ j) hj, ?_⟩
  funext i
  rw [Pi.smul_apply, smul_eq_mul, Int.natCast_natAbs, abs_of_nonneg hdnn]
  exact (Int.mul_ediv_cancel' (Finset.gcd_dvd (Finset.mem_univ i))).symm

/-! ### Rescaling the exponent vector of `θ_e^{p,q}` -/

/-- `θ_{ge}^{p,q} = g⁻¹ · θ_e^{gp,gq}` for `g ≥ 1`  [Remark 4.4,
where `2 − D^e − D^{−e} = g⁻¹ θ_{e'}^{g,−g}` for `e = g e'`].  Indeed both sides equal
`(p−q) + q·D^{gpe} − p·D^{gqe}`. -/
theorem theta_smul (e : Fin N → ℤ) {g : ℕ} (hg : 0 < g) (p q : ℤ) :
    theta ((g : ℤ) • e) p q = ((g : ℚ)⁻¹) • theta e (g * p) (g * q) := by
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hexp : ∀ r : ℤ, r • ((g : ℤ) • e) = ((g : ℤ) * r) • e := fun r => by
    rw [smul_smul, mul_comm]
  have h1 : (g : ℚ)⁻¹ * ((((g : ℤ) * p : ℤ) : ℚ) - (((g : ℤ) * q : ℤ) : ℚ))
      = (p : ℚ) - (q : ℚ) := by
    push_cast
    rw [mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hg', one_mul, one_mul]
  have h2 : (g : ℚ)⁻¹ * (((g : ℤ) * q : ℤ) : ℚ) = (q : ℚ) := by
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hg', one_mul]
  have h3 : (g : ℚ)⁻¹ * (((g : ℤ) * p : ℤ) : ℚ) = (p : ℚ) := by
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hg', one_mul]
  unfold theta
  rw [hexp, hexp, smul_sub, smul_add, smul_smul, smul_smul, smul_smul, h1, h2, h3]

/-! ### Proposition 2.4 (ii) with a primitive exponent vector -/

/-- The conclusion of Proposition 2.4 (ii) as stated in the paper: up to a nonzero scalar
and a Laurent monomial, an affine trinomial `τ_d`, or an infinite trinomial `θ_e^{p,q}`
with `e` primitive and `p ≠ q` both nonzero.  Compare `IsUnitMultipleOfFamily`, which
only records `e ≠ 0`. -/
def IsUnitMultipleOfFamilyPrimitive (g : Laurent N) : Prop :=
  (∃ (c : ℚ) (z : Exponent N) (d : Fin N → ℤ), c ≠ 0 ∧ g = c • (mono z * tau d)) ∨
  (∃ (c : ℚ) (z : Exponent N) (e : Fin N → ℤ) (p q : ℤ), c ≠ 0 ∧ IsPrimitive e ∧
    p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ g = c • (mono z * theta e p q))

/-- The primitive form of the classification implies the weaker one. -/
theorem IsUnitMultipleOfFamilyPrimitive.isUnitMultipleOfFamily {g : Laurent N}
    (h : IsUnitMultipleOfFamilyPrimitive g) : IsUnitMultipleOfFamily g := by
  rcases h with ⟨c, z, d, hc, hg⟩ | ⟨c, z, e, p, q, hc, he, hp, hq, hpq, hg⟩
  · exact Or.inl ⟨c, z, d, hc, hg⟩
  · exact Or.inr ⟨c, z, e, p, q, hc, he.ne_zero, hp, hq, hpq, hg⟩

/-- **Proposition 2.4 (ii)**, as stated in the paper: up to a nonzero scalar and a Laurent
monomial, every three-term element of `J₀` is an affine trinomial `τ_d` or an infinite
trinomial `θ_e^{p,q}` with `e ∈ ℤ^N` primitive and `p, q` distinct nonzero integers.

From `trinomial_in_baseIdeal`, writing `e = g • e'` with `e'` primitive
(`exists_primitive_smul`) and rescaling `θ_{ge'}^{p,q} = g⁻¹ θ_{e'}^{gp,gq}`
(`theta_smul`). -/
theorem trinomial_in_baseIdeal_primitive {f : Laurent N} (hf : f ∈ baseIdeal N)
    (h3 : f.support.card = 3) : IsUnitMultipleOfFamilyPrimitive f := by
  rcases trinomial_in_baseIdeal hf h3 with
    ⟨c, z, d, hc, heq⟩ | ⟨c, z, e, p, q, hc, he, hp, hq, hpq, heq⟩
  · exact Or.inl ⟨c, z, d, hc, heq⟩
  · obtain ⟨g, e', hg, he', rfl⟩ := exists_primitive_smul he
    have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    refine Or.inr ⟨c * (g : ℚ)⁻¹, z, e', g * p, g * q, mul_ne_zero hc (inv_ne_zero hg'), he',
      mul_ne_zero hgz hp, mul_ne_zero hgz hq, fun h => hpq (mul_left_cancel₀ hgz h), ?_⟩
    rw [heq, theta_smul e' hg, mul_smul_comm, smul_smul]

/-! ### Why affine trinomials force infinite trinomials -/

/-- The identity from Remark 4.4:
`τ_(d−e) + τ_(d+e) − (D^e + D^(−e)) τ_d = 2 − D^e − D^(−e)`. -/
theorem tau_three_term_identity (d e : Fin N → ℤ) :
    tau (d - e) + tau (d + e)
        - (mono (⟨0, 0, e⟩ : Exponent N) + mono ⟨0, 0, -e⟩) * tau d =
      2 - mono ⟨0, 0, e⟩ - mono ⟨0, 0, -e⟩ := by
  have hSe : (⟨0, 0, e⟩ : Exponent N) + ⟨1, 0, d⟩ = ⟨1, 0, d + e⟩ := by
    ext <;> simp [add_comm]
  have hSne : (⟨0, 0, -e⟩ : Exponent N) + ⟨1, 0, d⟩ = ⟨1, 0, d - e⟩ := by
    ext <;> simp [sub_eq_add_neg, add_comm]
  have hTe : (⟨0, 0, e⟩ : Exponent N) + ⟨0, 1, -d⟩ = ⟨0, 1, -(d - e)⟩ := by
    ext <;> simp [sub_eq_add_neg]
  have hTne : (⟨0, 0, -e⟩ : Exponent N) + ⟨0, 1, -d⟩ = ⟨0, 1, -(d + e)⟩ := by
    ext <;> simp
  rw [tau, tau, tau]
  simp only [mul_sub, add_mul, mono_mul, hSe, hSne, hTe, hTne]
  ring_nf

/-- If an ideal contains `τ_(d−e)`, `τ_d`, and `τ_(d+e)` for nonzero `e`, then it
contains the infinite trinomial `θ_(e')^(g,−g)`, where `e = g e'`, `e'` is primitive,
and `g` is positive. -/
theorem infinite_trinomial_mem_of_tau_arithmetic_progression
    (I : Ideal (Laurent N)) {d e : Fin N → ℤ} (he : e ≠ 0)
    (hminus : tau (d - e) ∈ I) (hzero : tau d ∈ I) (hplus : tau (d + e) ∈ I) :
    ∃ (g : ℕ) (e' : Fin N → ℤ), 0 < g ∧ IsPrimitive e' ∧ e = (g : ℤ) • e' ∧
      theta e' (g : ℤ) (-(g : ℤ)) ∈ I := by
  have hcomb : tau (d - e) + tau (d + e)
      - (mono (⟨0, 0, e⟩ : Exponent N) + mono ⟨0, 0, -e⟩) * tau d ∈ I :=
    I.sub_mem (I.add_mem hminus hplus) (I.mul_mem_left _ hzero)
  rw [tau_three_term_identity] at hcomb
  obtain ⟨g, e', hg, he', heq⟩ := exists_primitive_smul he
  refine ⟨g, e', hg, he', heq, ?_⟩
  have hscaled : (g : ℚ) •
      (2 - mono (⟨0, 0, e⟩ : Exponent N) - mono ⟨0, 0, -e⟩) ∈ I := by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hcomb
  rw [heq] at hscaled
  convert hscaled using 1
  unfold theta
  simp only [Int.cast_neg, Int.cast_natCast, Algebra.smul_def]
  push_cast
  ring_nf

end Trinomial
