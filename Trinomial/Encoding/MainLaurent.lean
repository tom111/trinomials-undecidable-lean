import Trinomial.Base.ShapeClassification
import Trinomial.Quadrics.KernelEvaluation

/-!
# Theorem 4.5, Laurent side: the ideal `J_P` and its short polynomials

[proof of Theorem 4.5].  Given a finite family `Q₁, …, Q_M` of quadratic forms
on `V = ℚ^N × ℚv₀` (as symmetric matrices `(b_ij)` of the bilinear forms), the reduction ideal is

  `J_P = J₀ ∩ ⋂ᵢ ker φ_{Qᵢ}`.

By Proposition 2.4 and Proposition 3.5, the trinomials of `J_P` are precisely the affine
`τ_d` with `Qᵢ(d,1) = 0` for all `i` and the infinite `θ_e^{p,q}` with `Qᵢ(e,0) = 0`
for all `i`.  If the system has no nonzero integral solution at infinity (the *guard*
condition, arranged by Lemma 4.2), only the affine family survives:

* `not_hasShort_two` — `J_P` contains no monomial and no binomial;
* `hasShort_three_iff` — `J_P` contains a trinomial iff the affine quadratic system
  `Qᵢ(d, 1) = 0` has an integral solution;
* `hasShort_four` — `J_P` always contains the quadrinomial `Ω`.

These three statements are the exact `3/4`-gap of the paper.
-/

set_option autoImplicit false

namespace Trinomial

variable {N M : ℕ}

/-- The reduction ideal `J_P = J₀ ∩ ⋂ᵢ ker φ_{Qᵢ}`  [proof of Theorem 4.5]. -/
noncomputable def reductionIdeal (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Ideal (Laurent N) :=
  baseIdeal N ⊓ ⨅ i, RingHom.ker (phi (Q i))

theorem mem_reductionIdeal_iff {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    {f : Laurent N} :
    f ∈ reductionIdeal Q ↔ f ∈ baseIdeal N ∧ ∀ i, f ∈ RingHom.ker (phi (Q i)) := by
  rw [reductionIdeal, Ideal.mem_inf, Submodule.mem_iInf]

/-- The system has no nonzero integral solution on the hyperplane at infinity `t = 0` (the paper states the rational version, equivalent by clearing denominators).  This is the
property that Lemma 4.2 arranges for the guarded system. -/
def NoIntegralSolutionAtInfinity (Q : Fin M → BilinearFormMatrix (Option (Fin N))) : Prop :=
  ∀ e : Fin N → ℤ, e ≠ 0 → ∃ i, quadAt (Q i) (ratCast e) 0 ≠ 0

/-- `τ_d ∈ J_P ⟺ d` solves the affine system  [proof of Theorem 4.5]. -/
theorem tau_mem_reductionIdeal_iff (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (d : Fin N → ℤ) :
    tau d ∈ reductionIdeal Q ↔ ∀ i, quadAt (Q i) (ratCast d) 1 = 0 := by
  rw [mem_reductionIdeal_iff]
  constructor
  · rintro ⟨-, h⟩ i
    exact (tau_mem_ker_phi_iff (Q i) d).mp (h i)
  · intro h
    exact ⟨tau_mem_baseIdeal d, fun i => (tau_mem_ker_phi_iff (Q i) d).mpr (h i)⟩

/-- `Ω ∈ J_P` always  [proof of Theorem 4.5]. -/
theorem Omega_mem_reductionIdeal (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Omega N ∈ reductionIdeal Q :=
  mem_reductionIdeal_iff.mpr ⟨Omega_mem_baseIdeal, fun i => Omega_mem_ker_phi (Q i)⟩

theorem phi_mono_val (G : BilinearFormMatrix (Option (Fin N))) (z : Exponent N) :
    phi G (mono z) = (phiMonoUnit G z : CubeAlgebra G) := by
  rw [mono, phi_single, one_smul]

/-- Membership in `ker φ_Q` is invariant under multiplication by units of `L_N`. -/
theorem smul_mono_mul_mem_ker_phi_iff (G : BilinearFormMatrix (Option (Fin N))) {c : ℚ}
    (hc : c ≠ 0) (z : Exponent N) (g : Laurent N) :
    c • (mono z * g) ∈ RingHom.ker (phi G) ↔ g ∈ RingHom.ker (phi G) := by
  rw [RingHom.mem_ker, RingHom.mem_ker, map_smul, map_mul, phi_mono_val, smul_eq_zero,
    Units.mul_right_eq_zero]
  exact or_iff_right hc

/-- The trinomials of a guarded reduction ideal are affine, with exponents solving the
full quadratic system  [proof of Theorem 4.5]. -/
theorem trinomial_in_reductionIdeal {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    (guard : NoIntegralSolutionAtInfinity Q) {f : Laurent N} (hf : f ∈ reductionIdeal Q)
    (h3 : f.support.card = 3) :
    ∃ (c : ℚ) (z : Exponent N) (d : Fin N → ℤ), c ≠ 0 ∧ f = c • (mono z * tau d) ∧
      ∀ i, quadAt (Q i) (ratCast d) 1 = 0 := by
  obtain ⟨hf0, hfker⟩ := mem_reductionIdeal_iff.mp hf
  rcases trinomial_in_baseIdeal hf0 h3 with
    ⟨c, z, d, hc, heq⟩ | ⟨c, z, e, p, q, hc, he, hp, hq, hpq, heq⟩
  · refine ⟨c, z, d, hc, heq, fun i => ?_⟩
    have hk := hfker i
    rw [heq, smul_mono_mul_mem_ker_phi_iff (Q i) hc] at hk
    exact (tau_mem_ker_phi_iff (Q i) d).mp hk
  · exfalso
    obtain ⟨i, hi⟩ := guard e he
    have hk := hfker i
    rw [heq, smul_mono_mul_mem_ker_phi_iff (Q i) hc] at hk
    exact hi ((theta_mem_ker_phi_iff (Q i) e hp hq hpq).mp hk)

/-- `J_P` contains no monomial and no binomial  [Theorem 4.5, first bullet]. -/
theorem not_hasShort_two (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    ¬ HasShort 2 (reductionIdeal Q) := by
  rintro ⟨f, hf, hf0, hcard⟩
  have hfJ0 : f ∈ baseIdeal N := (mem_reductionIdeal_iff.mp hf).1
  have h2 := one_lt_supportCard_of_mem_baseIdeal hfJ0 hf0
  exact no_binomial_in_baseIdeal hfJ0 (le_antisymm hcard h2)

/-- **Theorem 4.5, second bullet**: `J_P` contains a trinomial exactly when the affine
quadratic system has an integral solution. -/
theorem hasShort_three_iff {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    (guard : NoIntegralSolutionAtInfinity Q) :
    HasShort 3 (reductionIdeal Q) ↔
      ∃ d : Fin N → ℤ, ∀ i, quadAt (Q i) (ratCast d) 1 = 0 := by
  constructor
  · rintro ⟨f, hf, hf0, hcard⟩
    have hfJ0 : f ∈ baseIdeal N := (mem_reductionIdeal_iff.mp hf).1
    have h2 := one_lt_supportCard_of_mem_baseIdeal hfJ0 hf0
    rcases (by omega : f.support.card = 2 ∨ f.support.card = 3) with h | h
    · exact (no_binomial_in_baseIdeal hfJ0 h).elim
    · obtain ⟨c, z, d, hc, heq, hquad⟩ := trinomial_in_reductionIdeal guard hf h
      exact ⟨d, hquad⟩
  · rintro ⟨d, hd⟩
    exact ⟨tau d, (tau_mem_reductionIdeal_iff Q d).mpr hd, tau_ne_zero d,
      le_of_eq (supportCard_tau d)⟩

/-- `J_P` always contains the quadrinomial `Ω`  [Theorem 4.5, last sentence]. -/
theorem hasShort_four (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    HasShort 4 (reductionIdeal Q) :=
  ⟨Omega N, Omega_mem_reductionIdeal Q, Omega_ne_zero, le_of_eq supportCard_Omega⟩

/-- **Theorem 4.5, Laurent form** [Theorem 4.5]: for a family of quadratic
forms with no nonzero integral zero at infinity, the shortest polynomial in `J_P` has three
terms if the affine system `Qᵢ(d, 1) = 0` is integrally solvable, and four terms
otherwise. -/
theorem main_laurent {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    (guard : NoIntegralSolutionAtInfinity Q) :
    ¬ HasShort 2 (reductionIdeal Q)
    ∧ (HasShort 3 (reductionIdeal Q) ↔
        ∃ d : Fin N → ℤ, ∀ i, quadAt (Q i) (ratCast d) 1 = 0)
    ∧ HasShort 4 (reductionIdeal Q) :=
  ⟨not_hasShort_two Q, hasShort_three_iff guard, hasShort_four Q⟩

end Trinomial
