import Trinomial.Encoding.GuardedSystem

/-!
# Lemma 4.2, first bullet: only the origin at infinity, rationally

[Lemma 4.2 and Remark 4.3].  The paper states the guard property
over `ℚ`: "the origin is the only rational solution of `g₁, …, g_{m+2}` with `t = 0`".
The Laurent side (`MainLaurent.lean`) uses the integral form `NoIntegralSolutionAtInfinity`,
because the exponent vector `e` of an infinite trinomial `θ_e^{p,q}` is integral.  The two
forms are equivalent because the `Qᵢ(·, 0)` are homogeneous of degree two: a rational
solution becomes an integral one after clearing denominators, and the integral solutions are
rational ones.

* `NoRationalSolutionAtInfinity` — the paper's statement;
* `noRationalSolutionAtInfinity_iff` — equivalence with the integral form;
* `noRationalSolutionAtInfinity_homogenizedSystem` — the first bullet of Lemma 4.2
  for the homogenized guarded system, verbatim.
-/

set_option autoImplicit false

namespace Trinomial

variable {N M : ℕ}

/-- The origin is the only rational solution of the system `Qᵢ(e, t) = 0` with `t = 0`
[Lemma 4.2, first bullet]. -/
def NoRationalSolutionAtInfinity (Q : Fin M → BilinearFormMatrix (Option (Fin N))) : Prop :=
  ∀ e : Fin N → ℚ, e ≠ 0 → ∃ i, quadAt (Q i) e 0 ≠ 0

/-- The rational cast of an integer vector is injective at zero. -/
theorem ratCast_eq_zero_iff (e : Fin N → ℤ) : ratCast e = 0 ↔ e = 0 := by
  constructor
  · intro h
    funext i
    exact Int.cast_eq_zero.mp (congrFun h i)
  · rintro rfl
    exact ratCast_zero

/-- `Q(·, 0)` is homogeneous of degree two: `Q(c e, 0) = c² Q(e, 0)`. -/
theorem quadAt_smul_zero (G : BilinearFormMatrix (Option (Fin N))) (c : ℚ) (e : Fin N → ℚ) :
    quadAt G (c • e) 0 = c ^ 2 * quadAt G e 0 := by
  have h : homVec (c • e) 0 = c • homVec e 0 := by rw [homVec_smul, mul_zero]
  rw [quadAt, h, G.quad_smul]
  rfl

/-- Clearing denominators: a rational vector times the product of its denominators is the
cast of an integer vector. -/
theorem exists_natCast_smul_eq_ratCast (e : Fin N → ℚ) :
    ∃ (c : ℕ) (e' : Fin N → ℤ), c ≠ 0 ∧ (c : ℚ) • e = ratCast e' := by
  refine ⟨∏ j, (e j).den, fun i => (e i).num * ((∏ j, (e j).den) / (e i).den : ℕ), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => (e j).den_ne_zero
  · funext i
    have hdvd : (e i).den ∣ ∏ j, (e j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hc : ((∏ j, (e j).den : ℕ) : ℚ)
        = ((e i).den : ℚ) * (((∏ j, (e j).den) / (e i).den : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    rw [Pi.smul_apply, smul_eq_mul, ratCast_apply, Int.cast_mul, Int.cast_natCast, hc,
      mul_right_comm, Rat.den_mul_eq_num]

/-- The rational and the integral form of "only the origin at infinity" are equivalent,
by clearing denominators  [Lemma 4.2, first bullet, and Remark 4.3]. -/
theorem noRationalSolutionAtInfinity_iff (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    NoRationalSolutionAtInfinity Q ↔ NoIntegralSolutionAtInfinity Q := by
  constructor
  · intro h e he
    exact h (ratCast e) (fun h0 => he ((ratCast_eq_zero_iff e).mp h0))
  · intro h e he
    obtain ⟨c, e', hc, hce⟩ := exists_natCast_smul_eq_ratCast e
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    have he' : e' ≠ 0 := by
      intro h0
      rw [h0, ratCast_zero, smul_eq_zero] at hce
      exact hce.elim hcq he
    obtain ⟨i, hi⟩ := h e' he'
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hce, quadAt_smul_zero, h0, mul_zero]

/-- **Lemma 4.2, first bullet:** the origin is the only rational solution
of the homogenized guarded system `g₁, …, g_{m+2}` with `t = 0`. -/
theorem noRationalSolutionAtInfinity_homogenizedSystem {r : ℕ}
    (L : List (DegreeTwoEquation r)) :
    NoRationalSolutionAtInfinity (homogenizedSystem (guarded L)) :=
  (noRationalSolutionAtInfinity_iff _).mpr (noIntegralSolutionAtInfinity_homogenizedSystem L)

end Trinomial
