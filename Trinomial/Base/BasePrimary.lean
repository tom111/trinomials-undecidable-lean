import Trinomial.Base.BaseAlgebraBasis
import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Primaryness and radical of the base ideal

The paper notes before Lemma 2.1 that the base ideal `J₀` is primary to the
maximal ideal

`(2S − 1, 2T − 1, D₁ − 1, …, D_N − 1)`.

This file proves that statement directly from the coordinate model `BaseAlgebra N`.
An element of that algebra is a unit exactly when its constant coordinate is nonzero,
and an element with zero constant coordinate has fifth power zero.
-/

set_option autoImplicit false

namespace Trinomial

open BaseAlgebra

namespace BaseAlgebra

variable {N : ℕ}

instance : Nontrivial (BaseAlgebra N) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg BaseAlgebra.b0 h
    norm_num at this⟩⟩

theorem pow_five_eq_zero_of_b0_eq_zero (x : BaseAlgebra N) (hx : x.b0 = 0) :
    x ^ 5 = 0 := by
  ext <;> simp [pow_succ, hx]

theorem isUnit_iff_b0_ne_zero (x : BaseAlgebra N) : IsUnit x ↔ x.b0 ≠ 0 := by
  constructor
  · intro hx h0
    have hn : IsNilpotent x := ⟨5, pow_five_eq_zero_of_b0_eq_zero x h0⟩
    exact hx.not_isNilpotent hn
  · intro hx
    let n : BaseAlgebra N := x - algebraMap ℚ (BaseAlgebra N) x.b0
    have hn0 : n.b0 = 0 := by
      dsimp only [n]
      change x.b0 + -x.b0 = 0
      exact add_neg_cancel _
    have hn : IsNilpotent n := ⟨5, pow_five_eq_zero_of_b0_eq_zero n hn0⟩
    have huQ : IsUnit x.b0 := isUnit_iff_ne_zero.mpr hx
    have hu : IsUnit (algebraMap ℚ (BaseAlgebra N) x.b0) :=
      huQ.map (algebraMap ℚ (BaseAlgebra N))
    have hunit : IsUnit (algebraMap ℚ (BaseAlgebra N) x.b0 + n) :=
      hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    simpa [n] using hunit

/-- The residue map at the unique closed point of `A₀`. -/
def residueAlgHom (N : ℕ) : BaseAlgebra N →ₐ[ℚ] ℚ where
  toFun := BaseAlgebra.b0
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem residueAlgHom_apply (x : BaseAlgebra N) : residueAlgHom N x = x.b0 := rfl

end BaseAlgebra

variable {N : ℕ}

/-- Evaluation at `(S,T,D)=(1/2,1/2,1)`. -/
noncomputable def basePointEval (N : ℕ) : Laurent N →ₐ[ℚ] ℚ :=
  (BaseAlgebra.residueAlgHom N).comp (baseEval N)

@[simp] theorem basePointEval_S : basePointEval N (S N) = 1 / 2 := by
  simp [basePointEval, baseEval_S]

@[simp] theorem basePointEval_T : basePointEval N (T N) = 1 / 2 := by
  simp [basePointEval, baseEval_T]

@[simp] theorem basePointEval_D (i : Fin N) : basePointEval N (D i) = 1 := by
  simp [basePointEval, baseEval_D]

/-- The displayed maximal ideal `(2S−1, 2T−1, Dᵢ−1)` from the paper. -/
def baseMaximalIdealGens (N : ℕ) : Set (Laurent N) :=
  {2 * S N - 1, 2 * T N - 1} ∪ Set.range (fun i : Fin N => D i - 1)

noncomputable def baseMaximalIdeal (N : ℕ) : Ideal (Laurent N) :=
  Ideal.span (baseMaximalIdealGens N)

theorem baseMaximalIdeal_le_ker :
    baseMaximalIdeal N ≤ RingHom.ker (basePointEval N) := by
  rw [baseMaximalIdeal, Ideal.span_le]
  rintro f ((rfl | rfl) | ⟨i, rfl⟩)
  · change basePointEval N (2 * S N - 1) = 0
    rw [map_sub, map_mul, map_ofNat, basePointEval_S, map_one]
    change (2 : ℚ) * (1 / 2) - 1 = 0
    norm_num
  · change basePointEval N (2 * T N - 1) = 0
    rw [map_sub, map_mul, map_ofNat, basePointEval_T, map_one]
    change (2 : ℚ) * (1 / 2) - 1 = 0
    norm_num
  · simp [RingHom.mem_ker]

theorem basePoint_quot_factor :
    ((Algebra.ofId ℚ (Laurent N ⧸ baseMaximalIdeal N)).comp (basePointEval N) :
      Laurent N →ₐ[ℚ] Laurent N ⧸ baseMaximalIdeal N) =
      Ideal.Quotient.mkₐ ℚ (baseMaximalIdeal N) := by
  apply algHom_ext_laurent
  · rw [AlgHom.comp_apply, basePointEval_S]
    change Ideal.Quotient.mk (baseMaximalIdeal N)
        (algebraMap ℚ (Laurent N) (1 / 2)) = _
    rw [Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    have hgen : 2 * S N - 1 ∈ baseMaximalIdeal N :=
      Ideal.subset_span (Or.inl (Set.mem_insert _ _))
    have hscalar : algebraMap ℚ (Laurent N) (1 / 2) * 2 = 1 := by
      change algebraMap ℚ (Laurent N) (1 / 2) * algebraMap ℚ (Laurent N) 2 = 1
      rw [← map_mul]
      rw [show (1 / 2 : ℚ) * 2 = 1 by norm_num, map_one]
    have htwo : algebraMap ℚ (Laurent N) (1 / 2) * (2 * S N - 1) =
        S N - algebraMap ℚ (Laurent N) (1 / 2) := by
      calc
        _ = (algebraMap ℚ (Laurent N) (1 / 2) * 2) * S N -
              algebraMap ℚ (Laurent N) (1 / 2) := by ring
        _ = _ := by rw [hscalar, one_mul]
    have hpos : S N - algebraMap ℚ (Laurent N) (1 / 2) ∈ baseMaximalIdeal N := by
      rw [← htwo]
      exact Ideal.mul_mem_left _ _ hgen
    simpa only [neg_sub] using (neg_mem hpos)
  · rw [AlgHom.comp_apply, basePointEval_T]
    change Ideal.Quotient.mk (baseMaximalIdeal N)
        (algebraMap ℚ (Laurent N) (1 / 2)) = _
    rw [Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    have hgen : 2 * T N - 1 ∈ baseMaximalIdeal N :=
      Ideal.subset_span (Or.inl (Set.mem_insert_of_mem _ rfl))
    have hscalar : algebraMap ℚ (Laurent N) (1 / 2) * 2 = 1 := by
      change algebraMap ℚ (Laurent N) (1 / 2) * algebraMap ℚ (Laurent N) 2 = 1
      rw [← map_mul]
      rw [show (1 / 2 : ℚ) * 2 = 1 by norm_num, map_one]
    have htwo : algebraMap ℚ (Laurent N) (1 / 2) * (2 * T N - 1) =
        T N - algebraMap ℚ (Laurent N) (1 / 2) := by
      calc
        _ = (algebraMap ℚ (Laurent N) (1 / 2) * 2) * T N -
              algebraMap ℚ (Laurent N) (1 / 2) := by ring
        _ = _ := by rw [hscalar, one_mul]
    have hpos : T N - algebraMap ℚ (Laurent N) (1 / 2) ∈ baseMaximalIdeal N := by
      rw [← htwo]
      exact Ideal.mul_mem_left _ _ hgen
    simpa only [neg_sub] using (neg_mem hpos)
  · intro i
    rw [AlgHom.comp_apply, basePointEval_D]
    change Ideal.Quotient.mk (baseMaximalIdeal N) 1 = _
    rw [Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    have hgen : D i - 1 ∈ baseMaximalIdeal N :=
      Ideal.subset_span (Or.inr ⟨i, rfl⟩)
    simpa only [neg_sub] using (neg_mem hgen)

theorem baseMaximalIdeal_eq_ker :
    baseMaximalIdeal N = RingHom.ker (basePointEval N) := by
  apply le_antisymm baseMaximalIdeal_le_ker
  intro f hf
  rw [RingHom.mem_ker] at hf
  have h := DFunLike.congr_fun (basePoint_quot_factor (N := N)) f
  rw [AlgHom.comp_apply, hf, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h.symm

theorem basePointEval_surjective : Function.Surjective (basePointEval N) := by
  intro q
  exact ⟨algebraMap ℚ (Laurent N) q, (basePointEval N).commutes q⟩

theorem baseMaximalIdeal_isMaximal (N : ℕ) : (baseMaximalIdeal N).IsMaximal := by
  rw [baseMaximalIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective (basePointEval N) basePointEval_surjective

/-- The base ideal `J₀` is primary. -/
theorem baseIdeal_isPrimary (N : ℕ) : (baseIdeal N).IsPrimary := by
  rw [Ideal.isPrimary_iff]
  refine ⟨baseIdeal_ne_top, ?_⟩
  intro x y hxy
  rw [mem_baseIdeal_iff] at hxy
  rw [map_mul] at hxy
  by_cases hx : baseEval N x = 0
  · exact Or.inl ((mem_baseIdeal_iff x).mpr hx)
  · right
    have hy0 : (baseEval N y).b0 = 0 := by
      by_contra hy
      have hyu : IsUnit (baseEval N y) :=
        (BaseAlgebra.isUnit_iff_b0_ne_zero _).mpr hy
      exact hx (hyu.mul_left_eq_zero.mp hxy)
    rw [Ideal.mem_radical_iff]
    refine ⟨5, (mem_baseIdeal_iff _).mpr ?_⟩
    rw [map_pow, BaseAlgebra.pow_five_eq_zero_of_b0_eq_zero _ hy0]

/-- The radical of `J₀` is the displayed maximal ideal
`(2S−1, 2T−1, Dᵢ−1)`. -/
theorem radical_baseIdeal (N : ℕ) :
    (baseIdeal N).radical = baseMaximalIdeal N := by
  apply le_antisymm
  · exact (baseMaximalIdeal_isMaximal N).isPrime.radical_le_iff.mpr fun f hf => by
      rw [baseMaximalIdeal_eq_ker, RingHom.mem_ker]
      change ((baseEval N f).b0 = 0)
      rw [mem_baseIdeal_iff] at hf
      rw [hf]
      rfl
  · intro f hf
    rw [baseMaximalIdeal_eq_ker, RingHom.mem_ker] at hf
    rw [Ideal.mem_radical_iff]
    refine ⟨5, (mem_baseIdeal_iff _).mpr ?_⟩
    rw [map_pow]
    apply BaseAlgebra.pow_five_eq_zero_of_b0_eq_zero
    exact hf

end Trinomial
