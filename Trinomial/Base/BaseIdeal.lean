import Trinomial.Base.BaseAlgebra
import Trinomial.Base.Trinomials
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The base ideal `J₀` and its membership criterion

[§2, eq. (1)].  The base ideal is

  `J₀ = ⟨S+T−1, (S−T)⁵⟩ + ⟨(S−T)(Dᵢ−1)⟩ + ⟨(Dᵢ−1)(Dⱼ−1)⟩ ⊆ L_N`.

The central result of this module is `mem_baseIdeal_iff`:

  `f ∈ J₀  ⟺  baseEval f = 0`,

so membership in `J₀` is the vanishing of the `N+5` coordinates of the normal form —
which is precisely how the paper uses Lemmas 2.1 and 2.2.  The inclusion
`J₀ ⊆ ker` is a computation on the four families of generators.  For the reverse
inclusion we use the universal property of `A₀`: any commutative `ℚ`-algebra containing
elements `b, c₁, …, c_N` with `b⁵ = 0`, `b·cᵢ = 0`, `cᵢ·cⱼ = 0` (packaged as `NilData`)
receives an algebra homomorphism from `BaseAlgebra N` (`NilData.lift`).  Applying this
to the quotient `L_N ⧸ J₀` shows that the quotient map factors through `baseEval`.

The module ends with Proposition 2.4 (ii)–(iii), membership of the two trinomial families
and of the quadrinomial `Ω` in `J₀`.
-/

set_option autoImplicit false

namespace Trinomial

open BaseAlgebra

variable {N : ℕ}

/-- The generators of the base ideal [eq. (1)].  The products `(Dᵢ−1)(Dⱼ−1)`
are taken over all ordered pairs `(i, j)` rather than over `i ≤ j` as in the paper; by
commutativity the two sets generate the same ideal. -/
def baseIdealGens (N : ℕ) : Set (Laurent N) :=
  {S N + T N - 1, (S N - T N) ^ 5}
    ∪ Set.range (fun i : Fin N => (S N - T N) * (D i - 1))
    ∪ Set.range (fun p : Fin N × Fin N => (D p.1 - 1) * (D p.2 - 1))

/-- The base ideal `J₀`  [eq. (1)]. -/
noncomputable def baseIdeal (N : ℕ) : Ideal (Laurent N) :=
  Ideal.span (baseIdealGens N)

/-! ### `J₀ ⊆ ker baseEval`: the generators evaluate to zero -/

theorem baseEval_S_add_T_sub_one : baseEval N (S N + T N - 1) = 0 := by
  rw [map_sub, map_add, map_one, baseEval_S, baseEval_T]
  ext <;> simp [sub_eq_add_neg] <;> norm_num

theorem baseEval_S_sub_T : baseEval N (S N - T N) = BaseAlgebra.B N := by
  rw [map_sub, baseEval_S, baseEval_T]
  ext <;> simp [sub_eq_add_neg, BaseAlgebra.B]
  norm_num

theorem baseEval_D_sub_one (i : Fin N) : baseEval N (D i - 1) = BaseAlgebra.C i := by
  rw [map_sub, map_one, baseEval_D]
  refine BaseAlgebra.ext (by simp [sub_eq_add_neg, BaseAlgebra.C])
    (by simp [sub_eq_add_neg, BaseAlgebra.C]) (by simp [sub_eq_add_neg, BaseAlgebra.C])
    (by simp [sub_eq_add_neg, BaseAlgebra.C]) (by simp [sub_eq_add_neg, BaseAlgebra.C]) ?_
  funext j
  simp [sub_eq_add_neg, BaseAlgebra.C]

theorem baseIdeal_le_ker : baseIdeal N ≤ RingHom.ker (baseEval N) := by
  rw [baseIdeal, Ideal.span_le]
  rintro f (((rfl | rfl) | ⟨i, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · exact baseEval_S_add_T_sub_one
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, baseEval_S_sub_T, B_pow5]
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_mul, baseEval_S_sub_T,
      baseEval_D_sub_one, B_mul_C]
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_mul, baseEval_D_sub_one,
      baseEval_D_sub_one, C_mul_C]

/-- `S + T − 1` is one of the generators of `J₀`. -/
theorem gen_A_mem : S N + T N - 1 ∈ baseIdeal N :=
  Ideal.subset_span (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_insert _ _)))

/-! ### The universal property of `A₀` -/

/-- The defining relations of `A₀`, in an arbitrary commutative ring: an element `b`
with `b⁵ = 0` and elements `cᵢ` annihilating `b` and each other.  `BaseAlgebra N`
itself carries this data, and so does `L_N ⧸ J₀`. -/
structure NilData (N : ℕ) (R : Type*) [CommRing R] where
  /-- The image of `S − T`. -/
  b : R
  /-- The images of `D_i − 1`. -/
  c : Fin N → R
  /-- `B⁵ = 0`. -/
  b_pow5 : b ^ 5 = 0
  /-- `B·Cᵢ = 0`. -/
  b_mul_c : ∀ i, b * c i = 0
  /-- `CᵢCⱼ = 0`. -/
  c_mul_c : ∀ i j, c i * c j = 0

namespace NilData

variable {R : Type*} [CommRing R] [Algebra ℚ R] (Δ : NilData N R)

/-- The linear extension of `B^k ↦ b^k`, `Cᵢ ↦ cᵢ`. -/
def liftFun (x : BaseAlgebra N) : R :=
  algebraMap ℚ R x.b0 + algebraMap ℚ R x.b1 * Δ.b + algebraMap ℚ R x.b2 * Δ.b ^ 2
    + algebraMap ℚ R x.b3 * Δ.b ^ 3 + algebraMap ℚ R x.b4 * Δ.b ^ 4
    + ∑ i, algebraMap ℚ R (x.c i) * Δ.c i

lemma b_mul_sum (g : Fin N → ℚ) :
    Δ.b * ∑ i, algebraMap ℚ R (g i) * Δ.c i = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_left_comm, Δ.b_mul_c, mul_zero]

lemma sum_mul_sum_c (g h : Fin N → ℚ) :
    (∑ i, algebraMap ℚ R (g i) * Δ.c i) * (∑ j, algebraMap ℚ R (h j) * Δ.c j) = 0 := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [mul_mul_mul_comm, Δ.c_mul_c, mul_zero]

lemma liftFun_mul (x y : BaseAlgebra N) :
    Δ.liftFun (x * y) = Δ.liftFun x * Δ.liftFun y := by
  have hw : (∑ i, algebraMap ℚ R ((x * y).c i) * Δ.c i)
      = algebraMap ℚ R x.b0 * (∑ i, algebraMap ℚ R (y.c i) * Δ.c i)
        + algebraMap ℚ R y.b0 * (∑ i, algebraMap ℚ R (x.c i) * Δ.c i) := by
    have step : ∀ i, algebraMap ℚ R ((x * y).c i) * Δ.c i
        = algebraMap ℚ R x.b0 * (algebraMap ℚ R (y.c i) * Δ.c i)
          + algebraMap ℚ R y.b0 * (algebraMap ℚ R (x.c i) * Δ.c i) := by
      intro i
      rw [mul_c, map_add, map_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have hbu := Δ.b_mul_sum x.c
  have hbv := Δ.b_mul_sum y.c
  have huv := Δ.sum_mul_sum_c x.c y.c
  rw [liftFun, liftFun, liftFun, hw]
  simp only [mul_b0, mul_b1, mul_b2, mul_b3, mul_b4, map_add, map_mul]
  linear_combination
    (-(algebraMap ℚ R x.b1 * algebraMap ℚ R y.b4 + algebraMap ℚ R x.b2 * algebraMap ℚ R y.b3
        + algebraMap ℚ R x.b3 * algebraMap ℚ R y.b2 + algebraMap ℚ R x.b4 * algebraMap ℚ R y.b1)
      - (algebraMap ℚ R x.b2 * algebraMap ℚ R y.b4 + algebraMap ℚ R x.b3 * algebraMap ℚ R y.b3
        + algebraMap ℚ R x.b4 * algebraMap ℚ R y.b2) * Δ.b
      - (algebraMap ℚ R x.b3 * algebraMap ℚ R y.b4
        + algebraMap ℚ R x.b4 * algebraMap ℚ R y.b3) * Δ.b ^ 2
      - (algebraMap ℚ R x.b4 * algebraMap ℚ R y.b4) * Δ.b ^ 3) * Δ.b_pow5
    - (algebraMap ℚ R x.b1 + algebraMap ℚ R x.b2 * Δ.b + algebraMap ℚ R x.b3 * Δ.b ^ 2
        + algebraMap ℚ R x.b4 * Δ.b ^ 3) * hbv
    - (algebraMap ℚ R y.b1 + algebraMap ℚ R y.b2 * Δ.b + algebraMap ℚ R y.b3 * Δ.b ^ 2
        + algebraMap ℚ R y.b4 * Δ.b ^ 3) * hbu
    - huv

/-- The universal property of `A₀`: it maps to any `ℚ`-algebra with elements
satisfying the relations `b⁵ = 0`, `b·cᵢ = 0`, `cᵢ·cⱼ = 0`. -/
def lift : BaseAlgebra N →ₐ[ℚ] R where
  toFun := Δ.liftFun
  map_one' := by simp [liftFun]
  map_mul' := Δ.liftFun_mul
  map_zero' := by simp [liftFun]
  map_add' x y := by
    simp only [liftFun, add_b0, add_b1, add_b2, add_b3, add_b4, add_c, map_add, add_mul,
      Finset.sum_add_distrib]
    ring
  commutes' r := by simp [liftFun]

@[simp] lemma lift_apply (x : BaseAlgebra N) : Δ.lift x = Δ.liftFun x := rfl

end NilData

/-! ### `ker baseEval ⊆ J₀` via the quotient -/

/-- The images of `S − T` and `Dᵢ − 1` in `L_N ⧸ J₀` satisfy the relations of `A₀`. -/
noncomputable def quotNilData (N : ℕ) : NilData N (Laurent N ⧸ baseIdeal N) where
  b := Ideal.Quotient.mk (baseIdeal N) (S N - T N)
  c i := Ideal.Quotient.mk (baseIdeal N) (D i - 1)
  b_pow5 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_insert_of_mem _ rfl)))
  b_mul_c i := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨i, rfl⟩))
  c_mul_c i j := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_union_right _ ⟨(i, j), rfl⟩)

/-- The quotient map `L_N → L_N ⧸ J₀` factors through the normal form:
`π = lift ∘ baseEval`.  This is the formal content of Lemma 2.2. -/
theorem quot_factor :
    ((quotNilData N).lift.comp (baseEval N) : Laurent N →ₐ[ℚ] Laurent N ⧸ baseIdeal N)
      = Ideal.Quotient.mkₐ ℚ (baseIdeal N) := by
  have half : (algebraMap ℚ (Laurent N) (1/2)) + algebraMap ℚ (Laurent N) (1/2) = 1 := by
    rw [← map_add, show (1/2 + 1/2 : ℚ) = 1 by norm_num, map_one]
  have hneg : algebraMap ℚ (Laurent N) (-1/2) = -algebraMap ℚ (Laurent N) (1/2) := by
    rw [show (-1/2 : ℚ) = -(1/2) by norm_num, map_neg]
  have hq : ∀ r : ℚ, algebraMap ℚ (Laurent N ⧸ baseIdeal N) r
      = Ideal.Quotient.mk (baseIdeal N) (algebraMap ℚ (Laurent N) r) := fun r => rfl
  apply algHom_ext_laurent
  · -- image of S: `q(1/2) + q(1/2)·(S−T) ≡ S mod J₀`
    rw [AlgHom.comp_apply, baseEval_S, NilData.lift_apply, NilData.liftFun]
    simp only [quotNilData, map_zero, zero_mul, add_zero, Pi.zero_apply,
      Finset.sum_const_zero, Ideal.Quotient.mkₐ_eq_mk, hq, ← map_mul, ← map_add,
      Ideal.Quotient.eq]
    have : (algebraMap ℚ (Laurent N) (1/2)
          + algebraMap ℚ (Laurent N) (1/2) * (S N - T N)) - S N
        = algebraMap ℚ (Laurent N) (-(1/2)) * (S N + T N - 1) := by
      rw [map_neg]
      linear_combination S N * half
    rw [this]
    exact Ideal.mul_mem_left _ _ gen_A_mem
  · -- image of T: `q(1/2) − q(1/2)·(S−T) ≡ T mod J₀`
    rw [AlgHom.comp_apply, baseEval_T, NilData.lift_apply, NilData.liftFun]
    simp only [quotNilData, map_zero, zero_mul, add_zero, Pi.zero_apply,
      Finset.sum_const_zero, Ideal.Quotient.mkₐ_eq_mk, hq, ← map_mul, ← map_add,
      Ideal.Quotient.eq]
    have : (algebraMap ℚ (Laurent N) (1/2)
          + algebraMap ℚ (Laurent N) (-1/2) * (S N - T N)) - T N
        = -algebraMap ℚ (Laurent N) (1/2) * (S N + T N - 1) := by
      rw [hneg]
      linear_combination T N * half
    rw [this]
    exact Ideal.mul_mem_left _ _ gen_A_mem
  · -- image of Dᵢ: `1 + (Dᵢ − 1) ≡ Dᵢ mod J₀` on the nose
    intro i
    rw [AlgHom.comp_apply, baseEval_D, NilData.lift_apply, NilData.liftFun]
    simp only [quotNilData, map_zero, zero_mul, add_zero, map_one,
      Ideal.Quotient.mkₐ_eq_mk]
    have step : ∀ j : Fin N,
        algebraMap ℚ (Laurent N ⧸ baseIdeal N) ((Pi.single i 1 : Fin N → ℚ) j)
          * Ideal.Quotient.mk (baseIdeal N) (D j - 1)
        = if j = i then Ideal.Quotient.mk (baseIdeal N) (D j - 1) else 0 := by
      intro j
      rw [Pi.single_apply]
      split
      · rw [map_one, one_mul]
      · rw [map_zero, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, if_true]
    rw [← map_one (Ideal.Quotient.mk (baseIdeal N)), ← map_add]
    congr 1
    ring

theorem ker_le_baseIdeal : RingHom.ker (baseEval N) ≤ baseIdeal N := by
  intro f hf
  rw [RingHom.mem_ker] at hf
  have h := DFunLike.congr_fun (quot_factor (N := N)) f
  rw [AlgHom.comp_apply, hf, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h.symm

/-- **Membership criterion for the base ideal**: `f ∈ J₀ ⟺ baseEval f = 0`.
Ideal membership becomes the vanishing of the `N+5` coordinates of the normal form,
which is precisely how the paper uses Lemmas 2.1 and 2.2. -/
theorem mem_baseIdeal_iff (f : Laurent N) : f ∈ baseIdeal N ↔ baseEval N f = 0 :=
  ⟨fun h => baseIdeal_le_ker h, fun h => ker_le_baseIdeal (RingHom.mem_ker.mpr h)⟩

/-- `J₀` is a proper ideal. -/
theorem baseIdeal_ne_top : baseIdeal N ≠ ⊤ := by
  intro h
  have h1 : (1 : Laurent N) ∈ baseIdeal N := h ▸ Submodule.mem_top
  rw [mem_baseIdeal_iff, map_one] at h1
  exact one_ne_zero (congrArg BaseAlgebra.b0 h1)

/-! ### The trinomial families and `Ω` lie in `J₀`  [Proposition 2.4 (ii), (iii)] -/

theorem baseEval_tau (d : Fin N → ℤ) : baseEval N (tau d) = 0 := by
  rw [tau, map_sub, map_sub, map_one, baseEval_mono, baseEval_mono, baseMonoUnit_val,
    baseMonoUnit_val]
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ (funext fun j => ?_) <;>
    simp [w1, w2, w3, w4, sub_eq_add_neg] <;> norm_num

/-- The affine trinomial `τ_d` lies in `J₀` for every `d ∈ ℤ^N`. -/
theorem tau_mem_baseIdeal (d : Fin N → ℤ) : tau d ∈ baseIdeal N :=
  (mem_baseIdeal_iff _).mpr (baseEval_tau d)

theorem baseEval_theta (e : Fin N → ℤ) (p q : ℤ) : baseEval N (theta e p q) = 0 := by
  rw [theta, map_sub, map_add, map_smul, map_smul, map_smul, map_one, baseEval_mono,
    baseEval_mono, baseMonoUnit_val, baseMonoUnit_val]
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ (funext fun j => ?_) <;>
    simp [w1, w2, w3, w4, sub_eq_add_neg]
  ring

/-- The infinite trinomial `θ_e^{p,q}` lies in `J₀` (for all `e, p, q`). -/
theorem theta_mem_baseIdeal (e : Fin N → ℤ) (p q : ℤ) : theta e p q ∈ baseIdeal N :=
  (mem_baseIdeal_iff _).mpr (baseEval_theta e p q)

theorem baseEval_Omega : baseEval N (Omega N) = 0 := by
  rw [Omega, map_mul, baseEval_S_add_T_sub_one, zero_mul]

/-- The quadrinomial `Ω = (S+T−1)(S−T)` lies in `J₀`  [Proposition 2.4 (iii)]. -/
theorem Omega_mem_baseIdeal : Omega N ∈ baseIdeal N :=
  (mem_baseIdeal_iff _).mpr baseEval_Omega

end Trinomial
