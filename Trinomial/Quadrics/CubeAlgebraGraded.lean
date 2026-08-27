import Trinomial.Quadrics.CubeAlgebraStructure
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading of the cube-zero algebra `A_B`

This module completes the graded part of [Lemma 3.2].  The cube-zero algebra
`A_B = ℚ ⊕ V ⊕ ℚζ` has homogeneous components

* degree zero: `ℚ · 1`;
* degree one: `V`;
* degree two: `ℚζ`;
* degree at least three: zero.

The family `homogeneousComponent B` is made into a `GradedAlgebra` by an explicit
`DirectSum.Decomposition` and the multiplication rules of `CubeAlgebra B`.
-/

set_option autoImplicit false

namespace Trinomial

open scoped DirectSum

namespace CubeAlgebra

variable {ι : Type*} [Fintype ι] {B : BilinearFormMatrix ι}

/-- The degree-zero component `ℚ · 1` of `A_B`. -/
def degreeZero (B : BilinearFormMatrix ι) : Submodule ℚ (CubeAlgebra B) where
  carrier := {x | x.vector = 0 ∧ x.socle = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxv, hxs⟩ ⟨hyv, hys⟩
    simp [hxv, hxs, hyv, hys]
  smul_mem' := by
    rintro c x ⟨hxv, hxs⟩
    simp [hxv, hxs]

/-- The degree-one component `V` of `A_B`. -/
def degreeOne (B : BilinearFormMatrix ι) : Submodule ℚ (CubeAlgebra B) where
  carrier := {x | x.scalar = 0 ∧ x.socle = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxr, hxs⟩ ⟨hyr, hys⟩
    simp [hxr, hxs, hyr, hys]
  smul_mem' := by
    rintro c x ⟨hxr, hxs⟩
    simp [hxr, hxs]

/-- The degree-two component `ℚζ` of `A_B`. -/
def degreeTwo (B : BilinearFormMatrix ι) : Submodule ℚ (CubeAlgebra B) where
  carrier := {x | x.scalar = 0 ∧ x.vector = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxr, hxv⟩ ⟨hyr, hyv⟩
    simp [hxr, hxv, hyr, hyv]
  smul_mem' := by
    rintro c x ⟨hxr, hxv⟩
    simp [hxr, hxv]

@[simp] theorem mem_degreeZero_iff (x : CubeAlgebra B) :
    x ∈ degreeZero B ↔ x.vector = 0 ∧ x.socle = 0 :=
  Iff.rfl

@[simp] theorem mem_degreeOne_iff (x : CubeAlgebra B) :
    x ∈ degreeOne B ↔ x.scalar = 0 ∧ x.socle = 0 :=
  Iff.rfl

@[simp] theorem mem_degreeTwo_iff (x : CubeAlgebra B) :
    x ∈ degreeTwo B ↔ x.scalar = 0 ∧ x.vector = 0 :=
  Iff.rfl

/-- The homogeneous components of `A_B`, indexed by their nonnegative degree. -/
def homogeneousComponent (B : BilinearFormMatrix ι) : ℕ → Submodule ℚ (CubeAlgebra B)
  | 0 => degreeZero B
  | 1 => degreeOne B
  | 2 => degreeTwo B
  | _ + 3 => ⊥

@[simp] theorem homogeneousComponent_zero : homogeneousComponent B 0 = degreeZero B := rfl
@[simp] theorem homogeneousComponent_one : homogeneousComponent B 1 = degreeOne B := rfl
@[simp] theorem homogeneousComponent_two : homogeneousComponent B 2 = degreeTwo B := rfl
@[simp] theorem homogeneousComponent_add_three (n : ℕ) :
    homogeneousComponent B (n + 3) = ⊥ := by
  rfl

/-- The scalar-coordinate projection into the degree-zero component. -/
def degreeZeroProjection (B : BilinearFormMatrix ι) :
    CubeAlgebra B →ₗ[ℚ] degreeZero B where
  toFun x := ⟨⟨x.scalar, 0, 0⟩, by simp [degreeZero]⟩
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

/-- The vector-coordinate projection into the degree-one component. -/
def degreeOneProjection (B : BilinearFormMatrix ι) :
    CubeAlgebra B →ₗ[ℚ] degreeOne B where
  toFun x := ⟨⟨0, x.vector, 0⟩, by simp [degreeOne]⟩
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

/-- The socle-coordinate projection into the degree-two component. -/
def degreeTwoProjection (B : BilinearFormMatrix ι) :
    CubeAlgebra B →ₗ[ℚ] degreeTwo B where
  toFun x := ⟨⟨0, 0, x.socle⟩, by simp [degreeTwo]⟩
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem degreeZeroProjection_degreeZero (x : degreeZero B) :
    degreeZeroProjection B x = x := by
  obtain ⟨hxv, hxs⟩ := (mem_degreeZero_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeZeroProjection, hxv, hxs]

@[simp] theorem degreeOneProjection_degreeZero (x : degreeZero B) :
    degreeOneProjection B x = 0 := by
  obtain ⟨hxv, _⟩ := (mem_degreeZero_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeOneProjection, hxv]

@[simp] theorem degreeTwoProjection_degreeZero (x : degreeZero B) :
    degreeTwoProjection B x = 0 := by
  obtain ⟨_, hxs⟩ := (mem_degreeZero_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeTwoProjection, hxs]

@[simp] theorem degreeZeroProjection_degreeOne (x : degreeOne B) :
    degreeZeroProjection B x = 0 := by
  obtain ⟨hxr, _⟩ := (mem_degreeOne_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeZeroProjection, hxr]

@[simp] theorem degreeOneProjection_degreeOne (x : degreeOne B) :
    degreeOneProjection B x = x := by
  obtain ⟨hxr, hxs⟩ := (mem_degreeOne_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeOneProjection, hxr, hxs]

@[simp] theorem degreeTwoProjection_degreeOne (x : degreeOne B) :
    degreeTwoProjection B x = 0 := by
  obtain ⟨_, hxs⟩ := (mem_degreeOne_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeTwoProjection, hxs]

@[simp] theorem degreeZeroProjection_degreeTwo (x : degreeTwo B) :
    degreeZeroProjection B x = 0 := by
  obtain ⟨hxr, _⟩ := (mem_degreeTwo_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeZeroProjection, hxr]

@[simp] theorem degreeOneProjection_degreeTwo (x : degreeTwo B) :
    degreeOneProjection B x = 0 := by
  obtain ⟨_, hxv⟩ := (mem_degreeTwo_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeOneProjection, hxv]

@[simp] theorem degreeTwoProjection_degreeTwo (x : degreeTwo B) :
    degreeTwoProjection B x = x := by
  obtain ⟨hxr, hxv⟩ := (mem_degreeTwo_iff (x : CubeAlgebra B)).mp x.property
  apply Subtype.ext
  ext <;> simp [degreeTwoProjection, hxr, hxv]

/-- The explicit decomposition of an element of `A_B` into degrees zero, one, and two. -/
def gradedDecompose (B : BilinearFormMatrix ι) :
    CubeAlgebra B →ₗ[ℚ] (⨁ n, homogeneousComponent B n) :=
  (DirectSum.lof ℚ ℕ (fun n => homogeneousComponent B n) 0).comp (degreeZeroProjection B)
    + (DirectSum.lof ℚ ℕ (fun n => homogeneousComponent B n) 1).comp (degreeOneProjection B)
    + (DirectSum.lof ℚ ℕ (fun n => homogeneousComponent B n) 2).comp (degreeTwoProjection B)

theorem coe_gradedDecompose (x : CubeAlgebra B) :
    DirectSum.coeLinearMap (homogeneousComponent B) (gradedDecompose B x) = x := by
  simp only [gradedDecompose, LinearMap.add_apply, LinearMap.comp_apply,
    DirectSum.lof_eq_of, map_add, DirectSum.coeLinearMap_of,
    degreeZeroProjection, degreeOneProjection, degreeTwoProjection]
  ext <;> simp

theorem gradedDecompose_of (n : ℕ) (x : homogeneousComponent B n) :
    gradedDecompose B (x : CubeAlgebra B) =
      DirectSum.of (fun n => homogeneousComponent B n) n x := by
  rcases n with _ | _ | _ | n
  · simp [gradedDecompose]
    rfl
  · simp [gradedDecompose]
    rfl
  · simp [gradedDecompose]
    rfl
  · have hx := x.property
    change (x : CubeAlgebra B) ∈ (⊥ : Submodule ℚ (CubeAlgebra B)) at hx
    have hx0 : x = 0 := Subtype.ext ((Submodule.mem_bot ℚ).mp hx)
    rw [hx0]
    simp

/-- The homogeneous components are closed under multiplication in the additive degree. -/
instance homogeneousComponentGradedMonoid :
    SetLike.GradedMonoid (homogeneousComponent B) where
  one_mem := by
    simp [degreeZero]
  mul_mem := by
    intro i j x y hx hy
    rcases i with (_ | _ | _ | i) <;> rcases j with (_ | _ | _ | j)
    all_goals simp only [homogeneousComponent] at hx hy ⊢
    all_goals simp_all [CubeAlgebra.ext_iff]

/-- The coordinate splitting is a direct-sum decomposition of `A_B`. -/
instance homogeneousComponentDecomposition :
    DirectSum.Decomposition (homogeneousComponent B) :=
  DirectSum.Decomposition.ofLinearMap (homogeneousComponent B) (gradedDecompose B)
    (by
      apply LinearMap.ext
      exact coe_gradedDecompose)
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
      exact gradedDecompose_of n x)

/-- The grading `A_B = A_0 ⊕ A_1 ⊕ A_2` of [Lemma 3.2]. -/
instance homogeneousComponentGradedAlgebra :
    GradedAlgebra (homogeneousComponent B) where
  toGradedMonoid := homogeneousComponentGradedMonoid
  toDecomposition := homogeneousComponentDecomposition

end CubeAlgebra

end Trinomial
