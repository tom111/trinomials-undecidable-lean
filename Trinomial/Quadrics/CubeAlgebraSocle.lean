import Trinomial.Quadrics.CubeAlgebraStructure
import Mathlib.RingTheory.Ideal.Maps

/-!
# The socle of `A_B`

The paper's remark after Lemma 3.2 identifies the socle of
`A_B = ℚ ⊕ V ⊕ ℚζ` as `rad(B) ⊕ ℚζ`.  It follows that the socle is the
one-dimensional line `ℚζ` exactly when `B` is nondegenerate.  This is the standard
socle criterion for this Artin local algebra to be Gorenstein.
-/

set_option autoImplicit false

namespace Trinomial

namespace BilinearFormMatrix

variable {ι : Type*} [Fintype ι]

/-- The radical `rad(B) = {v | B(v,w)=0 for every w}` of the bilinear form. -/
def radical (B : BilinearFormMatrix ι) : Submodule ℚ (ι → ℚ) :=
  LinearMap.ker B.polar

theorem mem_radical_iff (B : BilinearFormMatrix ι) (v : ι → ℚ) :
    v ∈ B.radical ↔ ∀ w, B.polar v w = 0 := by
  rw [radical, LinearMap.mem_ker]
  constructor
  · intro h w
    exact DFunLike.congr_fun h w
  · intro h
    ext w
    exact h w

theorem radical_eq_bot_iff_nondegenerate (B : BilinearFormMatrix ι) :
    B.radical = ⊥ ↔ B.polar.Nondegenerate := by
  rw [radical, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

end BilinearFormMatrix

namespace CubeAlgebra

variable {ι : Type*} [Fintype ι] {B : BilinearFormMatrix ι}

/-- The socle of the local algebra `A_B`, defined as the annihilator of its maximal
ideal `nilideal B`. -/
def socleIdeal (B : BilinearFormMatrix ι) : Ideal (CubeAlgebra B) :=
  (nilideal B).annihilator

theorem mem_socleIdeal_iff (x : CubeAlgebra B) :
    x ∈ socleIdeal B ↔ x.scalar = 0 ∧ x.vector ∈ B.radical := by
  rw [socleIdeal, Submodule.mem_annihilator]
  constructor
  · intro hx
    have hz := hx (zeta B) zeta_mem_nilideal
    have hs : x.scalar = 0 := by
      have := congrArg CubeAlgebra.socle hz
      simpa [smul_eq_mul] using this
    refine ⟨hs, (B.mem_radical_iff x.vector).mpr fun w => ?_⟩
    have hw := hx (ofVector B w) (ofVector_mem_nilideal w)
    have := congrArg CubeAlgebra.socle hw
    simpa [smul_eq_mul, hs] using this
  · rintro ⟨hs, hv⟩ y hy
    have hy0 : y.scalar = 0 := (mem_nilideal_iff y).mp hy
    apply CubeAlgebra.ext <;> simp [smul_eq_mul, hs, hy0]
    exact (B.mem_radical_iff x.vector).mp hv y.vector

/-- Coordinate form of `soc(A_B) = rad(B) ⊕ ℚζ`. -/
theorem socleIdeal_eq_radical_plus_zeta (x : CubeAlgebra B) :
    x ∈ socleIdeal B ↔
      ∃ v : B.radical, ∃ s : ℚ, x = ⟨0, v.1, s⟩ := by
  rw [mem_socleIdeal_iff]
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨⟨x.vector, hv⟩, x.socle, by ext <;> simp [hs]⟩
  · rintro ⟨v, s, rfl⟩
    exact ⟨rfl, v.2⟩

/-- The socle as a `ℚ`-vector space is `rad(B) × ℚ`, with the second factor
corresponding to `ℚζ`. -/
noncomputable def socleEquivRadicalProd (B : BilinearFormMatrix ι) :
    socleIdeal B ≃ₗ[ℚ] B.radical × ℚ where
  toFun x := ⟨⟨x.1.vector, (mem_socleIdeal_iff x.1).mp x.2 |>.2⟩, x.1.socle⟩
  invFun x := ⟨⟨0, x.1.1, x.2⟩, (mem_socleIdeal_iff _).mpr ⟨rfl, x.1.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    ext <;> simp [(mem_socleIdeal_iff x.1).mp x.2 |>.1]
  right_inv x := by
    ext <;> simp
  map_add' x y := by
    ext <;> rfl
  map_smul' c x := by
    ext <;> simp

/-- The socle is exactly the line `ℚζ` if and only if `B` is nondegenerate. -/
theorem socle_is_zeta_line_iff_nondegenerate (B : BilinearFormMatrix ι) :
    (∀ x : CubeAlgebra B, x ∈ socleIdeal B ↔
      ∃ s : ℚ, x = s • zeta B) ↔ B.polar.Nondegenerate := by
  rw [← B.radical_eq_bot_iff_nondegenerate]
  constructor
  · intro h
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hsoc : ofVector B v ∈ socleIdeal B :=
      (mem_socleIdeal_iff _).mpr ⟨rfl, hv⟩
    obtain ⟨s, hs⟩ := (h (ofVector B v)).mp hsoc
    have := congrArg CubeAlgebra.vector hs
    simpa using this
  · intro hrad x
    rw [mem_socleIdeal_iff]
    constructor
    · rintro ⟨hs, hv⟩
      rw [hrad] at hv
      have hv0 : x.vector = 0 := hv
      refine ⟨x.socle, ?_⟩
      ext <;> simp [hs, hv0]
    · rintro ⟨s, rfl⟩
      simp [hrad]

end CubeAlgebra

end Trinomial
