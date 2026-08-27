import Trinomial.Quadrics.CubeAlgebraStructure

/-!
# The presentation `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` of Lemma 3.2

This module completes the presentation of the cube-zero algebra `A_B = ℚ ⊕ V ⊕ ℚζ`
[Lemma 3.2]: with `v₁, …, vₙ` the standard basis of `V = ℚ^ι`, `b_ij = B(vᵢ, vⱼ)`
and

  `I = ⟨XᵢXⱼ − b_ij Z⟩ + ⟨XᵢZ⟩ + ⟨Z²⟩ ⊆ ℚ[X₁, …, Xₙ, Z]`

(`relationIdeal B` of `Trinomial/Quadrics/CubeAlgebraStructure.lean`), the algebra map
`ℚ[X, Z] → A_B`, `Xᵢ ↦ vᵢ`, `Z ↦ ζ` (`presentation B`) induces `ℚ[X, Z]/I ≃ A_B`.

`CubeAlgebraStructure.lean` proves the easy half (`presentation_surjective`,
`relationIdeal_le_ker`).  The missing inclusion `ker ⊆ I` is proved here by a normal form
modulo `I`: every polynomial is congruent modulo `I` to a unique `c + ∑ᵢ vᵢ Xᵢ + d Z`
(`exists_normalForm`), and `ℚ[X, Z] → A_B` reads off the coordinates `(c, v, d)` of such a
normal form (`presentation_normalForm`), so a polynomial in the kernel is congruent to `0`.

Paper correspondence:

* `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` [Lemma 3.2] ↦ `ker_presentation`, `presentationEquiv`
* the normal form `c + ∑ᵢ vᵢ Xᵢ + d Z` modulo `I`  ↦ `exists_normalForm`,
                                                   `presentation_normalForm`
-/

set_option autoImplicit false

namespace Trinomial

namespace CubeAlgebra

open MvPolynomial

variable {ι : Type*} {B : BilinearFormMatrix ι}

/-! ### The generators of `I` and their classes modulo `I` -/

/-- `XᵢXⱼ − b_ij Z ∈ I`. -/
theorem X_mul_X_sub_mem_relationIdeal (i j : ι) :
    X (some i) * X (some j) - C (B.b i j) * X none ∈ relationIdeal B :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(i, j), rfl⟩))

/-- `XᵢZ ∈ I`. -/
theorem X_mul_Z_mem_relationIdeal (i : ι) :
    X (some i) * X none ∈ relationIdeal B :=
  Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))

/-- `Z² ∈ I`. -/
theorem Z_sq_mem_relationIdeal : (X none : MvPolynomial (Option ι) ℚ) ^ 2 ∈ relationIdeal B :=
  Ideal.subset_span (Or.inr rfl)

/-- `XᵢXⱼ ≡ b_ij Z` modulo `I`. -/
theorem mk_X_mul_X (i j : ι) :
    Ideal.Quotient.mk (relationIdeal B) (X (some i)) *
        Ideal.Quotient.mk (relationIdeal B) (X (some j)) =
      Ideal.Quotient.mk (relationIdeal B) (C (B.b i j)) *
        Ideal.Quotient.mk (relationIdeal B) (X none) := by
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
  exact X_mul_X_sub_mem_relationIdeal i j

/-- `XᵢZ ≡ 0` modulo `I`. -/
theorem mk_X_mul_Z (i : ι) :
    Ideal.Quotient.mk (relationIdeal B) (X (some i)) *
      Ideal.Quotient.mk (relationIdeal B) (X none) = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact X_mul_Z_mem_relationIdeal i

/-- `ZXᵢ ≡ 0` modulo `I`. -/
theorem mk_Z_mul_X (i : ι) :
    Ideal.Quotient.mk (relationIdeal B) (X none) *
      Ideal.Quotient.mk (relationIdeal B) (X (some i)) = 0 := by
  rw [mul_comm, mk_X_mul_Z]

/-- `Z² ≡ 0` modulo `I`. -/
theorem mk_Z_mul_Z :
    Ideal.Quotient.mk (relationIdeal B) (X none) *
      Ideal.Quotient.mk (relationIdeal B) (X none) = 0 := by
  rw [← map_mul, ← sq, Ideal.Quotient.eq_zero_iff_mem]
  exact Z_sq_mem_relationIdeal

/-! ### The normal form `c + ∑ᵢ vᵢ Xᵢ + d Z` modulo `I` -/

variable [Fintype ι]

/-- The linear combination `∑ᵢ (c·δ_ij) Xᵢ` is `c Xⱼ`. -/
theorem sum_C_single_mul_X [DecidableEq ι] (j : ι) (c : ℚ) :
    ∑ i, C ((Pi.single j c : ι → ℚ) i) * X (some i) =
      (C c * X (some j) : MvPolynomial (Option ι) ℚ) := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- The product of a normal form with a variable is congruent modulo `I` to a normal form:
`(c + ∑ᵢ vᵢ Xᵢ + d Z) Xⱼ ≡ c Xⱼ + (∑ᵢ vᵢ b_ij) Z` and `(c + ∑ᵢ vᵢ Xᵢ + d Z) Z ≡ c Z`. -/
theorem exists_mk_normalForm_mul_X (c : ℚ) (v : ι → ℚ) (d : ℚ) (o : Option ι) :
    ∃ (c' : ℚ) (v' : ι → ℚ) (d' : ℚ),
      Ideal.Quotient.mk (relationIdeal B)
          ((C c + ∑ i, C (v i) * X (some i) + C d * X none) * X o) =
        Ideal.Quotient.mk (relationIdeal B)
          (C c' + ∑ i, C (v' i) * X (some i) + C d' * X none) := by
  classical
  cases o with
  | none =>
    refine ⟨0, 0, c, ?_⟩
    simp [add_mul, Finset.sum_mul, mul_assoc, mk_X_mul_Z, mk_Z_mul_Z]
  | some j =>
    refine ⟨0, Pi.single j c, ∑ i, v i * B.b i j, ?_⟩
    rw [sum_C_single_mul_X]
    simp [add_mul, Finset.sum_mul, mul_assoc, mk_X_mul_X, mk_Z_mul_X]

/-- **Normal form modulo `I`** [Lemma 3.2]: every polynomial is congruent modulo
`I = ⟨XᵢXⱼ − b_ij Z, XᵢZ, Z²⟩` to one of the form `c + ∑ᵢ vᵢ Xᵢ + d Z`. -/
theorem exists_normalForm (p : MvPolynomial (Option ι) ℚ) :
    ∃ (c : ℚ) (v : ι → ℚ) (d : ℚ),
      p - (C c + ∑ i, C (v i) * X (some i) + C d * X none) ∈ relationIdeal B := by
  simp only [← Ideal.Quotient.eq]
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a, 0, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨c, v, d, hp⟩ := hp
    obtain ⟨c', v', d', hq⟩ := hq
    refine ⟨c + c', v + v', d + d', ?_⟩
    rw [map_add, hp, hq, ← map_add]
    congr 1
    simp only [Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p o hp =>
    obtain ⟨c, v, d, hp⟩ := hp
    rw [map_mul, hp, ← map_mul]
    exact exists_mk_normalForm_mul_X c v d o

/-! ### `ℚ[X, Z] → A_B` reads off the coordinates of a normal form -/

theorem sum_scalar {α : Type*} (s : Finset α) (f : α → CubeAlgebra B) :
    (∑ a ∈ s, f a).scalar = ∑ a ∈ s, (f a).scalar :=
  map_sum (AddMonoidHom.mk' scalar add_scalar) f s

theorem sum_vector {α : Type*} (s : Finset α) (f : α → CubeAlgebra B) :
    (∑ a ∈ s, f a).vector = ∑ a ∈ s, (f a).vector :=
  map_sum (AddMonoidHom.mk' vector add_vector) f s

theorem sum_socle {α : Type*} (s : Finset α) (f : α → CubeAlgebra B) :
    (∑ a ∈ s, f a).socle = ∑ a ∈ s, (f a).socle :=
  map_sum (AddMonoidHom.mk' socle add_socle) f s

variable [DecidableEq ι]

/-- The map `ℚ[X, Z] → A_B` sends the normal form `c + ∑ᵢ vᵢ Xᵢ + d Z` to the element
`(c, v, d)` of `A_B = ℚ ⊕ V ⊕ ℚζ`. -/
theorem presentation_normalForm (c : ℚ) (v : ι → ℚ) (d : ℚ) :
    presentation B (C c + ∑ i, C (v i) * X (some i) + C d * X none) = ⟨c, v, d⟩ := by
  simp only [map_add, map_sum, map_mul, presentation_C, presentation_X_some,
    presentation_X_none]
  ext
  · simp [sum_scalar]
  · simp [sum_vector, ← Pi.single_smul, Finset.univ_sum_single]
  · simp [sum_socle]

/-! ### Lemma 3.2: `ker (ℚ[X, Z] → A_B) = I` and `ℚ[X, Z]/I ≅ A_B` -/

/-- `ker (ℚ[X, Z] → A_B) ⊆ I`: a polynomial in the kernel is congruent modulo `I` to a
normal form `c + ∑ᵢ vᵢ Xᵢ + d Z` which is again in the kernel, so `(c, v, d) = 0` and the
polynomial lies in `I`. -/
theorem ker_le_relationIdeal : RingHom.ker (presentation B) ≤ relationIdeal B := by
  intro p hp
  obtain ⟨c, v, d, hq⟩ := exists_normalForm (B := B) p
  have h0 : presentation B (C c + ∑ i, C (v i) * X (some i) + C d * X none) = 0 := by
    have hker := relationIdeal_le_ker hq
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    rw [← hker]
    exact hp
  rw [presentation_normalForm] at h0
  obtain rfl : c = 0 := congrArg scalar h0
  obtain rfl : v = 0 := congrArg vector h0
  obtain rfl : d = 0 := congrArg socle h0
  simpa using hq

/-- **Lemma 3.2** (the kernel of the presentation): the kernel of `ℚ[X, Z] → A_B`,
`Xᵢ ↦ vᵢ`, `Z ↦ ζ` is exactly `I = ⟨XᵢXⱼ − b_ij Z⟩ + ⟨XᵢZ⟩ + ⟨Z²⟩`
[Lemma 3.2]. -/
theorem ker_presentation : RingHom.ker (presentation B) = relationIdeal B :=
  le_antisymm ker_le_relationIdeal relationIdeal_le_ker

/-- **Lemma 3.2** (the presentation): `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` as `ℚ`-algebras, the
isomorphism induced by `Xᵢ ↦ vᵢ`, `Z ↦ ζ` [Lemma 3.2]. -/
noncomputable def presentationEquiv (B : BilinearFormMatrix ι) :
    (MvPolynomial (Option ι) ℚ ⧸ relationIdeal B) ≃ₐ[ℚ] CubeAlgebra B :=
  (Ideal.quotientEquivAlgOfEq ℚ ker_presentation.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective presentation_surjective)

/-- `presentationEquiv` sends the class of `p` to its image under `ℚ[X, Z] → A_B`. -/
@[simp] theorem presentationEquiv_mk (p : MvPolynomial (Option ι) ℚ) :
    presentationEquiv B (Ideal.Quotient.mk (relationIdeal B) p) = presentation B p := rfl

/-- The class of the normal form `c + ∑ᵢ vᵢ Xᵢ + d Z` corresponds to `(c, v, d) ∈ A_B`. -/
theorem presentationEquiv_symm_mk (c : ℚ) (v : ι → ℚ) (d : ℚ) :
    (presentationEquiv B).symm ⟨c, v, d⟩ =
      Ideal.Quotient.mk (relationIdeal B) (C c + ∑ i, C (v i) * X (some i) + C d * X none) := by
  rw [AlgEquiv.symm_apply_eq, presentationEquiv_mk, presentation_normalForm]

end CubeAlgebra

end Trinomial
