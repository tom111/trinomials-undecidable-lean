import Trinomial.Base.BaseIdeal
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Lemma 2.1: the basis of `A₀ = L_N/J₀`, `dim_ℚ A₀ = N + 5`, and `dim J₀ = 0`

[Lemma 2.1]: "The ideal `J₀` has Krull dimension zero.  A `ℚ`-basis of
`A₀ := L_N/J₀` consists of the images of the monomials `1, B, B², B³, B⁴, C₁, …, C_N`,
and thus `dim_ℚ(A₀) = N + 5`."

`Trinomial/Base/BaseAlgebra.lean` realizes `A₀` as the coordinate algebra `BaseAlgebra N`
and `Trinomial/Base/BaseIdeal.lean` proves `J₀ = ker baseEval`.  This module completes the
identification:

* `baseEval_surjective` — `baseEval : L_N → A₀` is onto (the image contains
  `1, B = baseEval (S−T), …, B⁴` and `Cᵢ = baseEval (Dᵢ−1)`; `basePreimage` is an
  explicit preimage);
* `baseQuotEquiv` — the first isomorphism theorem `L_N ⧸ J₀ ≃ₐ[ℚ] A₀`;
* `baseBasis` — the basis `1, B, B², B³, B⁴, C₁, …, C_N` of `A₀`, indexed by
  `Fin 5 ⊕ Fin N` (`baseBasis_inl`, `baseBasis_inr`);
* `finrank_baseAlgebra`, `finrank_quotient_baseIdeal` — `dim_ℚ (L_N ⧸ J₀) = N + 5`;
* `ringKrullDim_quotient_baseIdeal` — `J₀` has Krull dimension zero: `L_N ⧸ J₀` is a
  finite-dimensional `ℚ`-algebra, hence Artinian, hence every prime ideal is maximal.
-/

set_option autoImplicit false

namespace Trinomial

open BaseAlgebra

variable {N : ℕ}

/-! ### The coordinate isomorphism `A₀ ≃ ℚ^{Fin 5 ⊕ Fin N}` -/

/-- The coordinates of `x ∈ A₀` with respect to `1, B, B², B³, B⁴` (indices `inl 0 … inl 4`)
and `C₁, …, C_N` (indices `inr i`)  [Lemma 2.1]. -/
def coords (x : BaseAlgebra N) : Fin 5 ⊕ Fin N → ℚ :=
  Sum.elim ![x.b0, x.b1, x.b2, x.b3, x.b4] x.c

/-- The element of `A₀` with the given coordinates; inverse to `coords`. -/
def ofCoords (v : Fin 5 ⊕ Fin N → ℚ) : BaseAlgebra N :=
  ⟨v (Sum.inl 0), v (Sum.inl 1), v (Sum.inl 2), v (Sum.inl 3), v (Sum.inl 4),
    fun i => v (Sum.inr i)⟩

@[simp] lemma coords_inl_zero (x : BaseAlgebra N) : coords x (Sum.inl 0) = x.b0 := rfl
@[simp] lemma coords_inl_one (x : BaseAlgebra N) : coords x (Sum.inl 1) = x.b1 := rfl
@[simp] lemma coords_inl_two (x : BaseAlgebra N) : coords x (Sum.inl 2) = x.b2 := rfl
@[simp] lemma coords_inl_three (x : BaseAlgebra N) : coords x (Sum.inl 3) = x.b3 := rfl
@[simp] lemma coords_inl_four (x : BaseAlgebra N) : coords x (Sum.inl 4) = x.b4 := rfl
@[simp] lemma coords_inr (x : BaseAlgebra N) (i : Fin N) : coords x (Sum.inr i) = x.c i := rfl

@[simp] lemma ofCoords_b0 (v : Fin 5 ⊕ Fin N → ℚ) : (ofCoords v).b0 = v (Sum.inl 0) := rfl
@[simp] lemma ofCoords_b1 (v : Fin 5 ⊕ Fin N → ℚ) : (ofCoords v).b1 = v (Sum.inl 1) := rfl
@[simp] lemma ofCoords_b2 (v : Fin 5 ⊕ Fin N → ℚ) : (ofCoords v).b2 = v (Sum.inl 2) := rfl
@[simp] lemma ofCoords_b3 (v : Fin 5 ⊕ Fin N → ℚ) : (ofCoords v).b3 = v (Sum.inl 3) := rfl
@[simp] lemma ofCoords_b4 (v : Fin 5 ⊕ Fin N → ℚ) : (ofCoords v).b4 = v (Sum.inl 4) := rfl
@[simp] lemma ofCoords_c (v : Fin 5 ⊕ Fin N → ℚ) (i : Fin N) :
    (ofCoords v).c i = v (Sum.inr i) := rfl

/-- The `ℚ`-linear isomorphism `A₀ ≃ ℚ^{Fin 5 ⊕ Fin N}`, `x ↦ coords x`: the coordinates
with respect to `1, B, B², B³, B⁴, C₁, …, C_N`  [Lemma 2.1]. -/
def baseCoordEquiv (N : ℕ) : BaseAlgebra N ≃ₗ[ℚ] (Fin 5 ⊕ Fin N → ℚ) where
  toFun := coords
  invFun := ofCoords
  map_add' x y := by
    funext k
    rcases k with k | i
    · fin_cases k <;> simp
    · simp
  map_smul' r x := by
    funext k
    rcases k with k | i
    · fin_cases k <;> simp
    · simp
  left_inv x := by
    ext <;> simp
  right_inv v := by
    funext k
    rcases k with k | i
    · fin_cases k <;> simp
    · simp

@[simp] lemma baseCoordEquiv_apply (x : BaseAlgebra N) : baseCoordEquiv N x = coords x := rfl
@[simp] lemma baseCoordEquiv_symm_apply (v : Fin 5 ⊕ Fin N → ℚ) :
    (baseCoordEquiv N).symm v = ofCoords v := rfl

/-! ### The basis `1, B, B², B³, B⁴, C₁, …, C_N` and the dimension `N + 5` -/

/-- **Lemma 2.1** (basis): the `ℚ`-basis of `A₀` indexed by `Fin 5 ⊕ Fin N`, whose
vectors are `1, B, B², B³, B⁴` (`baseBasis_inl`) and `C₁, …, C_N` (`baseBasis_inr`). -/
noncomputable def baseBasis (N : ℕ) : Module.Basis (Fin 5 ⊕ Fin N) ℚ (BaseAlgebra N) :=
  Module.Basis.ofEquivFun (baseCoordEquiv N)

/-- The basis vectors `inl k` are `B^k`, `k = 0, …, 4`. -/
theorem baseBasis_inl (k : Fin 5) : baseBasis N (Sum.inl k) = B N ^ (k : ℕ) := by
  rw [baseBasis, Module.Basis.coe_ofEquivFun]
  fin_cases k
  · ext <;> simp
  · ext <;> simp [B]
  · ext <;> simp
  · ext <;> simp
  · ext <;> simp

/-- The basis vectors `inr i` are the `Cᵢ`. -/
theorem baseBasis_inr (i : Fin N) : baseBasis N (Sum.inr i) = C i := by
  rw [baseBasis, Module.Basis.coe_ofEquivFun]
  ext <;> simp [C]
  simp only [Pi.single_apply, Sum.inr.injEq]

/-- **Lemma 2.1** (dimension): `dim_ℚ A₀ = N + 5`. -/
theorem finrank_baseAlgebra (N : ℕ) : Module.finrank ℚ (BaseAlgebra N) = N + 5 := by
  rw [Module.finrank_eq_card_basis (baseBasis N), Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, add_comm]

instance : Module.Finite ℚ (BaseAlgebra N) :=
  Module.Finite.equiv (baseCoordEquiv N).symm

/-! ### `baseEval` is onto, and `L_N ⧸ J₀ ≃ A₀` -/

/-- An explicit preimage under `baseEval` of the coordinate vector `x`: the linear
combination `b₀ + b₁(S−T) + b₂(S−T)² + b₃(S−T)³ + b₄(S−T)⁴ + Σᵢ cᵢ(Dᵢ−1)` of the monomials
`1, B, …, B⁴, Cᵢ` of Lemma 2.1, read in `L_N`. -/
noncomputable def basePreimage (x : BaseAlgebra N) : Laurent N :=
  algebraMap ℚ (Laurent N) x.b0 + x.b1 • (S N - T N) + x.b2 • (S N - T N) ^ 2
    + x.b3 • (S N - T N) ^ 3 + x.b4 • (S N - T N) ^ 4 + ∑ i, x.c i • (D i - 1)

theorem baseEval_basePreimage (x : BaseAlgebra N) : baseEval N (basePreimage x) = x := by
  apply (baseCoordEquiv N).injective
  rw [basePreimage]
  simp only [map_add, map_smul, map_pow, map_sum, AlgHom.commutes, baseEval_S_sub_T,
    baseEval_D_sub_one, B_pow2, B_pow3, B_pow4]
  funext k
  rcases k with k | j
  · fin_cases k <;> simp [B, C, Finset.sum_apply]
  · simp [B, C, Finset.sum_apply, Pi.single_apply]

/-- `baseEval : L_N → A₀` is surjective: every coordinate vector is the image of the
corresponding linear combination of `1, S−T, …, (S−T)⁴, Dᵢ−1`  [Lemma 2.1]. -/
theorem baseEval_surjective (N : ℕ) : Function.Surjective (baseEval N) :=
  fun x => ⟨basePreimage x, baseEval_basePreimage x⟩

/-- `J₀ = ker baseEval` as an equality of ideals (`mem_baseIdeal_iff`). -/
theorem baseIdeal_eq_ker (N : ℕ) : baseIdeal N = RingHom.ker (baseEval N) :=
  Ideal.ext fun f => by rw [mem_baseIdeal_iff, RingHom.mem_ker]

/-- **Lemma 2.1** (the identification `A₀ = L_N/J₀`): the first isomorphism theorem
for `baseEval`, whose kernel is `J₀` and which is onto. -/
noncomputable def baseQuotEquiv (N : ℕ) : (Laurent N ⧸ baseIdeal N) ≃ₐ[ℚ] BaseAlgebra N :=
  (Ideal.quotientEquivAlgOfEq ℚ (baseIdeal_eq_ker N)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (baseEval_surjective N))

/-- `baseQuotEquiv` sends the residue class of `f` to its normal form `baseEval f`. -/
@[simp] theorem baseQuotEquiv_mk (f : Laurent N) :
    baseQuotEquiv N (Ideal.Quotient.mk (baseIdeal N) f) = baseEval N f := rfl

/-- **Lemma 2.1** (dimension): `dim_ℚ (L_N ⧸ J₀) = N + 5`. -/
theorem finrank_quotient_baseIdeal (N : ℕ) :
    Module.finrank ℚ (Laurent N ⧸ baseIdeal N) = N + 5 :=
  (baseQuotEquiv N).toLinearEquiv.finrank_eq.trans (finrank_baseAlgebra N)

/-- **Lemma 2.1** (basis of `L_N ⧸ J₀`): the `ℚ`-basis of `A₀ = L_N ⧸ J₀` whose vectors
are the images of the monomials `1, B, B², B³, B⁴` (`quotBasis_inl`) and `C₁, …, C_N`
(`quotBasis_inr`), `B = S − T`, `Cᵢ = Dᵢ − 1`: the basis `baseBasis` of the coordinate
model transported along `baseQuotEquiv`. -/
noncomputable def quotBasis (N : ℕ) :
    Module.Basis (Fin 5 ⊕ Fin N) ℚ (Laurent N ⧸ baseIdeal N) :=
  (baseBasis N).map (baseQuotEquiv N).symm.toLinearEquiv

/-- The basis vectors `inl k` of `L_N ⧸ J₀` are the images of `(S − T)^k`, `k = 0, …, 4`. -/
theorem quotBasis_inl (k : Fin 5) :
    quotBasis N (Sum.inl k) = Ideal.Quotient.mk (baseIdeal N) ((S N - T N) ^ (k : ℕ)) := by
  apply (baseQuotEquiv N).injective
  rw [quotBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_symm, baseQuotEquiv_mk, map_pow,
    baseEval_S_sub_T, ← baseBasis_inl]
  exact (baseQuotEquiv N).apply_symm_apply _

/-- The basis vectors `inr i` of `L_N ⧸ J₀` are the images of `Dᵢ − 1`. -/
theorem quotBasis_inr (i : Fin N) :
    quotBasis N (Sum.inr i) = Ideal.Quotient.mk (baseIdeal N) (D i - 1) := by
  apply (baseQuotEquiv N).injective
  rw [quotBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_symm, baseQuotEquiv_mk,
    baseEval_D_sub_one, ← baseBasis_inr]
  exact (baseQuotEquiv N).apply_symm_apply _

/-! ### `J₀` has Krull dimension zero -/

instance : Module.Finite ℚ (Laurent N ⧸ baseIdeal N) :=
  Module.Finite.equiv (baseQuotEquiv N).symm.toLinearEquiv

/-- A finite-dimensional algebra over a field is Artinian. -/
instance : IsArtinianRing (Laurent N ⧸ baseIdeal N) :=
  IsArtinianRing.of_finite ℚ _

/-- Every prime ideal of `L_N ⧸ J₀` is maximal (an Artinian ring has Krull dimension
`≤ 0`). -/
theorem krullDimLE_zero_quotient_baseIdeal (N : ℕ) :
    Ring.KrullDimLE 0 (Laurent N ⧸ baseIdeal N) :=
  (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp inferInstance).2

/-- **Lemma 2.1** ("`J₀` has Krull dimension zero"): `ringKrullDim (L_N ⧸ J₀) = 0`.
The quotient is a nontrivial (`baseIdeal_ne_top`) finite-dimensional `ℚ`-algebra, hence
Artinian, hence of Krull dimension zero. -/
theorem ringKrullDim_quotient_baseIdeal (N : ℕ) :
    ringKrullDim (Laurent N ⧸ baseIdeal N) = 0 := by
  haveI : Nontrivial (Laurent N ⧸ baseIdeal N) :=
    Ideal.Quotient.nontrivial_iff.mpr (baseIdeal_ne_top (N := N))
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (krullDimLE_zero_quotient_baseIdeal N)

end Trinomial
