import Trinomial.Encoding.ZeroDimensional
import Trinomial.Base.BaseAlgebraBasis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The colength bound `(N+5) + M(N+3)`

[Corollary 5.1: "`dim_ℚ(ℚ[S, T, D₁, …, D_N] / I_e) ≤ C`", with
`C := (N+5) + M(N+3)`; proof of Theorem 4.5].

The proof of the corollary reads: "`I_e` is the kernel of the unital homomorphism
`ℚ[S, T, D₁, …, D_N] → A₀ × ∏ᵢ A_{Qᵢ}` which sends each variable to the tuple of its images.
The codomain has dimension `C := (N+5) + M(N+3)`, by Lemma 2.1 and because
`A_{Qᵢ} = ℚ × V × ℚ` with `dim_ℚ V = N+1`.  The quotient by `I_e` embeds into the codomain,
so its dimension is at most `C`."  This module formalizes exactly that, for every ideal `I_P`
of Theorem 4.5 (`Trinomial/Encoding/ZeroDimensional.lean` proves `I_P = ker ψ`):

* `cubeCoordEquiv`, `finrank_cubeAlgebra` — `A_Q = ℚ ⊕ V ⊕ ℚζ ≃ ℚ × V × ℚ` as
  `ℚ`-vector spaces, so `dim_ℚ A_Q = N + 3` for `V = ℚ^{N+1}`;
* `finrank_target` — `dim_ℚ (A₀ × ∏ᵢ A_{Qᵢ}) = (N+5) + M(N+3)`, the paper's `C`;
* `quotientEmbedding`, `quotientEmbedding_injective` — the embedding
  `ℚ[S,T,D]/I_P ↪ A₀ × ∏ᵢ A_{Qᵢ}` induced by `ψ`;
* `finrank_quotient_le` — the colength bound `dim_ℚ (ℚ[S,T,D]/I_P) ≤ (N+5) + M(N+3)`.

The instance for the family `I_e` of Corollary 5.1 (`finrank_haltingIdeal_le`,
with `N₀`, `M₀` independent of `e`) is in `Trinomial/Universal/HaltingFamily.lean`.
-/

set_option autoImplicit false

namespace Trinomial

open MvPolynomial

variable {N M : ℕ}

/-! ### `dim_ℚ A_Q = N + 3` -/

section CubeAlgebra

variable {ι : Type*} [Fintype ι]

/-- The `ℚ`-linear isomorphism `A_Q = ℚ ⊕ V ⊕ ℚζ ≃ ℚ × V × ℚ`,
`x ↦ (scalar, vector, socle)` [§3; proof of Corollary 5.1:
"`A_{Qᵢ} = ℚ × V × ℚ`"]. -/
def cubeCoordEquiv (B : BilinearFormMatrix ι) : CubeAlgebra B ≃ₗ[ℚ] (ℚ × (ι → ℚ) × ℚ) where
  toFun x := (x.scalar, x.vector, x.socle)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  map_add' _ _ := rfl
  map_smul' c x := by ext <;> simp
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma cubeCoordEquiv_apply (B : BilinearFormMatrix ι) (x : CubeAlgebra B) :
    cubeCoordEquiv B x = (x.scalar, x.vector, x.socle) := rfl

@[simp] lemma cubeCoordEquiv_symm_apply (B : BilinearFormMatrix ι) (p : ℚ × (ι → ℚ) × ℚ) :
    (cubeCoordEquiv B).symm p = ⟨p.1, p.2.1, p.2.2⟩ := rfl

instance (B : BilinearFormMatrix ι) : Module.Finite ℚ (CubeAlgebra B) :=
  Module.Finite.equiv (cubeCoordEquiv B).symm

/-- `dim_ℚ A_Q = 1 + dim_ℚ V + 1` for `V = ℚ^ι` [Lemma 3.2]. -/
theorem finrank_cubeAlgebra_eq_card_add_two (B : BilinearFormMatrix ι) :
    Module.finrank ℚ (CubeAlgebra B) = Fintype.card ι + 2 := by
  rw [(cubeCoordEquiv B).finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, Module.finrank_pi]
  omega

end CubeAlgebra

/-- `dim_ℚ A_Q = N + 3` for the forms of Theorem 4.5, whose space `V = ℚ^{N+1}` has the
coordinates `v₀, v₁, …, v_N` (index type `Option (Fin N)`) [proof of
Corollary 5.1: "`A_{Qᵢ} = ℚ × V × ℚ` with `dim_ℚ V = N+1`"]. -/
theorem finrank_cubeAlgebra (B : BilinearFormMatrix (Option (Fin N))) :
    Module.finrank ℚ (CubeAlgebra B) = N + 3 := by
  rw [finrank_cubeAlgebra_eq_card_add_two, Fintype.card_option, Fintype.card_fin]

/-! ### The dimension of the algebra `A₀ × ∏ᵢ A_{Qᵢ}` -/

/-- **The paper's constant `C`**: `dim_ℚ (A₀ × ∏ᵢ A_{Qᵢ}) = (N+5) + M(N+3)`
[proof of Corollary 5.1: "The codomain has dimension `C := (N+5) + M(N+3)`,
by Lemma 2.1 and because `A_{Qᵢ} = ℚ × V × ℚ` with `dim_ℚ V = N+1`"]. -/
theorem finrank_target (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Module.finrank ℚ (BaseAlgebra N × (∀ i, CubeAlgebra (Q i))) = (N + 5) + M * (N + 3) := by
  rw [Module.finrank_prod, finrank_baseAlgebra, Module.finrank_pi_fintype]
  simp only [finrank_cubeAlgebra, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-! ### The embedding `ℚ[S,T,D]/I_P ↪ A₀ × ∏ᵢ A_{Qᵢ}` -/

/-- The unital homomorphism `ℚ[S,T,D]/I_P → A₀ × ∏ᵢ A_{Qᵢ}` induced by `ψ` on the quotient
by its kernel `I_P` (`polyReductionIdeal_eq_ker_psi`) [proof of
Corollary 5.1: "The quotient by `I_e` embeds into the codomain"]. -/
noncomputable def quotientEmbedding (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    (MvPolynomial (Var N) ℚ ⧸ polyReductionIdeal Q) →ₐ[ℚ]
      BaseAlgebra N × (∀ i, CubeAlgebra (Q i)) :=
  Ideal.Quotient.liftₐ (polyReductionIdeal Q) (psi Q) fun _ ha => by
    rwa [polyReductionIdeal_eq_ker_psi, RingHom.mem_ker] at ha

@[simp] theorem quotientEmbedding_mk (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (p : MvPolynomial (Var N) ℚ) :
    quotientEmbedding Q (Ideal.Quotient.mk (polyReductionIdeal Q) p) = psi Q p := rfl

/-- The induced map is injective, because `I_P` is the whole kernel of `ψ`. -/
theorem quotientEmbedding_injective (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Function.Injective (quotientEmbedding Q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientEmbedding_mk] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, polyReductionIdeal_eq_ker_psi, RingHom.mem_ker]
  exact hx

/-- `ℚ[S,T,D]/I_P` is a finite-dimensional `ℚ`-vector space: it embeds into
`A₀ × ∏ᵢ A_{Qᵢ}`. -/
instance (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Module.Finite ℚ (MvPolynomial (Var N) ℚ ⧸ polyReductionIdeal Q) :=
  Module.Finite.of_injective (quotientEmbedding Q).toLinearMap (quotientEmbedding_injective Q)

/-- **The colength bound** `dim_ℚ (ℚ[S,T,D]/I_P) ≤ (N+5) + M(N+3)` for every ideal `I_P` of
Theorem 4.5 [proof of Corollary 5.1: "The quotient by `I_e` embeds into the
codomain, so its dimension is at most `C`"]. -/
theorem finrank_quotient_le (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Module.finrank ℚ (MvPolynomial (Var N) ℚ ⧸ polyReductionIdeal Q) ≤ (N + 5) + M * (N + 3) :=
  (LinearMap.finrank_le_finrank_of_injective (f := (quotientEmbedding Q).toLinearMap)
    (quotientEmbedding_injective Q)).trans_eq (finrank_target Q)

end Trinomial
