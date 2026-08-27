import Trinomial.Encoding.PolynomialTrinomials
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# `I_P` is primary to `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩` and zero-dimensional

[Theorem 4.5, first bullet "`I_P` has Krull dimension zero"; Corollary 5.1:
"each `I_e` is primary to the maximal ideal `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`"].

The proof follows the proof of Corollary 5.1: `I_P` is the kernel of the unital
homomorphism

  `ψ : ℚ[S,T,D] → A₀ × ∏ᵢ A_{Qᵢ}`,   `S ↦ (S, φ_{Q₁}(S), …, φ_{Q_M}(S))`, etc.,

because `f ∈ I_P` iff `f ∈ J₀ = ker baseEval` and `f ∈ ker φ_{Qᵢ}` for all `i`.  Each target
factor is local and its residue map evaluates the variables at
`(S, T, D₁, …, D_N) = (½, ½, 1, …, 1)`; the kernel of that evaluation is `𝔪`.  The generators
of `𝔪` map to `B`, `−B`, `Cᵢ` in `A₀` and to `Exp(v₀) − 1`, `Exp(−v₀) − 1`, `Exp(vᵢ) − 1`
in `A_Q`, all of which have vanishing residue, and a product of five elements of vanishing residue
is zero in every factor (`B⁵ = B·Cᵢ = Cᵢ·Cⱼ = 0` in `A₀`, `n³ = 0` in `A_Q`).  Hence

* `pointIdeal N` — the maximal ideal `𝔪`;
* `pointIdeal_pow_five_le` — `𝔪⁵ ⊆ I_P`;
* `polyReductionIdeal_le_pointIdeal` — `I_P ⊆ 𝔪`;
* `radical_polyReductionIdeal` — `√I_P = 𝔪`, so `I_P` is `𝔪`-primary
  (`polyReductionIdeal_isPrimary`) and proper (`polyReductionIdeal_ne_top`, from
  `Trinomial/Encoding/PolynomialTrinomials.lean`);
* `krullDimLE_zero_quotient`, `ringKrullDim_quotient` — `ℚ[S,T,D]/I_P` has Krull
  dimension zero: every prime containing `I_P` contains `𝔪⁵`, hence `𝔪`, hence equals `𝔪`.
-/

set_option autoImplicit false

namespace Trinomial

open MvPolynomial

variable {N M : ℕ}

/-! ### The maximal ideal `𝔪` and the evaluation at `(½, ½, 1, …, 1)` -/

/-- The maximal ideal `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩ ⊆ ℚ[S, T, D₁, …, D_N]`
[Corollary 5.1].  It is the radical of `J₀ ∩ ℚ[S,T,D]` and of every `I_P`
(`radical_polyReductionIdeal`). -/
noncomputable def pointIdeal (N : ℕ) : Ideal (MvPolynomial (Var N) ℚ) :=
  Ideal.span ({C 2 * X Var.S - 1, C 2 * X Var.T - 1}
    ∪ Set.range fun i : Fin N => X (Var.D i) - 1)

/-- The point `(S, T, D₁, …, D_N) = (½, ½, 1, …, 1)` at which the residue maps of the target
factors evaluate the variables [proof of Corollary 5.1]. -/
def basePoint (N : ℕ) : Var N → ℚ
  | Var.S => 1 / 2
  | Var.T => 1 / 2
  | Var.D _ => 1

/-- Taylor expansion at a point: every polynomial is congruent to its value modulo
`⟨X_v − a_v : v⟩`. -/
theorem sub_C_eval_mem_span {σ R : Type*} [CommRing R] (a : σ → R) (p : MvPolynomial σ R) :
    p - C (eval a p) ∈ Ideal.span (Set.range fun v => X v - C (a v)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
      have h := Ideal.add_mem _ hp hq
      convert h using 1
      rw [map_add, map_add]
      ring
  | mul_X p v hp =>
      have h1 : p * (X v - C (a v)) ∈ Ideal.span (Set.range fun v => X v - C (a v)) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨v, rfl⟩)
      have h2 := Ideal.mul_mem_right (C (a v)) _ hp
      convert Ideal.add_mem _ h1 h2 using 1
      rw [map_mul, eval_X, map_mul]
      ring

/-- The kernel of the evaluation at a point `a` is the ideal `⟨X_v − a_v : v⟩`. -/
theorem ker_eval_eq_span_X_sub_C {σ R : Type*} [CommRing R] (a : σ → R) :
    RingHom.ker (eval a) = Ideal.span (Set.range fun v => X v - C (a v)) := by
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have h := sub_C_eval_mem_span a p
    rwa [hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨v, rfl⟩
    simp [RingHom.mem_ker]

/-- `𝔪 = ⟨S − ½, T − ½, D₁ − 1, …, D_N − 1⟩`: the paper's generators and the generators
`X_v − a_v` at the point `a = (½, ½, 1, …, 1)` differ by the unit `2`. -/
theorem pointIdeal_eq_span_X_sub_C :
    pointIdeal N = Ideal.span (Set.range fun v => X v - C (basePoint N v)) := by
  have h2 : (C (1 / 2 : ℚ) * C 2 : MvPolynomial (Var N) ℚ) = 1 := by
    rw [← C_mul]
    norm_num
  apply le_antisymm
  · rw [pointIdeal, Ideal.span_le]
    rintro _ ((rfl | rfl) | ⟨i, rfl⟩)
    · have : (C 2 * X Var.S - 1 : MvPolynomial (Var N) ℚ)
          = C 2 * (X Var.S - C (basePoint N Var.S)) := by
        simp only [basePoint]
        linear_combination h2
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Var.S, rfl⟩)
    · have : (C 2 * X Var.T - 1 : MvPolynomial (Var N) ℚ)
          = C 2 * (X Var.T - C (basePoint N Var.T)) := by
        simp only [basePoint]
        linear_combination h2
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Var.T, rfl⟩)
    · exact Ideal.subset_span ⟨Var.D i, by simp [basePoint]⟩
  · rw [Ideal.span_le]
    rintro _ ⟨v, rfl⟩
    cases v with
    | S =>
        show X Var.S - C (basePoint N Var.S) ∈ pointIdeal N
        have : (X Var.S - C (basePoint N Var.S) : MvPolynomial (Var N) ℚ)
            = C (1 / 2) * (C 2 * X Var.S - 1) := by
          simp only [basePoint]
          linear_combination (-(X Var.S)) * h2
        rw [this]
        exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_union_left _ (Set.mem_insert _ _)))
    | T =>
        show X Var.T - C (basePoint N Var.T) ∈ pointIdeal N
        have : (X Var.T - C (basePoint N Var.T) : MvPolynomial (Var N) ℚ)
            = C (1 / 2) * (C 2 * X Var.T - 1) := by
          simp only [basePoint]
          linear_combination (-(X Var.T)) * h2
        rw [this]
        exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl)))
    | D i =>
        show X (Var.D i) - C (basePoint N (Var.D i)) ∈ pointIdeal N
        rw [show (X (Var.D i) - C (basePoint N (Var.D i)) : MvPolynomial (Var N) ℚ)
          = X (Var.D i) - 1 by simp [basePoint]]
        exact Ideal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩)

/-- `𝔪` is the kernel of the evaluation at `(½, ½, 1, …, 1)`. -/
theorem pointIdeal_eq_ker_eval : pointIdeal N = RingHom.ker (eval (basePoint N)) := by
  rw [pointIdeal_eq_span_X_sub_C, ker_eval_eq_span_X_sub_C]

/-- `𝔪` is a maximal ideal [Corollary 5.1]. -/
theorem pointIdeal_isMaximal (N : ℕ) : (pointIdeal N).IsMaximal := by
  rw [pointIdeal_eq_ker_eval]
  exact RingHom.ker_isMaximal_of_surjective _ fun r => ⟨C r, eval_C r⟩

/-! ### The evaluation `ψ : ℚ[S,T,D] → A₀ × ∏ᵢ A_{Qᵢ}` and its kernel `I_P` -/

/-- The unital homomorphism `ψ : ℚ[S,T,D] → A₀ × ∏ᵢ A_{Qᵢ}`,
`S ↦ (S, φ_{Q₁}(S), …, φ_{Q_M}(S))`, etc. [proof of Corollary 5.1].  Its kernel
is `I_P` (`polyReductionIdeal_eq_ker_psi`). -/
noncomputable def psi (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    MvPolynomial (Var N) ℚ →ₐ[ℚ] BaseAlgebra N × (∀ i, CubeAlgebra (Q i)) :=
  AlgHom.prod ((baseEval N).comp (toLaurent N))
    (Pi.algHom ℚ _ fun i => (phi (Q i)).comp (toLaurent N))

theorem psi_apply (Q : Fin M → BilinearFormMatrix (Option (Fin N))) (p : MvPolynomial (Var N) ℚ) :
    psi Q p = (baseEval N (toLaurent N p), fun i => phi (Q i) (toLaurent N p)) := rfl

/-- `I_P = ker ψ`: `f ∈ I_P` iff `f ∈ J₀` and `f ∈ ker φ_{Qᵢ}` for all `i`
[proof of Corollary 5.1]. -/
theorem polyReductionIdeal_eq_ker_psi (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    polyReductionIdeal Q = RingHom.ker (psi Q) := by
  ext p
  rw [mem_polyReductionIdeal_iff, mem_reductionIdeal_iff, mem_baseIdeal_iff, RingHom.mem_ker,
    psi_apply, Prod.ext_iff]
  simp only [RingHom.mem_ker, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.zero_apply]

theorem toLaurent_X_S : toLaurent N (X Var.S) = S N := by
  have h : (X Var.S : MvPolynomial (Var N) ℚ)
      = AddMonoidAlgebra.single (Finsupp.single Var.S 1) 1 := rfl
  rw [h, toLaurent_single, S, mono]
  congr 1
  ext <;> simp [expEmb, Exponent.gS]

theorem toLaurent_X_T : toLaurent N (X Var.T) = T N := by
  have h : (X Var.T : MvPolynomial (Var N) ℚ)
      = AddMonoidAlgebra.single (Finsupp.single Var.T 1) 1 := rfl
  rw [h, toLaurent_single, T, mono]
  congr 1
  ext <;> simp [expEmb, Exponent.gT]

theorem toLaurent_X_D (i : Fin N) : toLaurent N (X (Var.D i)) = D i := by
  have h : (X (Var.D i) : MvPolynomial (Var N) ℚ)
      = AddMonoidAlgebra.single (Finsupp.single (Var.D i) 1) 1 := rfl
  rw [h, toLaurent_single, D, mono]
  congr 1
  ext
  · simp [expEmb, Exponent.gD]
  · simp [expEmb, Exponent.gD]
  · simp [expEmb, Exponent.gD, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-! ### The residue maps of the target factors -/

/-- The residue map `A₀ → ℚ`, `x ↦ b₀(x)` (the coefficient of `1`); its kernel is the maximal
ideal `⟨B, C₁, …, C_N⟩` of `A₀` [proof of Corollary 5.1: "each target factor
is local"]. -/
def BaseAlgebra.residue (N : ℕ) : BaseAlgebra N →+* ℚ where
  toFun := BaseAlgebra.b0
  map_one' := rfl
  map_mul' := BaseAlgebra.mul_b0
  map_zero' := rfl
  map_add' := BaseAlgebra.add_b0

/-- The residue map `A_Q → ℚ` onto the scalar coordinate; its kernel is the nilradical
`n = V ⊕ ℚζ` of `A_Q` [Lemma 3.2]. -/
def CubeAlgebra.residue {ι : Type*} [Fintype ι] (B : BilinearFormMatrix ι) :
    CubeAlgebra B →+* ℚ where
  toFun := CubeAlgebra.scalar
  map_one' := rfl
  map_mul' := CubeAlgebra.mul_scalar
  map_zero' := rfl
  map_add' := CubeAlgebra.add_scalar

/-- The residue map of the target, `A₀ × ∏ᵢ A_{Qᵢ} → ℚ × ℚ^M`. -/
def targetResidue (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    BaseAlgebra N × (∀ i, CubeAlgebra (Q i)) →+* ℚ × (Fin M → ℚ) :=
  RingHom.prodMap (BaseAlgebra.residue N)
    (Pi.ringHom fun i => (CubeAlgebra.residue (Q i)).comp (Pi.evalRingHom _ i))

theorem targetResidue_apply (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (y : BaseAlgebra N × (∀ i, CubeAlgebra (Q i))) :
    targetResidue Q y = (y.1.b0, fun i => (y.2 i).scalar) := rfl

theorem mem_ker_targetResidue_iff (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (y : BaseAlgebra N × (∀ i, CubeAlgebra (Q i))) :
    y ∈ RingHom.ker (targetResidue Q) ↔ y.1.b0 = 0 ∧ ∀ i, (y.2 i).scalar = 0 := by
  rw [RingHom.mem_ker, targetResidue_apply, Prod.ext_iff]
  simp [funext_iff]

/-- The residue maps of the target factors evaluate the variables at
`(S, T, D₁, …, D_N) = (½, ½, 1, …, 1)` [proof of Corollary 5.1]. -/
theorem targetResidue_comp_psi (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    (targetResidue Q).comp (psi Q : MvPolynomial (Var N) ℚ →+* _)
      = RingHom.prod (eval (basePoint N)) (Pi.ringHom fun _ => eval (basePoint N)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    ext <;> simp [targetResidue_apply, algHom_C, Prod.algebraMap_apply]
  · intro v
    cases v with
    | S =>
        ext <;> simp [targetResidue_apply, psi_apply, toLaurent_X_S, BaseAlgebra.baseEval_S,
          phi_S, basePoint]
    | T =>
        ext <;> simp [targetResidue_apply, psi_apply, toLaurent_X_T, BaseAlgebra.baseEval_T,
          phi_T, basePoint]
    | D i =>
        ext <;> simp [targetResidue_apply, psi_apply, toLaurent_X_D, BaseAlgebra.baseEval_D,
          phi_D, basePoint]

theorem targetResidue_psi (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (p : MvPolynomial (Var N) ℚ) :
    targetResidue Q (psi Q p) = (eval (basePoint N) p, fun _ => eval (basePoint N) p) :=
  RingHom.congr_fun (targetResidue_comp_psi Q) p

/-- **`I_P ⊆ 𝔪`**: the composite of `ψ` with the residue map is the evaluation at
`(½, ½, 1, …, 1)`, whose kernel is `𝔪` [proof of Corollary 5.1]. -/
theorem polyReductionIdeal_le_pointIdeal (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    polyReductionIdeal Q ≤ pointIdeal N := by
  intro p hp
  rw [polyReductionIdeal_eq_ker_psi, RingHom.mem_ker] at hp
  rw [pointIdeal_eq_ker_eval, RingHom.mem_ker]
  have h := targetResidue_psi Q p
  rw [hp, map_zero] at h
  exact (congrArg Prod.fst h).symm

/-! ### `𝔪⁵ ⊆ I_P` -/

/-- The image under `ψ` of an element of `𝔪` has vanishing residues, i.e. lies in
`⟨B, C₁, …, C_N⟩ × ∏ᵢ nᵢ` [proof of Corollary 5.1]. -/
theorem psi_mem_ker_targetResidue (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    {p : MvPolynomial (Var N) ℚ} (hp : p ∈ pointIdeal N) :
    psi Q p ∈ RingHom.ker (targetResidue Q) := by
  rw [pointIdeal_eq_ker_eval, RingHom.mem_ker] at hp
  rw [RingHom.mem_ker, targetResidue_psi, hp]
  rfl

/-- In `A₀` a product of five elements of the maximal ideal `⟨B, C₁, …, C_N⟩` vanishes
(`B⁵ = 0`, `B·Cᵢ = 0`, `Cᵢ·Cⱼ = 0`) [Lemma 2.1]. -/
theorem BaseAlgebra.mul_five_eq_zero {x₁ x₂ x₃ x₄ x₅ : BaseAlgebra N} (h₁ : x₁.b0 = 0)
    (h₂ : x₂.b0 = 0) (h₃ : x₃.b0 = 0) (h₄ : x₄.b0 = 0) (h₅ : x₅.b0 = 0) :
    x₁ * x₂ * x₃ * x₄ * x₅ = 0 := by
  ext <;> simp [h₁, h₂, h₃, h₄, h₅]

/-- In `A_Q` a product of five (indeed three) elements of the nilradical `n` vanishes
[Lemma 3.2]. -/
theorem CubeAlgebra.mul_five_eq_zero {ι : Type*} [Fintype ι] {B : BilinearFormMatrix ι}
    {x₁ x₂ x₃ x₄ x₅ : CubeAlgebra B} (h₁ : x₁.scalar = 0) (h₂ : x₂.scalar = 0)
    (h₃ : x₃.scalar = 0) : x₁ * x₂ * x₃ * x₄ * x₅ = 0 := by
  rw [CubeAlgebra.cube_zero x₁ x₂ x₃ h₁ h₂ h₃, zero_mul, zero_mul]

/-- A product of five elements of `⟨B, C₁, …, C_N⟩ × ∏ᵢ nᵢ` vanishes. -/
theorem mul_five_eq_zero_of_mem_ker_targetResidue
    (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    {y₁ y₂ y₃ y₄ y₅ : BaseAlgebra N × (∀ i, CubeAlgebra (Q i))}
    (h₁ : y₁ ∈ RingHom.ker (targetResidue Q)) (h₂ : y₂ ∈ RingHom.ker (targetResidue Q))
    (h₃ : y₃ ∈ RingHom.ker (targetResidue Q)) (h₄ : y₄ ∈ RingHom.ker (targetResidue Q))
    (h₅ : y₅ ∈ RingHom.ker (targetResidue Q)) :
    y₁ * y₂ * y₃ * y₄ * y₅ = 0 := by
  rw [mem_ker_targetResidue_iff] at h₁ h₂ h₃ h₄ h₅
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Prod.fst_mul, Prod.fst_zero]
    exact BaseAlgebra.mul_five_eq_zero h₁.1 h₂.1 h₃.1 h₄.1 h₅.1
  · simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply]
    exact CubeAlgebra.mul_five_eq_zero (h₁.2 i) (h₂.2 i) (h₃.2 i)

/-- **`𝔪⁵ ⊆ I_P`** [proof of Corollary 5.1: the image of `ψ` is a local
Artinian algebra with nilpotent maximal ideal].  Every product
of five generators of `𝔪` maps to `0` in every factor of `A₀ × ∏ᵢ A_{Qᵢ}`. -/
theorem pointIdeal_pow_five_le (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    pointIdeal N ^ 5 ≤ polyReductionIdeal Q := by
  rw [polyReductionIdeal_eq_ker_psi, pointIdeal, Ideal.span, Submodule.span_pow,
    Submodule.span_le]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hx
  rw [List.prod_ofFn, Fin.prod_univ_five, SetLike.mem_coe, RingHom.mem_ker, map_mul, map_mul,
    map_mul, map_mul]
  exact mul_five_eq_zero_of_mem_ker_targetResidue Q
    (psi_mem_ker_targetResidue Q (Ideal.subset_span (f 0).2))
    (psi_mem_ker_targetResidue Q (Ideal.subset_span (f 1).2))
    (psi_mem_ker_targetResidue Q (Ideal.subset_span (f 2).2))
    (psi_mem_ker_targetResidue Q (Ideal.subset_span (f 3).2))
    (psi_mem_ker_targetResidue Q (Ideal.subset_span (f 4).2))

/-! ### `I_P` is `𝔪`-primary and zero-dimensional -/

/-- `√I_P = 𝔪` [Corollary 5.1]. -/
theorem radical_polyReductionIdeal (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    (polyReductionIdeal Q).radical = pointIdeal N := by
  apply le_antisymm
  · exact (pointIdeal_isMaximal N).isPrime.radical_le_iff.mpr
      (polyReductionIdeal_le_pointIdeal Q)
  · intro p hp
    exact ⟨5, pointIdeal_pow_five_le Q (Ideal.pow_mem_pow hp 5)⟩

/-- **`I_P` is `𝔪`-primary** [Corollary 5.1]. -/
theorem polyReductionIdeal_isPrimary (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    (polyReductionIdeal Q).IsPrimary :=
  Ideal.isPrimary_of_isMaximal_radical
    (by rw [radical_polyReductionIdeal]; exact pointIdeal_isMaximal N)

/-- **`I_P` has Krull dimension zero** [Theorem 4.5, first bullet]: every prime
ideal of `ℚ[S,T,D]/I_P` is maximal, because a prime containing `I_P ⊇ 𝔪⁵` contains `𝔪`. -/
theorem krullDimLE_zero_quotient (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Ring.KrullDimLE 0 (MvPolynomial (Var N) ℚ ⧸ polyReductionIdeal Q) := by
  refine Ring.KrullDimLE.mk₀ fun P hP => ?_
  haveI := hP
  have hle : polyReductionIdeal Q ≤ P.comap (Ideal.Quotient.mk (polyReductionIdeal Q)) :=
    fun f hf => by
      have h0 : Ideal.Quotient.mk (polyReductionIdeal Q) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hf
      rw [Ideal.mem_comap, h0]
      exact P.zero_mem
  have hm : pointIdeal N ≤ P.comap (Ideal.Quotient.mk (polyReductionIdeal Q)) :=
    (Ideal.IsPrime.pow_le_iff (by norm_num)).mp ((pointIdeal_pow_five_le Q).trans hle)
  have heq : pointIdeal N = P.comap (Ideal.Quotient.mk (polyReductionIdeal Q)) :=
    (pointIdeal_isMaximal N).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hm
  have hmap : P = Ideal.map (Ideal.Quotient.mk (polyReductionIdeal Q)) (pointIdeal N) := by
    rw [heq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (polyReductionIdeal Q))
    Ideal.Quotient.mk_surjective (pointIdeal_isMaximal N) with h | h
  · exact absurd (hmap.trans h) hP.ne_top
  · rw [hmap]
    exact h

/-- **`ringKrullDim (ℚ[S,T,D]/I_P) = 0`** [Theorem 4.5, first bullet]. -/
theorem ringKrullDim_quotient (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    ringKrullDim (MvPolynomial (Var N) ℚ ⧸ polyReductionIdeal Q) = 0 := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr (polyReductionIdeal_ne_top Q)
  apply le_antisymm
  · have h := krullDimLE_zero_quotient Q
    rw [Ring.krullDimLE_iff] at h
    simpa using h
  · exact ringKrullDim_nonneg_of_nontrivial

end Trinomial
