import Trinomial.Quadrics.QuadraticAlgebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Structure of the cube-zero algebra `A_B`: nilradical, locality, `Exp` and `Log`

This module proves the structure statements of [Lemma 3.2 and Remark 3.3] for
the algebra `A_B = ℚ ⊕ V ⊕ ℚζ` of `Trinomial/Quadrics/QuadraticAlgebra.lean`:

* the scalar projection `A_B → ℚ` is a ring homomorphism (`scalarHom`) whose kernel is
  `𝔫 = V ⊕ ℚζ` (`nilideal`, `mem_nilideal_iff`);
* `𝔫³ = 0` (`nilideal_pow_three`): `A_B` is a "radical cube zero" ring [Remark 3.3];
* `𝔫` is the nilradical (`isNilpotent_iff`, `nilradical_eq`);
* `A_B` is local with maximal ideal `𝔫` (`isUnit_iff`, the `IsLocalRing` instance,
  `maximalIdeal_eq`);
* the truncated exponential `Exp(x) = 1 + x + ½x²` on the whole nilradical (`expNil`), its
  inverse `Log(1 + u) = u − ½u²` (`logNil`), the exponential law `expNil_add`, the two
  inversion laws `logNil_expNil`, `expNil_logNil`, the consistency `expNil_ofVector` with the
  restricted `Exp(v) = 1 + v + ½Q(v)ζ` of `QuadraticAlgebra.lean`, and the packaged group
  isomorphism `expEquiv : 𝔫 ≃ 1 + 𝔫` from the additive group `𝔫` onto the multiplicative
  group `1 + 𝔫` [paragraph after Remark 3.3, citing Lenstra–Silverberg, Prop. 8.1].

Paper correspondence:

* `𝔫 = V ⊕ ℚζ`                            ↦ `CubeAlgebra.nilideal B`
* "local with nilradical `𝔫`"               ↦ `nilradical_eq`, `maximalIdeal_eq`
* "`𝔫³ = 0`", "radical cube zero"           ↦ `nilideal_pow_three`
* `Exp`, `Log` on `𝔫`                       ↦ `expNil`, `logNil`
* "`Exp : 𝔫 → 1 + 𝔫` is a group isomorphism" ↦ `expEquiv`, with `onePlusNil B` the
                                              subgroup `1 + 𝔫` of the unit group

The presentation `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` of Lemma 3.2 is set up here (the algebra map
`presentation`, the relation ideal `relationIdeal`, `presentation_surjective`,
`relationIdeal_le_ker`) and completed in `Trinomial/Quadrics/CubeAlgebraPresentation.lean`
(`ker_presentation`, `presentationEquiv`).
-/

set_option autoImplicit false

namespace Trinomial

namespace CubeAlgebra

variable {ι : Type*} [Fintype ι] {B : BilinearFormMatrix ι}

/-! ### Coordinates of differences -/

@[simp] theorem sub_scalar (x y : CubeAlgebra B) : (x - y).scalar = x.scalar - y.scalar := by
  rw [sub_eq_add_neg, add_scalar, neg_scalar, sub_eq_add_neg]

@[simp] theorem sub_vector (x y : CubeAlgebra B) : (x - y).vector = x.vector - y.vector := by
  rw [sub_eq_add_neg, add_vector, neg_vector, sub_eq_add_neg]

@[simp] theorem sub_socle (x y : CubeAlgebra B) : (x - y).socle = x.socle - y.socle := by
  rw [sub_eq_add_neg, add_socle, neg_socle, sub_eq_add_neg]

/-! ### The nilradical `𝔫 = V ⊕ ℚζ` -/

/-- The projection `A_B → ℚ` onto the scalar coordinate, a ring homomorphism (the residue
map of the local ring `A_B`) [Lemma 3.2].  (`CubeAlgebra.residue` in
`Trinomial/Encoding/ZeroDimensional.lean` is the same map.) -/
def scalarHom (B : BilinearFormMatrix ι) : CubeAlgebra B →+* ℚ where
  toFun := scalar
  map_one' := rfl
  map_mul' := mul_scalar
  map_zero' := rfl
  map_add' := add_scalar

@[simp] theorem scalarHom_apply (x : CubeAlgebra B) : scalarHom B x = x.scalar := rfl

/-- The ideal `𝔫 = V ⊕ ℚζ` of `A_B`, the kernel of the scalar projection
[Lemma 3.2].  It is the nilradical (`nilradical_eq`) and the maximal ideal
(`maximalIdeal_eq`) of `A_B`. -/
def nilideal (B : BilinearFormMatrix ι) : Ideal (CubeAlgebra B) := RingHom.ker (scalarHom B)

theorem mem_nilideal_iff (x : CubeAlgebra B) : x ∈ nilideal B ↔ x.scalar = 0 := Iff.rfl

theorem ofVector_mem_nilideal (v : ι → ℚ) : ofVector B v ∈ nilideal B := rfl

theorem zeta_mem_nilideal : zeta B ∈ nilideal B := rfl

/-- `𝔫³ = 0`: `A_B` is a "radical cube zero" ring [Remark 3.3]. -/
theorem nilideal_pow_three : nilideal B ^ 3 = ⊥ := by
  rw [eq_bot_iff, pow_three', Ideal.mul_le]
  intro a ha z hz
  rw [Ideal.mem_bot]
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · exact cube_zero x y z hx hy hz
  · rw [add_mul, hx, hy, add_zero]

/-- The nilpotent elements of `A_B` are exactly those with vanishing scalar coordinate. -/
theorem isNilpotent_iff (x : CubeAlgebra B) : IsNilpotent x ↔ x.scalar = 0 := by
  constructor
  · intro hx
    simpa using isNilpotent_iff_eq_zero.1 (hx.map (scalarHom B))
  · intro hx
    exact ⟨3, by rw [pow_three']; exact cube_zero x x x hx hx hx⟩

/-- The nilradical of `A_B` is `𝔫 = V ⊕ ℚζ` [Lemma 3.2]. -/
theorem nilradical_eq : nilradical (CubeAlgebra B) = nilideal B :=
  Ideal.ext fun x => by rw [mem_nilradical, isNilpotent_iff, mem_nilideal_iff]

/-! ### `A_B` is local with maximal ideal `𝔫` -/

instance : Nontrivial (CubeAlgebra B) := ⟨⟨zeta B, 0, zeta_ne_zero⟩⟩

/-- The units of `A_B` are the elements with nonzero scalar coordinate: such an element is a
nonzero scalar times `1 + n` with `n ∈ 𝔫` nilpotent. -/
theorem isUnit_iff (x : CubeAlgebra B) : IsUnit x ↔ x.scalar ≠ 0 := by
  constructor
  · intro hx
    exact isUnit_iff_ne_zero.1 (hx.map (scalarHom B))
  · intro hx
    have hn : (x.scalar⁻¹ • x - 1).scalar = 0 := by simp [hx]
    have hx' : x = algebraMap ℚ (CubeAlgebra B) x.scalar * (1 + (x.scalar⁻¹ • x - 1)) := by
      rw [add_sub_cancel, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hx, one_smul]
    rw [hx']
    exact ((isUnit_iff_ne_zero.2 hx).map (algebraMap ℚ (CubeAlgebra B))).mul
      ((isNilpotent_iff _).2 hn).isUnit_one_add

/-- `A_B` is a local ring [Lemma 3.2]. -/
instance : IsLocalRing (CubeAlgebra B) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : a.scalar = 0
    · exact Or.inr ((isUnit_iff _).2 (by simp [h]))
    · exact Or.inl ((isUnit_iff _).2 h)

/-- The maximal ideal of the local ring `A_B` is `𝔫 = V ⊕ ℚζ` [Lemma 3.2]. -/
theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (CubeAlgebra B) = nilideal B :=
  Ideal.ext fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff, not_not, mem_nilideal_iff]

/-! ### The exponential and logarithm on the nilradical -/

/-- The truncated exponential `Exp(x) = 1 + x + ½x²` on the nilradical `𝔫` of `A_B`
[paragraph after Remark 3.3].  (Defined on all of `A_B`; the laws below assume
`x ∈ 𝔫`.) -/
def expNil (x : CubeAlgebra B) : CubeAlgebra B := 1 + x + (1 / 2 : ℚ) • (x * x)

/-- The truncated logarithm `Log(1 + u) = u − ½u²` on `1 + 𝔫`
[paragraph after Remark 3.3]. -/
def logNil (y : CubeAlgebra B) : CubeAlgebra B := (y - 1) - (1 / 2 : ℚ) • ((y - 1) * (y - 1))

/-- On `V ⊆ 𝔫` the exponential is the `Exp(v) = 1 + v + ½Q(v)ζ` of `QuadraticAlgebra.lean`
[paragraph after Remark 3.3]. -/
theorem expNil_ofVector (v : ι → ℚ) : expNil (ofVector B v) = exp B v := by
  ext <;> simp [expNil, BilinearFormMatrix.quad, div_eq_inv_mul]

@[simp] theorem expNil_zero : expNil (0 : CubeAlgebra B) = 1 := by
  ext <;> simp [expNil]

theorem expNil_scalar {x : CubeAlgebra B} (hx : x.scalar = 0) : (expNil x).scalar = 1 := by
  simp [expNil, hx]

/-- `Exp` maps `𝔫` into `1 + 𝔫`. -/
theorem expNil_mem {x : CubeAlgebra B} (hx : x.scalar = 0) : (expNil x - 1).scalar = 0 := by
  simp [expNil_scalar hx]

/-- `y ∈ 1 + 𝔫` means `y.scalar = 1`. -/
theorem sub_one_scalar_eq_zero_iff (y : CubeAlgebra B) : (y - 1).scalar = 0 ↔ y.scalar = 1 := by
  rw [sub_scalar, one_scalar, sub_eq_zero]

/-- `Log` maps `1 + 𝔫` into `𝔫`. -/
theorem logNil_scalar {y : CubeAlgebra B} (hy : (y - 1).scalar = 0) : (logNil y).scalar = 0 := by
  rw [sub_one_scalar_eq_zero_iff] at hy
  simp [logNil, hy]

/-- The exponential law `Exp(x + y) = Exp(x) Exp(y)` on `𝔫`
[paragraph after Remark 3.3]. -/
theorem expNil_add {x y : CubeAlgebra B} (hx : x.scalar = 0) (hy : y.scalar = 0) :
    expNil (x + y) = expNil x * expNil y := by
  ext
  · simp [expNil, hx, hy]
  · simp [expNil, hx, hy]
    ring
  · simp [expNil, hx, hy, B.polar_comm y.vector x.vector]
    ring

/-- `Log ∘ Exp = id` on `𝔫` [paragraph after Remark 3.3]. -/
theorem logNil_expNil {x : CubeAlgebra B} (hx : x.scalar = 0) : logNil (expNil x) = x := by
  ext <;> simp [logNil, expNil, hx]

/-- `Exp ∘ Log = id` on `1 + 𝔫` [paragraph after Remark 3.3]. -/
theorem expNil_logNil {y : CubeAlgebra B} (hy : (y - 1).scalar = 0) : expNil (logNil y) = y := by
  rw [sub_one_scalar_eq_zero_iff] at hy
  ext <;> simp [logNil, expNil, hy]

/-- `Exp(−x) = Exp(x)⁻¹` on `𝔫` [paragraph after Remark 3.3]. -/
theorem expNil_mul_expNil_neg {x : CubeAlgebra B} (hx : x.scalar = 0) :
    expNil x * expNil (-x) = 1 := by
  rw [← expNil_add hx (by simp [hx]), add_neg_cancel, expNil_zero]

/-- `Exp(x)` as a unit of `A_B`, for `x ∈ 𝔫`, with inverse `Exp(−x)`. -/
def expNilUnit (x : nilideal B) : (CubeAlgebra B)ˣ where
  val := expNil x
  inv := expNil (-x)
  val_inv := expNil_mul_expNil_neg x.2
  inv_val := by rw [mul_comm]; exact expNil_mul_expNil_neg x.2

@[simp] theorem expNilUnit_val (x : nilideal B) : (expNilUnit x : CubeAlgebra B) = expNil x := rfl

/-- The multiplicative group `1 + 𝔫` of units of `A_B` with scalar coordinate `1`
[paragraph after Remark 3.3]. -/
def onePlusNil (B : BilinearFormMatrix ι) : Subgroup (CubeAlgebra B)ˣ where
  carrier := {u | (u : CubeAlgebra B) - 1 ∈ nilideal B}
  one_mem' := by simp [mem_nilideal_iff]
  mul_mem' {u v} hu hv := by
    simp only [Set.mem_setOf_eq, mem_nilideal_iff, sub_scalar, one_scalar, sub_eq_zero] at hu hv ⊢
    simp [hu, hv]
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq, mem_nilideal_iff, sub_scalar, one_scalar, sub_eq_zero] at hu ⊢
    have := congrArg scalar u.inv_mul
    rwa [mul_scalar, hu, mul_one, one_scalar] at this

theorem mem_onePlusNil_iff (u : (CubeAlgebra B)ˣ) :
    u ∈ onePlusNil B ↔ (u : CubeAlgebra B).scalar = 1 := by
  change (u : CubeAlgebra B) - 1 ∈ nilideal B ↔ _
  rw [mem_nilideal_iff, sub_scalar, one_scalar, sub_eq_zero]

/-- `Exp : 𝔫 → 1 + 𝔫` is an isomorphism from the additive group `𝔫` onto the multiplicative
group `1 + 𝔫`, with inverse `Log` [paragraph after Remark 3.3, citing
Lenstra–Silverberg, Prop. 8.1]. -/
def expEquiv : Multiplicative (nilideal B) ≃* onePlusNil B where
  toFun x := ⟨expNilUnit x.toAdd, (mem_onePlusNil_iff _).2 (expNil_scalar x.toAdd.2)⟩
  invFun u := Multiplicative.ofAdd
    ⟨logNil u.1, (mem_nilideal_iff _).2 (logNil_scalar u.2)⟩
  left_inv x := Multiplicative.toAdd.injective (Subtype.ext (logNil_expNil x.toAdd.2))
  right_inv u := Subtype.ext (Units.ext (expNil_logNil u.2))
  map_mul' x y := Subtype.ext (Units.ext (expNil_add x.toAdd.2 y.toAdd.2))

@[simp] theorem expEquiv_apply (x : Multiplicative (nilideal B)) :
    ((expEquiv x : (CubeAlgebra B)ˣ) : CubeAlgebra B) = expNil (x.toAdd : CubeAlgebra B) := rfl

@[simp] theorem expEquiv_symm_apply (u : onePlusNil B) :
    ((expEquiv.symm u).toAdd : CubeAlgebra B) = logNil ((u : (CubeAlgebra B)ˣ) : CubeAlgebra B) :=
  rfl

/-! ### Towards the presentation `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` of Lemma 3.2

The algebra map `ℚ[X, Z] → A_B`, `Xᵢ ↦ vᵢ`, `Z ↦ ζ` is surjective and the relations
`XᵢXⱼ − b_ij Z`, `XᵢZ`, `Z²` lie in its kernel, so `A_B` is a quotient of `ℚ[X, Z]/I`.  The
reverse inclusion `ker ⊆ I`, hence the isomorphism, is proved in
`Trinomial/Quadrics/CubeAlgebraPresentation.lean`. -/

section Presentation

open MvPolynomial

variable [DecidableEq ι]

/-- The algebra map `ℚ[Xᵢ (i : ι), Z] → A_B`, `Xᵢ ↦ vᵢ`, `Z ↦ ζ` of Lemma 3.2, with the
variable `some i` playing `Xᵢ` and `none` playing `Z`. -/
noncomputable def presentation (B : BilinearFormMatrix ι) :
    MvPolynomial (Option ι) ℚ →ₐ[ℚ] CubeAlgebra B :=
  aeval fun o => o.elim (zeta B) fun i => ofVector B (Pi.single i 1)

@[simp] theorem presentation_X_some (i : ι) :
    presentation B (X (some i)) = ofVector B (Pi.single i 1) := by
  simp [presentation]

@[simp] theorem presentation_X_none : presentation B (X none) = zeta B := by
  simp [presentation]

@[simp] theorem presentation_C (c : ℚ) :
    presentation B (C c) = algebraMap ℚ (CubeAlgebra B) c := by
  simp [presentation]

/-- `b_ij = B(vᵢ, vⱼ)` for the standard basis. -/
theorem polar_single_single (i j : ι) : B.polar (Pi.single i 1) (Pi.single j 1) = B.b i j := by
  simp [BilinearFormMatrix.polar]

/-- The relation ideal `I = ⟨XᵢXⱼ − b_ij Z⟩ + ⟨XᵢZ⟩ + ⟨Z²⟩` of Lemma 3.2. -/
noncomputable def relationIdeal (B : BilinearFormMatrix ι) :
    Ideal (MvPolynomial (Option ι) ℚ) :=
  Ideal.span
    ((Set.range fun ij : ι × ι => X (some ij.1) * X (some ij.2) - C (B.b ij.1 ij.2) * X none) ∪
      (Set.range fun i : ι => X (some i) * X none) ∪ {X none ^ 2})

/-- The relations of Lemma 3.2 hold in `A_B`: `I ⊆ ker (ℚ[X, Z] → A_B)`. -/
theorem relationIdeal_le_ker : relationIdeal B ≤ RingHom.ker (presentation B) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ((⟨⟨i, j⟩, rfl⟩ | ⟨i, rfl⟩) | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, presentation_X_some,
      presentation_X_none, presentation_C, ofVector_mul_ofVector, polar_single_single,
      Algebra.smul_def, sub_self]
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_mul, presentation_X_some,
      presentation_X_none]
    ext <;> simp
  · simp [RingHom.mem_ker, sq]

/-- `ℚ[X, Z] → A_B` is surjective: `(r, v, s)` is the image of `r + ∑ᵢ vᵢ Xᵢ + s Z`. -/
theorem presentation_surjective : Function.Surjective (presentation B) := by
  have hV : ∀ v : ι → ℚ, ∃ p, presentation B p = ofVector B v := by
    intro v
    induction v using Pi.single_induction with
    | zero => exact ⟨0, by ext <;> simp⟩
    | add f g hf hg =>
      obtain ⟨p, hp⟩ := hf
      obtain ⟨q, hq⟩ := hg
      exact ⟨p + q, by rw [map_add, hp, hq]; ext <;> simp⟩
    | single i m => exact ⟨C m * X (some i), by ext <;> simp [Pi.single_apply]⟩
  rintro ⟨r, v, s⟩
  obtain ⟨p, hp⟩ := hV v
  refine ⟨C r + p + C s * X none, ?_⟩
  rw [map_add, map_add, map_mul, hp, presentation_C, presentation_C, presentation_X_none]
  ext <;> simp

end Presentation

end CubeAlgebra

end Trinomial
