import Trinomial.Universal.FixedIdeal
import Trinomial.Universal.ComputableHaltingFamily
import Trinomial.Encoding.Undecidability
import Trinomial.Encoding.GuardSection
import Trinomial.Encoding.RationalInfinity
import Trinomial.Quadrics.CubeAlgebraPresentation
import Trinomial.Quadrics.CubeAlgebraGraded
import Trinomial.Quadrics.CubeAlgebraSocle
import Trinomial.Base.PrimitiveNormalization
import Trinomial.Base.BasePrimary

/-!
# The paper, statement by statement

This file follows the paper (Boege–Hofer–Kahle, *Trinomial containment in polynomial
ideals is undecidable*) in the paper's order and notation.  Formalized results appear as
Lean statements with short proofs referring to the development.  A result of the paper is
formalized exactly when its mathematical content appears here, and the docstring of each
item records every deviation from the paper's wording.  The remaining omissions are listed
before the axiom checks.  The axioms of every formalized item are printed at the end
(`#print axioms`); all depend on `propext`, `Classical.choice`, `Quot.sound` only.

Notation (see `README.md` for the full glossary):

* `Laurent N` is `L_N = ℚ[S^{±1}, T^{±1}, D₁^{±1}, …, D_N^{±1}]`, `mono ⟨a, b, d⟩` the
  monomial `S^a T^b D^d`, `S N`, `T N`, `D i` the variables;
* `MvPolynomial (Var N) ℚ` is `ℚ[S, T, D₁, …, D_N]`, with variables `X Var.S`, `X Var.T`,
  `X (Var.D i)`;
* `baseIdeal N` is `J₀`, `BaseAlgebra N` the coordinate model of `A₀ = L_N/J₀` with
  `B`, `C i` the residues of `S − T`, `Dᵢ − 1`, and `baseQuotEquiv N : L_N/J₀ ≃ A₀`;
* `tau d`, `theta e p q`, `Omega N` are `τ_d`, `θ_e^{p,q}`, `Ω`; `tauPoly d` is `τ̃_d`;
* `CubeAlgebra B` is `A_B` for the matrix `B : BilinearFormMatrix ι` of a symmetric bilinear
  form, `CubeAlgebra.zeta B` is `ζ`, `CubeAlgebra.ofVector B v` the element `v ∈ V`;
* `phi G : L_N →ₐ A_Q` is `φ_Q`, where `G : BilinearFormMatrix (Option (Fin N))` is the
  matrix of `Q` in the basis `v₁, …, v_N, v₀` (`none` is the homogenization coordinate `v₀`),
  `quadAt G d t = Q(d, t)`, `ratCast d` the integer vector `d` read in `ℚ^N`;
* `DegreeTwoEquation r` is an equation of degree at most two in `r` variables,
  `Solves z L` says that `z` is a common integral zero of the system `L`, and
  `IntPolynomialCode n` is the sparse syntax of a polynomial `P ∈ ℤ[y₁, …, yₙ]` with value
  `evalPolynomial p y`;
* `polyIdeal p` is `I_P` and `generatorsOf p` its computed generator list.
-/

set_option autoImplicit false

namespace Trinomial.Paper

open Trinomial BaseAlgebra CubeAlgebra
open MvPolynomial (X monomial)
open TrinomialUndecidability.Computability (IntPolynomialCode EffDiophRel evalPolynomial)
open TrinomialUndecidability.Computability.HaltingEvalnBridge (HaltsAtZero)
open Nat.Partrec (Code)

variable {N : ℕ}

/-! ## Section 1: the number of terms

`tinv I = t(I) = min {|supp f| : 0 ≠ f ∈ I}` with `t(0) = ∞`, for an ideal `I` of any
polynomial ring `MvPolynomial σ K`; `HasShortPoly k I` is the decision problem `t(I) ≤ k`
(`Trinomial/ShortestPolynomial.lean`).  On the Laurent side, `HasShort k I` is the same
problem for an ideal of `L_N`.  The subsequent introductory algorithms for one or two
terms and for a prescribed finite support are listed among the omissions below. -/

/-- `t(I) ≤ k` iff `I` contains a nonzero polynomial with at most `k` terms. -/
theorem tinv_le_iff {σ K : Type*} [CommSemiring K] (I : Ideal (MvPolynomial σ K)) (k : ℕ) :
    tinv I ≤ k ↔ HasShortPoly k I :=
  Trinomial.tinv_le_iff

/-! ## Section 2: the base ideal -/

/-- The statement preceding Lemma 2.1: `J₀` is primary to the maximal ideal
`(2S−1, 2T−1, D₁−1, …, D_N−1)`, and its radical is that ideal.  The displayed
maximal ideal is `baseMaximalIdeal N`. -/
theorem base_ideal_primary_and_radical :
    (baseIdeal N).IsPrimary
    ∧ (baseIdeal N).radical = baseMaximalIdeal N
    ∧ (baseMaximalIdeal N).IsMaximal :=
  ⟨baseIdeal_isPrimary N, radical_baseIdeal N, baseMaximalIdeal_isMaximal N⟩

/-- **Lemma 2.1.**  `J₀` has Krull dimension zero (`ringKrullDim (L_N/J₀) = 0`), and the
images of `1, B, B², B³, B⁴, C₁, …, C_N` form a `ℚ`-basis of `A₀ = L_N/J₀`, so
`dim_ℚ A₀ = N + 5`.  The basis is `quotBasis N`, indexed by `Fin 5 ⊕ Fin N`. -/
theorem lemma_A0_dim :
    ringKrullDim (Laurent N ⧸ baseIdeal N) = 0
    ∧ (∀ k : Fin 5, quotBasis N (Sum.inl k) = Ideal.Quotient.mk _ ((S N - T N) ^ (k : ℕ)))
    ∧ (∀ i : Fin N, quotBasis N (Sum.inr i) = Ideal.Quotient.mk _ (D i - 1))
    ∧ Module.finrank ℚ (Laurent N ⧸ baseIdeal N) = N + 5 :=
  ⟨ringKrullDim_quotient_baseIdeal N, quotBasis_inl, quotBasis_inr, finrank_quotient_baseIdeal N⟩

/-- **Lemma 2.2**, the relations `S = (1+B)/2`, `T = (1−B)/2`, `Dᵢ = 1 + Cᵢ` modulo `J₀`,
read in `A₀` through `baseQuotEquiv`. -/
theorem lemma_J0_nf_variables :
    baseQuotEquiv N (Ideal.Quotient.mk _ (S N)) = (1 / 2 : ℚ) • (1 + B N)
    ∧ baseQuotEquiv N (Ideal.Quotient.mk _ (T N)) = (1 / 2 : ℚ) • (1 - B N)
    ∧ ∀ i, baseQuotEquiv N (Ideal.Quotient.mk _ (D i)) = 1 + BaseAlgebra.C i := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · rw [baseQuotEquiv_mk, baseEval_S]; ext <;> simp [B]
  · rw [baseQuotEquiv_mk, baseEval_T]; ext <;> simp [B, sub_eq_add_neg]; norm_num
  · rw [baseQuotEquiv_mk, baseEval_D]
    refine BaseAlgebra.ext (by simp [BaseAlgebra.C]) (by simp [BaseAlgebra.C])
      (by simp [BaseAlgebra.C]) (by simp [BaseAlgebra.C]) (by simp [BaseAlgebra.C]) ?_
    funext j; simp [BaseAlgebra.C]

/-- **Lemma 2.2**, "the images of `1 + B` and `1 − B` in `A₀` are units": the units
`uBe N 1 = 1 + B` and `uBe N (-1) = 1 − B` of `A₀`. -/
theorem lemma_J0_nf_units :
    ((uBe N 1 : (BaseAlgebra N)ˣ) : BaseAlgebra N) = 1 + B N
    ∧ ((uBe N (-1) : (BaseAlgebra N)ˣ) : BaseAlgebra N) = 1 - B N := by
  constructor <;> (ext <;> simp [B, sub_eq_add_neg])

/-- The linear combination `Σ dᵢ Cᵢ` in coordinates. -/
theorem sum_smul_C (d : Fin N → ℚ) : (∑ i, d i • BaseAlgebra.C i) = ⟨0, 0, 0, 0, 0, d⟩ := by
  apply (baseCoordEquiv N).injective
  rw [map_sum]
  funext k
  rcases k with k | j
  · simp only [Finset.sum_apply, map_smul, baseCoordEquiv_apply, Pi.smul_apply]
    fin_cases k <;> simp [BaseAlgebra.C]
  · simp [BaseAlgebra.C, Pi.single_apply]

/-- **Lemma 2.2**, the normal form: for all `a, b ∈ ℤ` and `d ∈ ℤ^N`,
`S^a T^b D^d ≡ 2^{−a−b} ((1+B)^a (1−B)^b + Σᵢ dᵢ Cᵢ) (mod J₀)`, where `(1±B)^a` are the
integer powers of the units of `lemma_J0_nf_units`.  The truncated binomial series
`(1+εB)^a = Σ_{k<5} (a choose k) ε^k B^k` used in the paper's proof of Proposition 2.4,
with mathlib's generalized binomial coefficient `Ring.choose`, is `uBe_zpow`. -/
theorem lemma_J0_nf (x : Exponent N) :
    baseQuotEquiv N (Ideal.Quotient.mk (baseIdeal N) (mono x)) =
      (1 / 2 : ℚ) ^ (x.s + x.t) •
        (((uBe N 1 ^ x.s * uBe N (-1) ^ x.t : (BaseAlgebra N)ˣ) : BaseAlgebra N)
          + ∑ i, (x.d i : ℚ) • BaseAlgebra.C i) := by
  rw [baseQuotEquiv_mk, baseEval_mono, baseMonoUnit_val, Units.val_mul, uBe_zpow, uBe_zpow,
    sum_smul_C]
  congr 1
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp [w1]; ring
  · simp [w2]; ring
  · simp [w3]; ring
  · simp [w4]; ring
  · funext j
    simp

/-- **Definition 2.3** of the two trinomial families and of the clearing, as in the paper:
`τ_d = 1 − S D^d − T D^{−d}`, `θ_e^{p,q} = (p−q) + q D^{pe} − p D^{qe}`, and
`τ̃_d = D^{|d|} τ_d = D^{|d|} − S D^{|d|+d} − T D^{|d|−d}` (`tauPoly_eq` spells the
exponents out in `ℚ[S, T, D]`; `toLaurent_tauPoly` identifies `τ̃_d` with `D^{|d|} τ_d`). -/
theorem definition_trinomials (d e : Fin N → ℤ) (p q : ℤ) :
    tau d = 1 - mono ⟨1, 0, d⟩ - mono ⟨0, 1, -d⟩
    ∧ theta e p q = ((p : ℚ) - q) • 1 + (q : ℚ) • mono ⟨0, 0, p • e⟩ - (p : ℚ) • mono ⟨0, 0, q • e⟩
    ∧ toLaurent N (tauPoly d) = mono ⟨0, 0, fun i => ((d i).natAbs : ℤ)⟩ * tau d := by
  refine ⟨rfl, rfl, ?_⟩
  rw [toLaurent_tauPoly]
  simp

/-- **Proposition 2.4 (i).**  There is no monomial or binomial in `J₀`: no nonzero element
of `J₀` has at most two terms. -/
theorem prop_shape_i : ¬ HasShort 2 (baseIdeal N) := by
  rintro ⟨f, hf, hf0, hcard⟩
  exact no_binomial_in_baseIdeal hf
    (le_antisymm hcard (one_lt_supportCard_of_mem_baseIdeal hf hf0))

/-- **The units of `L_N`.**  "Up to units of `L_N`" in Proposition 2.4 means up to
nonzero scalars and Laurent monomials: `f ∈ L_N` is a unit if and only if
`f = c · S^a T^b D^d` with `c ≠ 0`.  (Monomials are units; conversely, ordering the exponent
lattice lexicographically, the coefficients of a product at the sum of the largest and at the
sum of the smallest exponents of the factors are nonzero, so a factor of `1` has one term.) -/
theorem units_of_laurent (f : Laurent N) :
    IsUnit f ↔ ∃ (c : ℚ) (z : Exponent N), c ≠ 0 ∧ f = c • mono z :=
  isUnit_laurent_iff f

/-- **Proposition 2.4 (ii).**  Up to units of `L_N` (nonzero scalars times monomials
`S^a T^b D^d`, which are all the units by `units_of_laurent`), the trinomials of `J₀` are
precisely the affine trinomials `τ_d`, `d ∈ ℤ^N`, and the infinite trinomials `θ_e^{p,q}`,
`e ∈ ℤ^N` primitive (`IsPrimitive e`: the coordinates of `e` have gcd `1`) and `p, q ∈ ℤ`
distinct and nonzero. -/
theorem prop_shape_ii (f : Laurent N) :
    (f ∈ baseIdeal N ∧ f.support.card = 3) ↔
      (∃ (c : ℚ) (z : Exponent N) (d : Fin N → ℤ), c ≠ 0 ∧ f = c • (mono z * tau d)) ∨
      (∃ (c : ℚ) (z : Exponent N) (e : Fin N → ℤ) (p q : ℤ), c ≠ 0 ∧ IsPrimitive e ∧
        p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ f = c • (mono z * theta e p q)) := by
  constructor
  · rintro ⟨hf, h3⟩
    exact trinomial_in_baseIdeal_primitive hf h3
  · have hmem : ∀ (c : ℚ) (z : Exponent N) (g : Laurent N), g ∈ baseIdeal N →
        c • (mono z * g) ∈ baseIdeal N := fun c z g hg => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hg)
    rintro (⟨c, z, d, hc, rfl⟩ | ⟨c, z, e, p, q, hc, he, hp, hq, hpq, rfl⟩)
    · exact ⟨hmem c z _ (tau_mem_baseIdeal d),
        by rw [supportCard_smul_mono_mul hc, supportCard_tau]⟩
    · exact ⟨hmem c z _ (theta_mem_baseIdeal e p q),
        by rw [supportCard_smul_mono_mul hc, supportCard_theta he.ne_zero hp hq hpq]⟩

/-- **Proposition 2.4 (iii).**  The quadrinomial `Ω = (S+T−1)(S−T) = S² − T² − S + T`
lies in `J₀`, and it has four terms. -/
theorem prop_shape_iii :
    Omega N = (S N + T N - 1) * (S N - T N)
    ∧ Omega N = mono ⟨2, 0, 0⟩ - mono ⟨0, 2, 0⟩ - mono ⟨1, 0, 0⟩ + mono ⟨0, 1, 0⟩
    ∧ Omega N ∈ baseIdeal N ∧ (Omega N).support.card = 4 :=
  ⟨rfl, Omega_eq_singles, Omega_mem_baseIdeal, supportCard_Omega⟩

/-! ## Section 3: imposing quadratic constraints -/

section Quadrics

variable {ι : Type*} [Fintype ι] (B : BilinearFormMatrix ι)

/-- **Definition 3.1** of `A_B`: the multiplication
`(r, v, s)·(r', v', s') = (rr', rv' + r'v, rs' + r's + B(v, v'))` on `ℚ × V × ℚ`, where
`B(v, v') = polar` is the bilinear form with matrix `(b_ij)` (mathlib's `Matrix.toBilin'`,
`polar_eq_toBilin'`), and `Q(v) = B(v, v)` (`quad_eq_toQuadraticMap`).  The paper's
associated bilinear form `B(v, v') = ½(Q(v+v') − Q(v) − Q(v'))` is `quad_add`. -/
theorem definition_A_B (x y : CubeAlgebra B) :
    (x * y).scalar = x.scalar * y.scalar
    ∧ (x * y).vector = x.scalar • y.vector + y.scalar • x.vector
    ∧ (x * y).socle = x.scalar * y.socle + y.scalar * x.socle + B.polar x.vector y.vector
    ∧ ∀ v w : ι → ℚ, B.quad (v + w) = B.quad v + 2 * B.polar v w + B.quad w :=
  ⟨rfl, rfl, rfl, fun v w => B.quad_add v w⟩

/-- **Lemma 3.2.**  `A_B` is local with nilradical `𝔫 = V ⊕ ℚζ` (the elements with vanishing
scalar coordinate, `nilideal B`), `𝔫³ = 0` (Remark 3.3), and `A_B ≅ ℚ[X₁, …, Xₙ, Z]/I` with
`I = ⟨XᵢXⱼ − b_ij Z⟩ + ⟨XᵢZ⟩ + ⟨Z²⟩` (`relationIdeal B`; the products `XᵢXⱼ` are taken over
all ordered pairs, which generates the same ideal as `i ≤ j`), the isomorphism
`presentationEquiv B` being induced by `Xᵢ ↦ vᵢ`, `Z ↦ ζ` (`presentation B`). -/
theorem lemma_A_B [DecidableEq ι] :
    IsLocalRing (CubeAlgebra B)
    ∧ nilradical (CubeAlgebra B) = nilideal B
    ∧ IsLocalRing.maximalIdeal (CubeAlgebra B) = nilideal B
    ∧ (∀ x : CubeAlgebra B, x ∈ nilideal B ↔ x.scalar = 0)
    ∧ nilideal B ^ 3 = ⊥
    ∧ RingHom.ker (presentation B) = relationIdeal B
    ∧ ∀ p, presentationEquiv B (Ideal.Quotient.mk _ p) = presentation B p :=
  ⟨inferInstance, nilradical_eq, maximalIdeal_eq, mem_nilideal_iff, nilideal_pow_three,
    ker_presentation, fun p => presentationEquiv_mk p⟩

/-- **Lemma 3.2, the grading.**  The homogeneous components of the graded algebra
`A_B = ℚ ⊕ V ⊕ ℚζ` are the scalar line in degree zero, `V` in degree one, the socle line
`ℚζ` in degree two, and zero in every degree at least three.  The final conjunct records
the `GradedAlgebra` structure built from the explicit coordinate decomposition. -/
theorem lemma_A_B_graded :
    (∀ x : CubeAlgebra B, x ∈ homogeneousComponent B 0 ↔
      x.vector = 0 ∧ x.socle = 0)
    ∧ (∀ x : CubeAlgebra B, x ∈ homogeneousComponent B 1 ↔
      x.scalar = 0 ∧ x.socle = 0)
    ∧ (∀ x : CubeAlgebra B, x ∈ homogeneousComponent B 2 ↔
      x.scalar = 0 ∧ x.vector = 0)
    ∧ (∀ n : ℕ, homogeneousComponent B (n + 3) = ⊥)
    ∧ Nonempty (GradedAlgebra (homogeneousComponent B)) := by
  exact ⟨fun x => mem_degreeZero_iff x, fun x => mem_degreeOne_iff x,
    fun x => mem_degreeTwo_iff x, homogeneousComponent_add_three, ⟨inferInstance⟩⟩

/-- **The structural remark after Lemma 3.2.**  The socle of `A_B` (the annihilator of
its maximal ideal `𝔫`, `socleIdeal B`) is `rad(B) ⊕ ℚζ`: an element lies in the socle
exactly when its scalar coordinate vanishes and its vector coordinate lies in the radical
`rad(B) = ker B` of the bilinear form, and as a `ℚ`-vector space the socle is
`rad(B) × ℚ`.  It is the line `ℚζ` exactly when the bilinear form is nondegenerate.  For a finite local algebra this one-dimensional-socle condition is the
criterion used in the paper for `A_B` to be Gorenstein.  Mathlib has no general
Gorenstein predicate, so the statement records that criterion explicitly.  The last
conjunct also records that the construction realizes the given symmetric bilinear map
as multiplication `V × V → ℚζ`. -/
theorem remark_A_B_socle :
    (∀ x : CubeAlgebra B, x ∈ socleIdeal B ↔ x.scalar = 0 ∧ x.vector ∈ B.radical)
    ∧ Nonempty (socleIdeal B ≃ₗ[ℚ] B.radical × ℚ)
    ∧ ((∀ x : CubeAlgebra B, x ∈ socleIdeal B ↔
        ∃ s : ℚ, x = s • zeta B) ↔ B.polar.Nondegenerate)
    ∧ ∀ v w : ι → ℚ,
      ofVector B v * ofVector B w = B.polar v w • zeta B :=
  ⟨fun x => mem_socleIdeal_iff x, ⟨socleEquivRadicalProd B⟩,
    socle_is_zeta_line_iff_nondegenerate B, ofVector_mul_ofVector⟩

/-- **The exponential.**  `Exp(x) = 1 + x + ½x²` is an isomorphism from the additive group
`𝔫` onto the multiplicative group `1 + 𝔫` (`expEquiv`), with inverse
`Log(1 + u) = u − ½u²`; and for `v, v' ∈ V`: `Exp(v) = 1 + v + ½ Q(v) ζ`,
`Exp(−v) = Exp(v)⁻¹`, `Exp(v) Exp(v') = Exp(v + v')`. -/
theorem exponential :
    (∀ x : nilideal B, ((expEquiv (B := B) (Multiplicative.ofAdd x) : (CubeAlgebra B)ˣ)
      : CubeAlgebra B) = 1 + x + (1 / 2 : ℚ) • (x * x))
    ∧ (∀ x : CubeAlgebra B, x.scalar = 0 → logNil (expNil x) = x)
    ∧ (∀ y : CubeAlgebra B, (y - 1).scalar = 0 → expNil (logNil y) = y)
    ∧ (∀ v : ι → ℚ, expNil (ofVector B v) = ⟨1, v, B.quad v / 2⟩)
    ∧ (∀ v : ι → ℚ, exp B v * exp B (-v) = 1)
    ∧ ∀ v w : ι → ℚ, exp B v * exp B w = exp B (v + w) :=
  ⟨fun _ => rfl, fun _ hx => logNil_expNil hx, fun _ hy => expNil_logNil hy,
    fun v => expNil_ofVector v, exp_mul_exp_neg, exp_mul_exp⟩

end Quadrics

section KernelEvaluation

variable (G : BilinearFormMatrix (Option (Fin N)))

/-- **Definition 3.4** of `φ_Q : L_N → A_Q`: `S ↦ ½ Exp(v₀)`, `T ↦ ½ Exp(−v₀)`, `Dᵢ ↦ Exp(vᵢ)`;
a `ℚ`-algebra homomorphism (`phi G`), determined by these values (`algHom_ext_laurent`). -/
theorem definition_phi :
    phi G (S N) = (1 / 2 : ℚ) • exp G (homVec 0 1)
    ∧ phi G (T N) = (1 / 2 : ℚ) • exp G (homVec 0 (-1))
    ∧ ∀ i, phi G (D i) = exp G (homVec (Pi.single i 1) 0) :=
  ⟨phi_S G, phi_T G, phi_D G⟩

/-- **Proposition 3.5.**  For every `d ∈ ℤ^N`, `e ∈ ℤ^N` and `p, q ∈ ℤ`:
`φ_Q(τ_d) = −½ Q(d,1) ζ` and `φ_Q(θ_e^{p,q}) = ½ pq(p−q) Q(e,0) ζ`; in particular
`τ_d ∈ ker φ_Q ⟺ Q(d,1) = 0`, and for `p, q` distinct and nonzero
`θ_e^{p,q} ∈ ker φ_Q ⟺ Q(e,0) = 0`.  (The formulas hold without the paper's hypothesis
that `e` be primitive.) -/
theorem prop_A_Q_eval (d e : Fin N → ℤ) (p q : ℤ) :
    phi G (tau d) = (-(quadAt G (ratCast d) 1 / 2)) • zeta G
    ∧ phi G (theta e p q) = ((p * q * (p - q) : ℚ) * quadAt G (ratCast e) 0 / 2) • zeta G
    ∧ (tau d ∈ RingHom.ker (phi G) ↔ quadAt G (ratCast d) 1 = 0)
    ∧ (p ≠ 0 → q ≠ 0 → p ≠ q →
        (theta e p q ∈ RingHom.ker (phi G) ↔ quadAt G (ratCast e) 0 = 0)) :=
  ⟨phi_tau G d, phi_theta G e p q, tau_mem_ker_phi_iff G d,
    fun hp hq hpq => theta_mem_ker_phi_iff G e hp hq hpq⟩

end KernelEvaluation

/-! ## Section 4: encoding Diophantine equations -/

/-- **Lemma 4.1**, as an algorithm.  The executable function `degreeTwoSystem` computes
from the syntax `p` of `P ∈ ℤ[y₁, …, yₙ]` a system of `m` equations of degree at most two
(`DegreeTwoEquation`) in `r = n + k` variables (`k` the number of auxiliary variables of the
straight line program `StraightLineProgram.ofCode p`, which computes `P`: `ofCode_computes`),
such that `∃ y ∈ ℤⁿ : P(y) = 0 ⟺ ∃ x ∈ ℤʳ : f₁(x) = ⋯ = f_m(x) = 0`. -/
theorem lemma_quadratic {n : ℕ} (p : IntPolynomialCode n) :
    (StraightLineProgram.ofCode p).Computes (evalPolynomial p)
    ∧ ((∃ y : Fin n → ℤ, evalPolynomial p y = 0)
        ↔ ∃ x : Fin (n + (StraightLineProgram.ofCode p).k) → ℤ, Solves x (degreeTwoSystem p)) :=
  ⟨StraightLineProgram.ofCode_computes p, (degreeTwoSystem_solvable_iff p).symm⟩

/-- **Lemma 4.2.**  For a system `L = (f₁, …, f_m)` of equations of degree at most
two in `r` variables, the guarded system `guarded L` in the `r + 6` variables
`x, h, k, u₁, …, u₄` consists of `f₁, …, f_m` and the two guards
`g_{m+1} = h² − 3k² − 1`, `g_{m+2} = Σ xᵢ² + Σ uⱼ² − h` (in the affine chart `t = 1`), and
`homogenizedSystem (guarded L)` is the family of homogenized quadratic forms `gᵢ(x, t)`,
with `gᵢ(x, 1) = fᵢ(x)` (`quadAt_homogenize_one`).  Then:

* the origin is the only rational solution of `g₁, …, g_{m+2}` with `t = 0`;
* the projection `π : X̂₁ → X` (forgetting `h, k, u`) is surjective: every integral solution
  `z` of `L` extends to an integral solution `w` of the guarded system;
* `guardSection` is a computable section of `π`: for every solution `z` of `L`,
  `guardSection z` solves the guarded system and restricts to `z`.

In particular `X = ∅ ⟺ X̂₁ = ∅` (`guarded_solvable_iff`). -/
theorem lemma_Pell_guard {r : ℕ} (L : List (DegreeTwoEquation r)) :
    (∀ w : Fin (r + 6) → ℤ, Solves w (guarded L) ↔
      (Solves (fun i => w (Fin.castAdd 6 i)) L
        ∧ w (vh r) ^ 2 - 3 * w (vk r) ^ 2 - 1 = 0
        ∧ (∑ i : Fin r, w (Fin.castAdd 6 i) ^ 2) + (∑ j : Fin 4, w (vu r j) ^ 2) - w (vh r) = 0))
    ∧ (∀ (F : DegreeTwoEquation (r + 6)) (z : Fin (r + 6) → ℤ),
        quadAt F.homogenize (ratCast z) 1 = F.eval z)
    ∧ NoRationalSolutionAtInfinity (homogenizedSystem (guarded L))
    ∧ (∀ z : Fin r → ℤ, Solves z L →
        ∃ w : Fin (r + 6) → ℤ, Solves w (guarded L) ∧ ∀ i, w (Fin.castAdd 6 i) = z i)
    ∧ (∀ z : Fin r → ℤ, Solves z L →
        Solves (guardSection z) (guarded L) ∧ ∀ i, guardSection z (Fin.castAdd 6 i) = z i)
    ∧ ((∃ w : Fin (r + 6) → ℤ, Solves w (guarded L)) ↔ ∃ z : Fin r → ℤ, Solves z L) := by
  refine ⟨fun w => ?_, fun F z => DegreeTwoEquation.quadAt_homogenize_one F z,
    noRationalSolutionAtInfinity_homogenizedSystem L, projection_surjective L,
    fun z hz => ⟨guardSection_solves hz, guardSection_castAdd z⟩, guarded_solvable_iff L⟩
  rw [guarded, solves_append, Solves, Solves]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    DegreeTwoEquation.eval_rename, gPell_eval, gSq_eval]
  simp only [sq]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- **Remark 4.4.**  The displayed identity holds.  Consequently, if an
ideal contains the three affine trinomials indexed by the arithmetic progression
`d−e, d, d+e`, where `e ≠ 0`, then it contains an infinite trinomial
`θ_(e')^(g,−g)` with `e = g e'`, `g > 0`, and `e'` primitive. -/
theorem remark_infinite_forced (d e : Fin N → ℤ) (he : e ≠ 0) :
    tau (d - e) + tau (d + e)
        - (mono (⟨0, 0, e⟩ : Exponent N) + mono ⟨0, 0, -e⟩) * tau d =
      2 - mono ⟨0, 0, e⟩ - mono ⟨0, 0, -e⟩
    ∧ ∀ I : Ideal (Laurent N),
      tau (d - e) ∈ I → tau d ∈ I → tau (d + e) ∈ I →
        ∃ (g : ℕ) (e' : Fin N → ℤ), 0 < g ∧ IsPrimitive e'
          ∧ e = (g : ℤ) • e' ∧ theta e' (g : ℤ) (-(g : ℤ)) ∈ I := by
  refine ⟨tau_three_term_identity d e, ?_⟩
  intro I hminus hzero hplus
  exact infinite_trinomial_mem_of_tau_arithmetic_progression I he hminus hzero hplus

/-- **Theorem 4.5.**  The executable function `generatorsOf` computes from the syntax `p` of
any `P ∈ ℤ[y₁, …, yₙ]` the number `N = numVars p` and a list of at most `C(N+7,5)`
generators of the ideal `I_P = polyIdeal p ⊆ ℚ[S, T, D₁, …, D_N]`, each of total degree at
most five, such that

* `I_P` has Krull dimension zero and is primary to `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`,
  which is a maximal ideal;
* `I_P` contains no monomial and no binomial;
* `I_P` contains the quadrinomial `S² − T² − S + T`;
* every trinomial in `I_P` is a term `c·S^a T^b D^m` times a cleared affine trinomial `τ̃_d`;
* `∃ d ∈ ℤ^N : τ̃_d ∈ I_P ⟺ ∃ y ∈ ℤⁿ : P(y) = 0`. -/
theorem theorem_main {n : ℕ} (p : IntPolynomialCode n) :
    Ideal.span {g | ∃ l ∈ generatorsOf p, g = l.toPoly} = polyIdeal p
    ∧ (∀ l ∈ generatorsOf p, l.toPoly.totalDegree ≤ 5)
    ∧ (generatorsOf p).length ≤ Nat.choose (numVars p + 7) 5
    ∧ ringKrullDim (MvPolynomial (Var (numVars p)) ℚ ⧸ polyIdeal p) = 0
    ∧ (polyIdeal p).IsPrimary ∧ (polyIdeal p).radical = pointIdeal (numVars p)
    ∧ (pointIdeal (numVars p)).IsMaximal
    ∧ ¬ HasShortPoly 2 (polyIdeal p)
    ∧ (X Var.S ^ 2 - X Var.T ^ 2 - X Var.S + X Var.T : MvPolynomial (Var (numVars p)) ℚ)
        ∈ polyIdeal p
    ∧ (∀ f ∈ polyIdeal p, f.support.card = 3 →
        ∃ (c : ℚ) (m : Var (numVars p) →₀ ℕ) (d : Fin (numVars p) → ℤ),
          c ≠ 0 ∧ f = c • (monomial m 1 * tauPoly d))
    ∧ ((∃ d : Fin (numVars p) → ℤ, tauPoly d ∈ polyIdeal p)
        ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Trinomial.theorem_main p
  refine ⟨h1, fun l hl => generators_totalDegree_le _ hl, h2, h3, h4, h5, pointIdeal_isMaximal _,
    h6, ?_, h8, h9⟩
  rwa [← OmegaPoly_eq]

open Classical in
/-- **The displayed formula of the introduction**: `t(I_P) = 3` if `P` has an integral zero
and `t(I_P) = 4` otherwise. -/
theorem tinv_I_P {n : ℕ} (p : IntPolynomialCode n) :
    tinv (polyIdeal p) = if ∃ y : Fin n → ℤ, evalPolynomial p y = 0 then 3 else 4 :=
  tinv_polyIdeal p

/-- **Corollary 4.6**, the Diophantine reduction retained as a direct consequence
of Theorem 4.5.  For the zero-dimensional ideals `I_P` of
Theorem 4.5, each of the three questions (A) "`I` contains a trinomial", (B) "`I` contains
a nonzero polynomial with at most three terms", (C) "`t(I) = 3`, under the promise
`t(I) ∈ {3, 4}`" has answer YES if and only if `P` has an integral zero.
The many-one statement on encoded presentations is `cor_undecidable`. -/
theorem cor_undecidable_reduction {n : ℕ} (p : IntPolynomialCode n) :
    ((∃ f ∈ polyIdeal p, f.support.card = 3) ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0)
    ∧ (HasShortPoly 3 (polyIdeal p) ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0)
    ∧ (tinv (polyIdeal p) = 3 ∨ tinv (polyIdeal p) = 4)
    ∧ (tinv (polyIdeal p) = 3 ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0) := by
  have h := main_theorem_code p
  have ht := tinv_polyIdeal p
  refine ⟨?_, h.2.1, ?_, ?_⟩
  · rw [← h.2.1]
    constructor
    · rintro ⟨f, hf, h3⟩
      exact ⟨f, hf, fun h0 => by simp [h0] at h3, h3.le⟩
    · rintro ⟨f, hf, hf0, hf3⟩
      refine ⟨f, hf, le_antisymm hf3 ?_⟩
      by_contra hlt
      exact h.1 ⟨f, hf, hf0, by omega⟩
  · rw [ht]; split_ifs <;> simp
  · rw [ht]; split_ifs with hc <;> simp [hc]

/-- **Corollary 4.6.**  Problems (A) "`I` contains a trinomial" (`ContainsTrinomial`)
and (B) "`I` contains a nonzero polynomial with at most three terms"
(`ContainsAtMostThree`) on encoded finite rational ideal presentations
(`IdealPresentation`: a number `k` of variables and a finite list of sparse polynomials
with rational coefficients) are many-one equivalent to the natural-number fixed-input
halting problem `HaltingProblemAtZero`.  The explicit forward reductions output only
zero-dimensional presentations.

Problem (C) is a promise problem, and mathlib's `ManyOneEquiv` is defined for total
predicates only.  The total predicate `TinvThreeProblem` is *by definition*
`ContainsTrinomial` (the question "`t(I) = 3`" extended off the promise by the trinomial
question), so the third equivalence below restates the first; the content specific to (C)
is the fourth conjunct, agreement with `t(I) = 3` on every promised presentation, and the
last conjunct, that the forward reduction lands in the promised zero-dimensional
instances.  The promise problem itself, with `t(I) = 3` spelled out, is
`cor_undecidable_promise`. -/
theorem cor_undecidable :
    ManyOneEquiv HaltingProblemAtZero ContainsTrinomial
    ∧ ManyOneEquiv HaltingProblemAtZero ContainsAtMostThree
    ∧ ManyOneEquiv HaltingProblemAtZero TinvThreeProblem
    ∧ (∀ q, TinvThreeOrFour q →
        (TinvThreeProblem q ↔ tinv q.ideal = 3))
    ∧ ManyOneReducibleInto HaltingProblemAtZero ContainsTrinomial
        ZeroDimensionalPresentation
    ∧ ManyOneReducibleInto HaltingProblemAtZero ContainsAtMostThree
        ZeroDimensionalPresentation
    ∧ ManyOneReducibleInto HaltingProblemAtZero TinvThreeProblem
        (fun q => ZeroDimensionalPresentation q ∧ TinvThreeOrFour q) :=
  ⟨haltingProblemAtZero_manyOneEquiv_containsTrinomial,
    haltingProblemAtZero_manyOneEquiv_containsAtMostThree,
    haltingProblemAtZero_manyOneEquiv_tinvThreeProblem,
    tinvThreeProblem_iff,
    haltingProblemAtZero_le_containsTrinomial_zeroDimensional,
    haltingProblemAtZero_le_containsAtMostThree_zeroDimensional,
    haltingProblemAtZero_le_tinvThreeProblem_promised_zeroDimensional⟩

/-- **Corollary 4.6, problem (C) as a promise problem.**  Under the promise
`t(I) ∈ {3, 4}`, deciding `t(I) = 3` is many-one equivalent to the halting problem:

* the computable map `e ↦ haltingPresentation e` produces zero-dimensional presentations
  satisfying the promise, with `t(I) = 3` if and only if machine `e` halts on `0`;
* conversely there is a computable `g` such that, on every presentation `I` satisfying
  the promise, `t(I) = 3` if and only if machine `g(I)` halts on `0`. -/
theorem cor_undecidable_promise :
    (Computable haltingPresentation
      ∧ ∀ e : ℕ, ZeroDimensionalPresentation (haltingPresentation e)
        ∧ TinvThreeOrFour (haltingPresentation e)
        ∧ (HaltingProblemAtZero e ↔ tinv (haltingPresentation e).ideal = 3))
    ∧ ∃ g : IdealPresentation → ℕ, Computable g ∧
        ∀ q : IdealPresentation, TinvThreeOrFour q →
          (tinv q.ideal = 3 ↔ HaltingProblemAtZero (g q)) := by
  refine ⟨⟨haltingPresentation_computable, fun e =>
    ⟨haltingPresentation_zeroDimensional e, haltingPresentation_promise e,
      (haltingPresentation_containsTrinomial_iff e).symm.trans
        (tinvThreeProblem_iff _ (haltingPresentation_promise e))⟩⟩, ?_⟩
  obtain ⟨g, hg, hspec⟩ := containsTrinomial_le_haltingProblemAtZero
  exact ⟨g, hg, fun q hq => (tinvThreeProblem_iff q hq).symm.trans (hspec q)⟩

/-- **Remark 4.7.**  The construction gives the chain
`𝒯(J_P) ≃ X̂₁ ↠ X ≃ {y ∈ ℤⁿ | P(y) = 0}`.  Here `𝒯(J_P)` is the actual
quotient of the three-term elements of `J_P` by multiplication by nonzero rational
scalars and Laurent monomials.  Every class has a unique representative `τ_d`, and the
left bijection sends its class to `d` in the affine chart with implicit homogenizing
coordinate `1`.  The middle map forgets the six guard coordinates, its displayed section
is executable, and every fiber contains an injectively indexed copy of `ℕ`.  The right
bijection is projection to the input coordinates.  Finally, the guarded ideal contains no
three affine trinomials indexed by a nonconstant arithmetic progression.

The paper's stronger scheme-isomorphism statement over `ℤ` is not asserted.  This theorem
gives a bijection of integer solution sets.  The right inverse and the final choice of one
trinomial for each zero are not packaged as executable definitions, although the middle
guard section is executable. -/
theorem remark_geometry {n : ℕ} (p : IntPolynomialCode n) :
    Function.Bijective (trinomialClassesEquivGuarded p)
    ∧ (∀ d : NormalizedTauTrinomials p,
        trinomialClassesEquivGuarded p (normalizedTauClass p d) =
          normalizedTauEquivGuarded p d)
    ∧ Function.Surjective (guardProjection (degreeTwoSystem p))
    ∧ Function.LeftInverse (guardProjection (degreeTwoSystem p))
        (guardSolutionSection (degreeTwoSystem p))
    ∧ (∀ z : DegreeTwoSolutionSet p,
        ∃ w : ℕ → GuardedSolutionSet p, Function.Injective w ∧
          ∀ m, guardProjection (degreeTwoSystem p) (w m) = z)
    ∧ Function.Bijective (degreeTwoSolutionsEquivZeros p)
    ∧ (∀ d : NormalizedTauTrinomials p, ∀ i : Fin n,
        (degreeTwoSolutionsEquivZeros p
          (guardProjection (degreeTwoSystem p) (normalizedTauEquivGuarded p d))).1 i =
            d.1 (reductionInputCoordinate p i))
    ∧ (∀ (d e : Fin (numVars p) → ℤ), e ≠ 0 →
        ¬ (tau (d - e) ∈ reductionIdeal (quadraticForms p)
          ∧ tau d ∈ reductionIdeal (quadraticForms p)
          ∧ tau (d + e) ∈ reductionIdeal (quadraticForms p))) :=
  ⟨(trinomialClassesEquivGuarded p).bijective,
    trinomialClassesEquivGuarded_normalizedTauClass p, guardProjection_surjective _,
    guardProjection_section _, guardProjection_infinite_fibers _,
    (degreeTwoSolutionsEquivZeros p).bijective, geometry_input_coordinate p,
    fun _ _ he => not_all_tau_mem_of_arithmetic_progression
      (noIntegralSolutionAtInfinity_homogenizedSystem (degreeTwoSystem p)) he⟩

/-! ## Section 5: a universal halting family

The halting set: machine `e` is the `e`-th partial recursive code `Denumerable.ofNat Code e`
of mathlib, and `HaltsAtZero c` says that `c` halts on input `0`.  The universal polynomial
`U` is represented by the effective Diophantine relation `MRDP.haltingRel` (a finite list
of integer polynomials in the variable `X₀` and `haltingRel.aux` auxiliary variables), and
`U(e, Y)` by the sparse syntax `haltingCode e = frozenCode haltingRel e`. -/

/-- **The universal polynomial** (eq. (9)): `e ∈ K₀ ⟺ ∃ y : U(e, y) = 0`. -/
theorem universal_polynomial (e : ℕ) :
    (∃ x : Fin (1 + MRDP.haltingRel.aux) → ℤ, evalPolynomial (haltingCode e) x = 0)
      ↔ HaltsAtZero (Denumerable.ofNat Code e) :=
  haltingCode_zero_iff e

open Classical in
/-- **Corollary 5.1.**  In the fixed ring `ℚ[S, T, D₁, …, D_{N₀}]`, the ideals
`I_e = haltingIdeal e` (`e ∈ ℕ`) are proper, zero-dimensional, and primary to the maximal
ideal `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_{N₀}−1⟩`, with `t(I_e) = 3` if `M_e(0)` halts and `4`
otherwise, colength `dim_ℚ(ℚ[S, T, D]/I_e) ≤ C(N₀+6, 4)`, and the computed presentation
`haltingGenerators e` consists of at most `C(N₀+7, 5)` generators, each of total degree at
most `5`.

Lean additionally records the sharper colength bound `≤ (N₀+5) + M₀(N₀+3)`, the dimension of
the codomain of `ψ`, which the paper's proof no longer states.  The parameter
`E` is kept as a variable and pinned by a square (`frozenCode`), which adds one variable `D`.
"Computable sequence": the presentation is an executable function `Universal.generators R e`
of the universal relation `R` and of `e` (see `Trinomial/Universal/HaltingFamily.lean`); the
fixed relation `haltingRel` is chosen classically from the proof `MRDP.dioph_haltingSet`
that the halting set is Diophantine (mathlib's `Dioph`; the proof is in this repository),
and mathlib's `Computable` is not applied to `e ↦ haltingGenerators e`. -/
theorem cor_halting_family (e : ℕ) :
    haltingIdeal e ≠ ⊤
    ∧ ringKrullDim (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) = 0
    ∧ (haltingIdeal e).IsPrimary ∧ (haltingIdeal e).radical = pointIdeal N₀
    ∧ (pointIdeal N₀).IsMaximal
    ∧ tinv (haltingIdeal e) = (if HaltsAtZero (Denumerable.ofNat Code e) then 3 else 4)
    ∧ Module.finrank ℚ (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) ≤ (N₀ + 5) + M₀ * (N₀ + 3)
    ∧ Module.finrank ℚ (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) ≤ Nat.choose (N₀ + 6) 4
    ∧ Ideal.span {g | ∃ l ∈ haltingGenerators e, g = l.toPoly} = haltingIdeal e
    ∧ (haltingGenerators e).length ≤ Nat.choose (N₀ + 7) 5
    ∧ ∀ l ∈ haltingGenerators e, l.toPoly.totalDegree ≤ 5 :=
  ⟨haltingIdeal_ne_top e, ringKrullDim_haltingIdeal e, haltingIdeal_isPrimary e,
    radical_haltingIdeal e, pointIdeal_isMaximal _, haltingIdeal_tinv e, finrank_haltingIdeal_le e,
    finrank_haltingIdeal_le_choose e, span_haltingGenerators e,
    haltingGenerators_length_le_choose e, fun _ hl => haltingGenerators_degree_le e hl⟩

open Classical in
/-- **Corollary 5.1, as one computable sequence of finite presentations.**
The map `e ↦ haltingPresentation e` is computable in mathlib's extensional
recursion-theoretic sense.  Every output has the same arity `2 + N₀`, at most
`C(N₀+7,5)` listed generators, and generator degree at most five.

`haltingPresentationFixedIdeal e` is the ideal denoted by that output after the standard
variable renaming into the one fixed ring `ℚ[S,T,D₁,…,D_{N₀}]`, and it is equal to the
ideal `I_e = haltingIdeal e` of `cor_halting_family`
(`haltingPresentationFixedIdeal_eq_haltingIdeal`).  The computability assertion and the
algebraic properties therefore concern one family; the conjuncts after that equation
restate, for the presentation, that `I_e` is proper, zero-dimensional, primary to the
displayed maximal ideal, and has `t = 3` or `4` according as machine `e` halts.

This remains an extensional theorem: `MRDP.haltingRel` is classically chosen, so the
closed presentation is not executable and the paused data-carrying MRDP strengthening
is not asserted. -/
theorem cor_halting_family_computable_presentations :
    Computable (haltingPresentation : ℕ → IdealPresentation)
    ∧ ∀ e : ℕ,
      (haltingPresentation e).1 = 2 + N₀
      ∧ haltingPresentation e =
          compiler ⟨1 + MRDP.haltingRel.aux, frozenCode MRDP.haltingRel e⟩
      ∧ haltingPresentationFixedIdeal e = haltingIdeal e
      ∧ haltingPresentationFixedIdeal e ≠ ⊤
      ∧ (haltingPresentationFixedIdeal e).IsPrimary
      ∧ (haltingPresentationFixedIdeal e).radical = pointIdeal N₀
      ∧ ringKrullDim
          (MvPolynomial (Var N₀) ℚ ⧸ haltingPresentationFixedIdeal e) = 0
      ∧ (haltingPresentation e).generatorPolynomials.length ≤
          Nat.choose (N₀ + 7) 5
      ∧ PresentationGeneratorsDegreeLE (haltingPresentation e) 5
      ∧ (tinv (haltingPresentationFixedIdeal e) =
          if HaltsAtZero (Denumerable.ofNat Code e) then 3 else 4)
      ∧ ZeroDimensionalPresentation (haltingPresentation e)
      ∧ TinvThreeOrFour (haltingPresentation e)
      ∧ tinv (haltingPresentation e).ideal =
          if HaltsAtZero (Denumerable.ofNat Code e) then 3 else 4 :=
  ⟨haltingPresentation_computable, fun e =>
    ⟨haltingPresentation_arity e, haltingPresentation_eq_compiler_frozenCode e,
      haltingPresentationFixedIdeal_eq_haltingIdeal e,
      haltingPresentationFixedIdeal_ne_top e,
      haltingPresentationFixedIdeal_isPrimary e,
      radical_haltingPresentationFixedIdeal e,
      haltingPresentationFixedIdeal_zeroDimensional e,
      haltingPresentation_generatorPolynomials_length_le e,
      haltingPresentation_presentationGeneratorsDegreeLE e,
      haltingPresentationFixedIdeal_tinv e,
      haltingPresentation_zeroDimensional e, haltingPresentation_promise e,
      haltingPresentation_tinv e⟩⟩

/-- **Corollary 5.1, uniformly in the universal polynomial**: the same statement
for every effective Diophantine relation `R` in one free variable, with `R.Realizes (fun _ => e)`
in place of "`M_e(0)` halts".  Here everything, including `Universal.generators R e`, is an
executable function of `R` and `e`. -/
theorem cor_halting_family_uniform (R : EffDiophRel 1) (e : ℕ) :
    Universal.ideal R e ≠ ⊤
    ∧ ringKrullDim (MvPolynomial (Var (Universal.N₀ R)) ℚ ⧸ Universal.ideal R e) = 0
    ∧ (Universal.ideal R e).IsPrimary
    ∧ (Universal.ideal R e).radical = pointIdeal (Universal.N₀ R)
    ∧ (pointIdeal (Universal.N₀ R)).IsMaximal
    ∧ (HasShortPoly 3 (Universal.ideal R e) ↔ R.Realizes (fun _ => (e : ℤ)))
    ∧ Module.finrank ℚ (MvPolynomial (Var (Universal.N₀ R)) ℚ ⧸ Universal.ideal R e)
        ≤ (Universal.N₀ R + 5) + Universal.M₀ R * (Universal.N₀ R + 3)
    ∧ Ideal.span {g | ∃ l ∈ Universal.generators R e, g = l.toPoly} = Universal.ideal R e
    ∧ (Universal.generators R e).length ≤ Nat.choose (Universal.N₀ R + 7) 5
    ∧ ∀ l ∈ Universal.generators R e, l.toPoly.totalDegree ≤ 5 :=
  ⟨Universal.ideal_ne_top R e, Universal.ringKrullDim_ideal R e, Universal.ideal_isPrimary R e,
    Universal.radical_ideal R e, pointIdeal_isMaximal _, Universal.hasShortPoly_three_iff R e,
    Universal.finrank_quotient_le R e, Universal.span_generators R e,
    Universal.generators_length_le R e, fun _ hl => Universal.generators_degree_le R e hl⟩

/-- **Corollary 5.1, the undecidability**: no algorithm decides, given `e`,
whether `t(I_e) = 3` (mathlib's `ComputablePred`, via `ComputablePred.halting_problem`). -/
theorem cor_halting_family_undecidable :
    ¬ ComputablePred (fun e : ℕ => tinv (haltingIdeal e) = 3) :=
  haltingIdeal_not_computable

/-- **Search bounds, the absence-certificate conclusion.**  The predicate
`tinv (I_e) = 4`, equivalently the absence of a trinomial in the universal family, is not
recursively enumerable.  Consequently there is no computable verifier relation `V(e,c)`
whose existential certificates characterize `tinv (I_e) = 4`.

This statement formalizes the certificate-scheme conclusion of the paper's observation.
It does not introduce a code for normalized supports and therefore does not restate the
preceding busy-beaver comparison for their exponent bounds. -/
theorem obs_search_bounds :
    (¬REPred fun e => tinv (haltingIdeal e) = 4)
    ∧ ¬∃ verifier : ℕ → ℕ → Prop,
      ComputablePred (fun input : ℕ × ℕ => verifier input.1 input.2) ∧
      ∀ e, tinv (haltingIdeal e) = 4 ↔ ∃ certificate, verifier e certificate :=
  ⟨haltingIdeal_tinv_eq_four_not_re, no_computable_absence_certificate_scheme⟩

/-- **A fixed ideal.**  Leave the parameter `E` free in the universal equation and apply
Theorem 4.5 once.  For the resulting single Laurent ideal `J_U = fixedHaltingLaurentIdeal`,
machine `e` halts on input zero exactly when `J_U` contains some normalized trinomial
`τ_d` whose parameter exponent is `d_E = e`.  The universal equation is the sum of squares
of the finite system representing the paper's `U`. -/
theorem obs_fixed_ideal (e : ℕ) :
    (∃ d : Fin (numVars (universalEquationCode MRDP.haltingRel)) → ℤ,
      tau d ∈ fixedHaltingLaurentIdeal
        ∧ d fixedHaltingParameterCoordinate = (e : ℤ)) ↔
      HaltsAtZero (Denumerable.ofNat Code e) :=
  fixedHaltingLaurentIdeal_tau_fiber_iff e

/-! ## Not formalized

* The introductory claims that `t(I) ≤ 1` and `t(I) ≤ 2` are decidable, and that
  containment with a prescribed finite support is decidable.  Their proofs use saturation,
  algorithms for binomial parts, and Gröbner bases not available in the pinned mathlib.
* Remark 4.7's scheme isomorphism over `ℤ` and one executable composite choosing a
  trinomial for each integer zero.  The integer-point bijection and executable guard section
  are included in `remark_geometry`.
* The coefficients and independence observations after Corollary 5.1, and the
  normalized-support exponent-growth part of the search-bounds observation.  Its
  absence-certificate conclusion is `obs_search_bounds`.
* Section 6: Propositions 6.1 and 6.2.  Their difficult cases
  depend on effective theorems of Bilu–Luca and Dong–Shafrir that have not been formalized.
-/

/-! ## Axioms -/

#print axioms tinv_le_iff
#print axioms base_ideal_primary_and_radical
#print axioms lemma_A0_dim
#print axioms lemma_J0_nf_variables
#print axioms lemma_J0_nf_units
#print axioms lemma_J0_nf
#print axioms definition_trinomials
#print axioms prop_shape_i
#print axioms units_of_laurent
#print axioms prop_shape_ii
#print axioms prop_shape_iii
#print axioms definition_A_B
#print axioms lemma_A_B
#print axioms lemma_A_B_graded
#print axioms remark_A_B_socle
#print axioms exponential
#print axioms definition_phi
#print axioms prop_A_Q_eval
#print axioms lemma_quadratic
#print axioms lemma_Pell_guard
#print axioms remark_infinite_forced
#print axioms theorem_main
#print axioms tinv_I_P
#print axioms cor_undecidable_reduction
#print axioms cor_undecidable
#print axioms cor_undecidable_promise
#print axioms remark_geometry
#print axioms universal_polynomial
#print axioms cor_halting_family
#print axioms cor_halting_family_computable_presentations
#print axioms cor_halting_family_uniform
#print axioms cor_halting_family_undecidable
#print axioms obs_search_bounds
#print axioms obs_fixed_ideal

end Trinomial.Paper
