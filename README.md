# Lean 4 formalization: trinomial containment in polynomial ideals is undecidable

This package formalizes

> Tobias Boege, Anna Hofer, Thomas Kahle,
> *Trinomial containment in polynomial ideals is undecidable*.

It is meant to be read side by side with the paper: the module layout follows the sections
of the paper, every definition and theorem carries a docstring naming the numbered paper
item it formalizes (Lemma 2.1, Theorem 4.5, …), and the vocabulary follows the paper
(glossary below).

**Start with [`Trinomial/Paper.lean`](Trinomial/Paper.lean).**  That file follows the paper's
order and notation.  Formalized claims appear there as Lean statements with short proofs
referring to the development, and the file prints the axioms of each.  A result of the paper
is formalized exactly when its mathematical content appears in one of those statements.
Each docstring records deviations from the paper, and the file ends with a precise list of
what remains unformalized.

## Pins, build, verification

- Lean `4.27.0`, mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900` (`lean-toolchain`,
  `lake-manifest.json`).
- `lake exe cache get && lake build` (from this directory; instant when up to date).
  Re-elaborate one file with `lake env lean Trinomial/<Dir>/<File>.lean`.
- `lake build` prints `#print axioms` for the 34 statements of `Trinomial/Paper.lean`; each
  depends on `propext`, `Classical.choice`, `Quot.sound` only.  There is no `sorry`, no
  custom `axiom`, and no `native_decide` (`grep -rn "sorry\|native_decide\|^axiom" Trinomial`).
- `Trinomial/Examples.lean` runs the executable parts on small inputs at build time.
- The executable definitions `kernelBasis` and `rows` have faster array-based
  implementations attached by `implemented_by`; each implementation is proved equal to the
  definition used in the proofs (`kernelBasisImpl_eq`, `rowsImpl_eq`), so nothing is trusted.

## Layout

| Directory / file | Paper | Contents |
|---|---|---|
| `Trinomial/ShortestPolynomial.lean` | §1 | `HasShortPoly k I` (the problem `t(I) ≤ k`) and `tinv I = t(I)`, for ideals of any `MvPolynomial σ K` |
| `Trinomial/Base/` | §2 | `Laurent N` (`L_N`), `BaseAlgebra N` (`A₀`) and `baseEval` (Lemma 2.2), `baseIdeal N` (`J₀`), its primaryness and radical (`BasePrimary`), `quotBasis` (Lemma 2.1), `tau`, `theta`, `Omega`, Proposition 2.4 (`Shape`, `ShapeClassification` with the Macaulay2-found and Lean-checked certificates `ShapeCert/`, `PrimitiveNormalization`) |
| `Trinomial/Quadrics/` | §3 | `BilinearFormMatrix`, `CubeAlgebra B` (`A_B`), `exp` (`QuadraticAlgebra`); Lemma 3.2 (`CubeAlgebraStructure`, `CubeAlgebraGraded`, `CubeAlgebraPresentation`); its socle calculation (`CubeAlgebraSocle`); `phi G` (`φ_Q`) and Proposition 3.5 (`KernelEvaluation`) |
| `Trinomial/Encoding/` | §4 | `DegreeTwoEquation`, the compiler `StraightLineProgram.ofCode` and `degreeTwoSystem` (Lemma 4.1); `Homogenization`, `PellGuard`, `GuardedSystem`, `GuardSection`, `RationalInfinity` (Lemma 4.2); `Geometry` (Remark 4.7); `reductionIdeal` (`J_P`, `MainLaurent`), `polyReductionIdeal` (`I_P`, `PolynomialSide`, `PolynomialTrinomials`); `ZeroDimensional`, `DegreeDecomposition`, `KernelBasis`, `Generators`, `Colength`, `Counting`; `MainTheorem` (`theorem_main`, `generatorsOf`); `Codes`, `Semidecision`, `Compiler`, and `Undecidability` (primitive-recursive encodings and compiler, finite cofactor certificates, and the many-one equivalences for finite presentations) |
| `Trinomial/Universal/` | §5 | `MRDP` (the halting set is Diophantine; the vendored `TrinomialUndecidability/` supplies the MRDP theorem missing from mathlib), `HaltingFamily` (Corollary 5.1: the generic executable construction `Universal.*` and its instance `haltingIdeal`), `ComputableHaltingFamily` (the same fixed-ring properties for the computable presentation sequence), `FixedIdeal` (the fixed ideal `J_U` and its exponent fibers) |
| `Trinomial/Paper.lean` | all | the formalized claims in paper order, the remaining omissions, and `#print axioms` checks |
| `Trinomial/Examples.lean` | | the executable parts run on the paper's example and on toy inputs |
| `certificates/` | | Macaulay2 scripts: the cofactors behind `ShapeCert/` and the independent cross-check `degree_five_check.m2` of the generator algorithm |

## Paper ↔ Lean comparison

`Paper.*` names are in `Trinomial/Paper.lean`; the other names are the underlying
development.

| Paper | `Trinomial/Paper.lean` | Development |
|---|---|---|
| `t(I)`, the problem `t(I) ≤ k` (§1) | `tinv_le_iff` | `tinv`, `HasShortPoly`, `tinv_eq_succ`, `tinv_eq_ite`; `HasShort` on `L_N` |
| §1 algorithms for `t(I) ≤ 1`, `t(I) ≤ 2`, and a fixed support | — | not formalized; these use saturation, algorithms for binomial parts, and Gröbner bases not supplied by the pinned mathlib |
| `J₀` is primary and `√J₀` is the displayed maximal ideal | `base_ideal_primary_and_radical` | `baseIdeal_isPrimary`, `radical_baseIdeal`, `baseMaximalIdeal_isMaximal` |
| Lemma 2.1 | `lemma_A0_dim` | `ringKrullDim_quotient_baseIdeal`, `quotBasis`, `quotBasis_inl/inr`, `finrank_quotient_baseIdeal`, `baseQuotEquiv : L_N/J₀ ≃ₐ A₀` |
| Lemma 2.2 | `lemma_J0_nf_variables`, `lemma_J0_nf_units`, `lemma_J0_nf` | `baseEval_S/T/D`, `uBe`, `uBe_zpow` (truncated binomial series with `Ring.choose`), `baseMonoUnit_val`, `mem_baseIdeal_iff` (`f ∈ J₀ ⟺ baseEval f = 0`) |
| Definition 2.3 of `τ_d`, `θ_e^{p,q}`, `τ̃_d` | `definition_trinomials` | `tau`, `theta`, `tauPoly`, `tauPoly_eq`, `toLaurent_tauPoly`, `IsPrimitive` |
| Proposition 2.4 (i) | `prop_shape_i` | `no_monomial_in_baseIdeal`, `no_binomial_in_baseIdeal` |
| Proposition 2.4 (ii) | `units_of_laurent` ("up to units of `L_N`": the units are the `c · S^a T^b D^d`, `c ≠ 0`), `prop_shape_ii` (both directions, `e` primitive) | `isUnit_laurent_iff` (via the lexicographic embedding `lexEmb` and `card_support_eq_one_of_mul_eq_one`), `trinomial_in_baseIdeal_primitive`, `tau_mem_baseIdeal`, `theta_mem_baseIdeal`, `supportCard_smul_mono_mul` |
| Proposition 2.4 (iii) | `prop_shape_iii` | `Omega_mem_baseIdeal`, `supportCard_Omega` |
| Definition 3.1 of `A_B`, `A_Q` | `definition_A_B` | `CubeAlgebra`, `BilinearFormMatrix.polar/quad` (`= Matrix.toBilin'`, `polar_eq_toBilin'`) |
| Lemma 3.2 | `lemma_A_B`, `lemma_A_B_graded` | `homogeneousComponent` and its `GradedAlgebra` instance, `IsLocalRing` instance, `nilradical_eq`, `maximalIdeal_eq`, `nilideal_pow_three`, `ker_presentation`, `presentationEquiv` |
| Remark after Lemma 3.2: `soc(A_B) = rad(B) ⊕ ℚζ`; the Gorenstein criterion | `remark_A_B_socle` | `socleIdeal` (the annihilator of `𝔫`), `mem_socleIdeal_iff` (pointwise `soc(A_B) = rad(B) ⊕ ℚζ`), `socleEquivRadicalProd`, `socle_is_zeta_line_iff_nondegenerate`; mathlib has no general Gorenstein predicate, so the stated one-dimensional-socle criterion is formalized |
| `Exp`, `Log` and the three identities | `exponential` | `expNil`, `logNil`, `expEquiv : 𝔫 ≃* 1 + 𝔫`, `exp`, `exp_mul_exp`, `exp_mul_exp_neg` |
| Definition 3.4 of `φ_Q` | `definition_phi` | `phi`, `phi_S/T/D`, `phi_mono`, `algHom_ext_laurent` |
| Proposition 3.5 | `prop_A_Q_eval` | `phi_tau`, `phi_theta`, `tau_mem_ker_phi_iff`, `theta_mem_ker_phi_iff` |
| Lemma 4.1 | `lemma_quadratic` (as an executable compiler) | `StraightLineProgram.ofCode`, `ofCode_computes`, `degreeTwoSystem`, `degreeTwoSystem_solvable_iff`, `shape_ofCode` |
| Lemma 4.2 | `lemma_Pell_guard` (all three bullets) | `gPell`, `gSq`, `guarded`, `homogenize`, `quadAt_homogenize_one`, `noRationalSolutionAtInfinity_homogenizedSystem`, `projection_surjective`, `guardSection` (computable: `pellSolution` from mathlib's `Pell.xn`/`Pell.yn` with `a = 2`, `fourSquares` by search), `guarded_solvable_iff` |
| Remark 4.4 | `remark_infinite_forced` | `tau_three_term_identity`, `infinite_trinomial_mem_of_tau_arithmetic_progression` |
| Theorem 4.5 | `theorem_main` (all bullets + at most `C(N+7,5)` executable generators of degree `≤ 5`) | `generatorsOf`, `span_generatorsOf`, `generators_length_le`, `generators_totalDegree_le`, `ringKrullDim_quotient`, `polyReductionIdeal_isPrimary`, `radical_polyReductionIdeal`, `pointIdeal_isMaximal`, `main_theorem_code`, `OmegaPoly_eq`, `trinomial_in_polyReductionIdeal`, `exists_tauPoly_mem_iff`; universally in the degree-two system: `main_theorem_system` |
| `t(I_P) ∈ {3, 4}` (introduction) | `tinv_I_P` | `tinv_polyIdeal` |
| Corollary 4.6 | `cor_undecidable`, `cor_undecidable_promise` ((C) as a promise problem), `cor_undecidable_reduction` | `PolynomialInput`, `IdealPresentation`, `ContainsTrinomial`, `ContainsAtMostThree`, `TinvThreeProblem` (by definition `ContainsTrinomial`), `TinvThreeOrFour`, `tinvThreeProblem_iff`; primitive-recursive cofactor certificates and `REPred` proofs; `compiler`, `compiler_primrec`; `haltingProblemAtZero_manyOneEquiv_containsTrinomial`, `haltingProblemAtZero_manyOneEquiv_containsAtMostThree`, `haltingProblemAtZero_manyOneEquiv_tinvThreeProblem`; zero-dimensional and promise-preserving forward reductions |
| Remark 4.7 | `remark_geometry` | the actual quotient `TrinomialClasses`, `trinomialClassesEquivGuarded`, `guardProjection`, `guardSolutionSection`, `guardProjection_infinite_fibers`, `degreeTwoSolutionsEquivZeros`, `geometry_input_coordinate`, `not_all_tau_mem_of_arithmetic_progression` |
| eq. (8) | `universal_polynomial` | `MRDP.haltingRel`, `haltingRel_spec`, `frozenCode`, `frozenCode_zero_iff`, `haltingCode` |
| Corollary 5.1 | `cor_halting_family`, `cor_halting_family_computable_presentations`, `cor_halting_family_uniform` (for any relation `R`), `cor_halting_family_undecidable` | `Universal.ideal/generators/N₀/M₀`, `haltingIdeal`; `haltingPresentation`, its computability, fixed arity and generator bounds; `haltingPresentationFixedIdeal`, equal to `haltingIdeal e` (`haltingPresentationFixedIdeal_eq_haltingIdeal`, via `Universal.ideal_eq_map_polyIdeal` and `map_idealOfSystem_cast`), its primaryness, exact radical, zero-dimensionality, and `3/4` behavior; `pointIdeal_isMaximal`; `haltingIdeal_not_computable` |
| Observation “A fixed ideal” | `obs_fixed_ideal` | `universalEquationCode`, `fixedLaurentIdeal`, `fixedParameterCoordinate`, `fixedHaltingLaurentIdeal_tau_fiber_iff` |
| Search bounds, absence-certificate conclusion | `obs_search_bounds` | `haltingIdeal_tinv_eq_four_not_re`, `no_computable_absence_certificate_scheme` |
| Observations coefficients, normalized-support exponent bounds, independence | — | not formalized |
| Propositions 6.1 and 6.2 (§6) | — | not formalized; their proofs use the effective theorems of Bilu–Luca and Dong–Shafrir, respectively |

### What "formalized" means here, and what is not formalized

- A paper result counts as formalized only if the Lean *statement* expresses it.  No
  statement has the form "there exists an ideal (algorithm, generating set) with property
  `P`": the objects are always the explicitly defined `generatorsOf`, `haltingIdeal`,
  `haltingPresentation`, and so on, and the statements are universally quantified over
  their inputs.  Existential quantifiers occur inside statements, for the paper's own
  existential content (an integral zero of `P`, a trinomial in `I_P`) and for the converse
  direction of the many-one equivalences (`cor_undecidable_promise`, `obs_search_bounds`),
  where only the forward reduction is exhibited.
- "There is an algorithm" means an executable `def` together with a correctness theorem:
  `StraightLineProgram.ofCode`, `degreeTwoSystem`, `guarded`, `homogenizedSystem`,
  `guardSection`, `kernelBasis`, `generators`, `generatorsOf`, `Universal.generators` are
  all plain definitions, none of them `noncomputable`, and they evaluate:
  `Trinomial/Examples.lean` runs them on small inputs at build time, and `generatorsOf` on
  the smallest instance in about a minute (that call is left commented out there to keep
  the build fast).  `#print axioms` gives `propext, Quot.sound` for `ofCode`,
  `degreeTwoSystem` and `guarded`; the other six also report `Classical.choice`, which
  enters through proof arguments carried inside the definitions.  Those proofs are erased
  by compilation, which is why the definitions still run.  The encoded presentation
  compiler `compiler` additionally has the mathlib theorem `compiler_computable`.
- **Corollary 4.6** has explicit encoded presentations and recursively enumerable
  predicates for all three questions, proved by primitive-recursive sparse cofactor
  certificates in `Semidecision.lean`.  For the promise question (C), the total predicate
  `TinvThreeProblem` is by definition `ContainsTrinomial`; `TinvThreeOrFour` is the promise,
  `TinvThreeProblem` agrees with `t(I)=3` on promised inputs (`tinvThreeProblem_iff`), and
  `Paper.cor_undecidable_promise` states (C) as a promise problem with `t(I)=3` spelled out.
  The standard-coordinate presentation compiler in `Compiler.lean` is primitive recursive
  and its decoded generators agree with `generatorsOf` after the explicit variable
  equivalence.  `Undecidability.lean` proves all three many-one equivalences with fixed-input
  halting.  Its explicit forward map produces only zero-dimensional presentations and also
  satisfies the `{3,4}` promise for problem (C).
- **Corollary 5.1**: the construction is an executable function `Universal.generators`
  of an effective Diophantine relation `R` (a list of integer polynomials) and of `e`; the
  fixed relation `MRDP.haltingRel` representing the paper's universal polynomial `U` (which
  the paper also does not exhibit) is obtained classically (`Classical.choose`) from the
  proof `MRDP.dioph_haltingSet` that the halting set is Diophantine (mathlib supplies the
  predicate `Dioph`; the proof is in `Universal/MRDP.lean` and the vendored
  `TrinomialUndecidability/`), so `haltingGenerators e` cannot be evaluated.  The separate
  statement `cor_halting_family_computable_presentations` names the encoded
  finite-presentation map `haltingPresentation`, proves it `Computable` in mathlib's
  extensional sense, and proves that the ideal it denotes, transported to the fixed ring,
  is `haltingIdeal e` itself (`haltingPresentationFixedIdeal_eq_haltingIdeal`).  This does
  not turn its classically chosen closed data into an evaluable term.  The generator
  bounds are those of the paper: `≤ C(N₀+7, 5)` generators of total degree `≤ 5`.  Lean also records the colength bounds
  `≤ min{(N₀+5) + M₀(N₀+3), C(N₀+6, 4)}`.  The parameter `E` is kept as a variable and
  pinned by a square (`frozenCode`), which adds one variable.
- **Remark 4.7** defines the actual quotient of trinomials by nonzero scalar and
  Laurent-monomial multiplication.  It proves the bijection with normalized `τ_d`, both
  point-set bijections in the paper, the guard projection and executable section,
  coordinate tracking, infinitude of every guard fiber, and the final exclusion of
  nonconstant arithmetic progressions.  The stronger assertion that the straight-line
  program gives a scheme isomorphism over `ℤ` is not formalized.  Nor is the composite
  choice of one trinomial for each zero packaged as one executable definition.
- **A fixed ideal** is formalized for the single sum-of-squares equation representing the
  effective universal relation, with `E` left free and its exponent coordinate tracked.
- The halting set is mathlib's: machine `e` is the code `Denumerable.ofNat Code e` and
  "halts on input `0`" is `(Code.eval c 0).Dom` (`HaltsAtZero`).
- The introductory algorithms for monomials, binomials, and fixed supports are not
  formalized.  The first is an elementary saturation criterion.  The latter two invoke
  external computer-algebra results not present in mathlib.
- Section 6 is not formalized: the effective Bilu–Luca and Dong–Shafrir theorems on which
  the proofs depend have no Lean implementation here or in the pinned mathlib.

## Glossary: Lean names ↔ paper notation

| Lean | Paper |
|---|---|
| `Laurent N`, `Exponent N`, `mono x`, `monoUnit x`, `S N`, `T N`, `D i` | `L_N`, exponent vectors `(a, b, d)`, the monomials `S^a T^b D^d` (as units), the variables |
| `HasShort k I`, `HasShortPoly k I`, `tinv I` | `t(I) ≤ k` (Laurent, resp. polynomial ideal), `t(I)` |
| `lexVec x`, `lexEmb N`, `isUnit_laurent_iff` | the exponent vector `(a, b, d₁, …, d_N) ∈ ℤ^{N+2}`, the exponent lattice ordered lexicographically, "the units of `L_N` are the `c · S^a T^b D^d`" (Proposition 2.4, "up to units") |
| `Var N`, `MvPolynomial (Var N) ℚ`, `toLaurent N` | the variables `S, T, D_i` of `ℚ[S, T, D]`, the ring, its embedding into `L_N` |
| `baseIdeal N`, `baseIdealGens N` | `J₀` and its generators (eq. (1); all ordered pairs `(i, j)`) |
| `BaseAlgebra.residueAlgHom`, `basePointEval`, `baseMaximalIdeal` | the residue map `A₀ → ℚ`, evaluation at `(S,T,D)=(1/2,1/2,1)`, and the displayed maximal ideal `√J₀` |
| `BaseAlgebra N`, `.b0 … .b4`, `.c`, `B`, `C i`, `baseEval`, `baseQuotEquiv`, `quotBasis` | `A₀` with basis `1, B, …, B⁴, C₁, …, C_N`, `B = S−T`, `C_i = D_i−1`, the normal-form map of Lemma 2.2, `L_N/J₀ ≃ A₀`, the basis of Lemma 2.1 |
| `zchoose a k`, `uBe N ε`, `uD i`, `baseMonoUnit x`, `w1 … w4` | `(a choose k)` for `a ∈ ℤ` (`Ring.choose`), the units `1 + εB`, `1 + C_i`, the residue of `S^a T^b D^d`, the `B^k`-coefficients of `(1+B)^a (1−B)^b` (the polynomials in the equations `(k=1)…(k=4)` of the proof of Proposition 2.4) |
| `NilData`, `NilData.lift` | the universal property of `A₀` (used to prove `J₀ = ker baseEval`) |
| `tau d`, `theta e p q`, `Omega N`, `tauPoly d`, `OmegaPoly N` | `τ_d`, `θ_e^{p,q}`, `Ω`, the clearing `τ̃_d`, `Ω` as a polynomial |
| `IsPrimitive e` | `e ∈ ℤ^N` primitive |
| `IsUnitMultipleOfFamily g`, `IsUnitMultipleOfFamilyPrimitive g` | `g` is a unit times `τ_d` or times `θ_e^{p,q}` (`e ≠ 0`, resp. `e` primitive) |
| `lam c x`, `ShapeCert.eqs`, `elimination_of_ne_zero`, `solution_table` | `λ = c 2^{−a−b}`, the equations `(k=0)…(k=4)`, their elimination (Macaulay2 certificates checked by `linear_combination`), the finite solution table of the proof of Proposition 2.4 |
| `BilinearFormMatrix ι`, `.b`, `.polar`, `.quad` | the matrix `(b_ij) = (B(v_i, v_j))` of a symmetric bilinear form on `V = ℚ^ι`, `B(x, y)`, `Q(x) = B(x, x)` (`Matrix.toBilin'`, `LinearMap.BilinMap.toQuadraticMap`) |
| `CubeAlgebra B`, `.scalar/.vector/.socle`, `ofVector`, `zeta`, `scalarHom`, `nilideal`, `onePlusNil` | `A_B = ℚ ⊕ V ⊕ ℚζ`, its components, `V ↪ A_B`, `ζ`, the residue map `A_B → ℚ`, `𝔫`, `1 + 𝔫` |
| `BilinearFormMatrix.radical`, `CubeAlgebra.socleIdeal`, `socleEquivRadicalProd` | `rad(B)`, `soc(A_B)`, and `soc(A_B) ≃ rad(B) ⊕ ℚζ` |
| `degreeZero`, `degreeOne`, `degreeTwo`, `homogeneousComponent B`, `gradedDecompose B` | the grading `A_B = ℚ ⊕ V ⊕ ℚζ` in degrees `0`, `1`, `2`, with zero components in degrees at least `3` |
| `exp`, `expUnit`, `expNil`, `logNil`, `expNilUnit`, `expEquiv` | `Exp(v)` for `v ∈ V` (as a unit), `Exp`, `Log` on `𝔫`, `Exp : 𝔫 ≃ 1 + 𝔫` |
| `presentation B`, `relationIdeal B`, `presentationEquiv B` | `ℚ[X₁, …, Xₙ, Z] → A_B`, the ideal `I`, `A_B ≅ ℚ[X, Z]/I` of Lemma 3.2 |
| `homVec d t`, `expVec x`, `ratCast d`, `quadAt G d t` | `(d, t) ∈ V = ℚ^N × ℚv₀`; the point `d + (a−b)v₀` of `S^a T^b D^d`; `d ∈ ℤ^N` read in `ℚ^N`; `Q(d, t)` |
| `phi G`, `phiMonoUnit` | `φ_Q`, `φ_Q(S^a T^b D^d)` as a unit |
| `DegreeTwoEquation r`, `.eval`, `.rename`, `.homogenize`, `Solves z L` | an equation `f_i` of degree at most two in `r` variables, its value, renaming of variables, its homogenization `g_i`, "`z` is a common zero of the system `L`" |
| `eqConst`, `eqAdd`, `eqMul`, `eqZero`, `eqCopy`, `eqScale` | the gates `x = a`, `x = y + z`, `x = y·z`, `x = 0`, `x = y`, `x = c·y` of a straight line program |
| `StraightLineProgram n`, `.Computes`, `ofCode`, `degreeTwoSystem p` | a straight line program with `n` inputs (§4), "the output variable is forced to equal `P(y)`", the compiler, the system of Lemma 4.1 |
| `StraightLineProgram.Determines` | every auxiliary coordinate of the compiled system is determined by the input coordinates |
| `IntPolynomialCode n`, `evalPolynomial`, `codeToMv` | the sparse syntax of `P ∈ ℤ[y₁…yₙ]` (list of (exponent vector, coefficient)), its value, the polynomial it denotes |
| `vh`, `vk`, `vu`, `gPell`, `gSq`, `guarded L`, `homogenizedSystem L'` | the variables `h, k, u₁…u₄`, the guards `g_{m+1}`, `g_{m+2}`, the guarded system, the forms `g_1, …, g_{m+2}` of Lemma 4.2 |
| `pell3 n`, `pellSolution B`, `fourSquares n`, `guardSection z` | the Pell solutions generated by `2+√3` (mathlib's `Pell.xn`/`Pell.yn`, `a = 2`), the first with `h ≥ B`, a four-squares witness, the section `s : X → X̂₁` |
| `IntegralSolutions L`, `GuardedSolutionSet p`, `DegreeTwoSolutionSet p`, `PolynomialZeroSet p` | `X(L)`, `X̂₁`, `X`, and `Y = {y ∈ ℤⁿ : P(y) = 0}` of Remark 4.7 |
| `TermRelated`, `TrinomialsInReductionIdeal p`, `TrinomialClasses p` | multiplication by a nonzero scalar and Laurent monomial, the three-term elements of `J_P`, and their quotient `𝒯(J_P)` |
| `NormalizedTauTrinomials p`, `normalizedTauClass p`, `trinomialClassesEquivNormalized p`, `trinomialClassesEquivGuarded p` | normalized representatives `τ_d`, their classes, uniqueness of the representatives, and the left bijection `𝒯(J_P) ≃ X̂₁` |
| `guardProjection L`, `guardSolutionSection L`, `guardFiberPoint z m` | the map `π : X̂₁ → X`, its computable section, and the Pell-indexed points proving its fibers infinite |
| `degreeTwoInput p`, `degreeTwoSolutionsEquivZeros p`, `reductionInputCoordinate p i` | projection `X → Y`, the right bijection of Remark 4.7, and the exponent coordinate corresponding to `y_i` |
| `NoIntegralSolutionAtInfinity Q`, `NoRationalSolutionAtInfinity Q` | the origin is the only integral (resp. rational, as in the paper) solution of `Q_1 = ⋯ = Q_M = 0` with `t = 0`; equivalent by clearing denominators |
| `reductionIdeal Q`, `polyReductionIdeal Q` | `J_P = J₀ ∩ ⋂ ker φ_{Q_i}`, `I_P = J_P ∩ ℚ[S, T, D]`, for a family `Q` of quadratic forms |
| `idealOfSystem L`, `polyIdeal p`, `quadraticForms p`, `numVars p` | `I_P` from a degree-two system `L`, resp. from the syntax `p` of `P`; the forms `Q_1, …, Q_M`; the number `N` |
| `pointIdeal N`, `pointGen N`, `basePoint N`, `pointMonomial N e` | `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`, its generators `s, t, c_i`, the point `(½, ½, 1, …, 1)`, the product `s^a t^b c^γ` |
| `psi Q`, `quotientEmbedding Q`, `finrank_target` | `ψ : ℚ[S,T,D] → A₀ × ∏ A_{Q_i}` (proof of Corollary 5.1), the embedding of the quotient, `C = (N+5) + M(N+3)` |
| `lowDegreeSpan N`, `lowMonomials N`, `exponentsLE/EQ` | `W₄`, the products `s^a t^b c^γ` with `a+b+|γ| ≤ 4`, the exponent lists (proof of Theorem 4.5) |
| `rowEval`, `rowForm`, `eliminate`, `kernelBasis rows` | "linear algebra on the residues": a linear condition, one elimination step, a spanning set of the solutions of a linear system |
| `toArr`, `ofArr`, `kernelBasisA`, `kernelBasisImpl`; `CubeAlgebra.store`, `BaseAlgebra.store`, `matTable`, `mulWith`, `cubeImageWith`, `rowsImpl` | the array-based implementations of `kernelBasis` and `rows` (proved equal) |
| `PointPoly N`, `.toPoly`, `.display`, `rows Q`, `generators Q`, `generatorsOf p` | a polynomial written in `s, t, c`, its value in `ℚ[S,T,D]`, a printable form; the linear system and the computed generator list of `I_P` (Theorem 4.5) |
| `PolynomialInput`, `IdealPresentation` | encoded inputs `Σ n, IntPolynomialCode n` and finite presentations by rational sparse polynomials in `n` standard variables |
| `PolynomialInputCode`, `IdealPresentationCode`, `polynomialInputEquivCode`, `idealPresentationEquivCode` | nondependent list encodings with primitive-recursive exponent-length invariants and their equivalences with the paper-facing input types |
| `SignedCode`, `RationalCode`, `CodedPolynomial` | first-order signed-integer, positive-denominator rational, and sparse-polynomial codes used by the semidecision procedures |
| `ContainsTrinomial`, `ContainsAtMostThree`, `TinvThreeProblem`; `TrinomialCertificate`, `AtMostThreeCertificate` | the three presentation problems and their primitive-recursive finite cofactor certificates; the third agrees with `t(I)=3` under `TinvThreeOrFour` |
| `PolynomialHasIntegralZero`, `HaltingProblemAtZero`, `haltingPolynomialInput`, `haltingPresentation` | Hilbert's tenth problem on encoded sparse inputs, the natural-number fixed-input halting set, its computable polynomial instance, and the finite ideal presentation used in the reductions |
| `PresentationGeneratorsDegreeLE`, `haltingPresentationVarEquiv`, `haltingPresentationFixedIdeal` | the generator-degree bound, the standard variable renaming, and the ideal denoted by `haltingPresentation e` in the fixed ring of Corollary 5.1 |
| `compilerPointIdeal` | the displayed maximal ideal in the compiler's standard variable order |
| `compilerVarEquiv`, `compiler_ideal_map`, `compiler_main_theorem` | the standard-variable equivalence, equality of the presented compiler ideal with `I_P`, and Theorem 4.5's short-support gap on the encoded presentation |
| `ZeroDimensionalPresentation`, `ManyOneReducibleInto` | the zero-dimensional input restriction and a many-one reduction required to land inside a promise |
| `haltingProblemAtZero_manyOneEquiv_containsTrinomial`, `haltingProblemAtZero_manyOneEquiv_containsAtMostThree`, `haltingProblemAtZero_manyOneEquiv_tinvThreeProblem` | the many-one equivalences of Corollary 4.6, for problems (A), (B), and (C) |
| `REPred.comp_computable`, `REPred.manyOneReducible_haltingProblemAtZero`, `ComputablePred.re_exists_nat_right` | closure and completeness lemmas used to reduce recursively enumerable presentation predicates to fixed-input halting and to rule out absence certificates |
| `frozenPolynomialInputRaw`, `frozenPolynomialInputCode`, `frozenPolynomialInput`, `haltingPolynomialInput` | the first-order and dependent encodings of `U(e,Y)` used in the computable reduction from halting to Hilbert's tenth problem |
| `haltingIdeal_tinv_eq_four_not_re`, `no_computable_absence_certificate_scheme` | the non-r.e. absence predicate and the certificate-scheme conclusion of the search-bounds observation |
| `MRDP.haltingRel`, `haltingPoly e`, `frozenCode R e`, `freezeCode i e`, `haltingCode e` | the universal relation `U` (as a list of integer polynomials), `U(e, Y)` as a polynomial, its syntax for any relation `R` (frozen-parameter form, a sum of squares with `(X₀ − e)²`), the syntax `X_i − e`, the syntax at `haltingRel` |
| `universalEquationCode R`, `fixedLaurentIdeal R`, `fixedParameterCoordinate R` | the sum-of-squares equation for `U(E,Y)`, the fixed Laurent ideal `J_U`, and its parameter exponent `d_E` |
| `fixedHaltingLaurentIdeal`, `fixedHaltingParameterCoordinate` | `J_U` and `d_E` for the universal relation encoding the halting set |
| `Universal.k₀ R`, `N₀ R`, `M₀ R`, `system R e`, `forms R e`, `ideal R e`, `generators R e` | the constants of Corollary 5.1 (auxiliary variables, `N`, `M`), the system of Lemma 4.1 for `P_e` in the fixed coordinates, the forms, `I_e`, its presentation, for any relation `R` |
| `N₀`, `M₀`, `haltingIdeal e`, `haltingGenerators e` | the same at `R = haltingRel`: `I_e` and "the computed presentation of `I_e`" |
| `HaltsAtZero c` | "`M_e(0)` halts" for the code `c = Denumerable.ofNat Code e` |

## Citing

The mathematics is the paper; cite it:

```bibtex
@unpublished{BoegeHoferKahle2026,
  author = {Boege, Tobias and Hofer, Anna and Kahle, Thomas},
  title  = {Trinomial containment in polynomial ideals is undecidable},
  year   = {2026},
}
```

To point at the formalization itself, add this repository.

## License

Apache License 2.0 (`LICENSE`), the license of mathlib, on which this development depends.
