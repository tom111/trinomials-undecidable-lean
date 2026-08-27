import Trinomial.Encoding.Compiler
import Trinomial.Universal.HaltingFamily

/-!
# Many-one completeness of the short-polynomial presentation problems

This module assembles the computable compiler and the semidecision procedures into
many-one equivalences with the halting problem.  The compiler writes its output in the
standard variable order `S, T, D₁, …`; the first section identifies the ideal of that
finite presentation with the ideal `I_P` used in Theorem 4.5.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntPolynomialCode evalPolynomial)

/-! ### The ideal denoted by the compiler output -/

namespace StandardPolynomialCode

/-- The inverse of the compiler's standard variable ordering. -/
def standardVarInv (r : ℕ) : Var r → Fin (2 + r)
  | Var.S => Fin.castAdd r 0
  | Var.T => Fin.castAdd r 1
  | Var.D i => Fin.natAdd 2 i

/-- The compiler's standard variable ordering as an equivalence. -/
def standardVarEquiv (r : ℕ) : Fin (2 + r) ≃ Var r where
  toFun := standardVar r
  invFun := standardVarInv r
  left_inv i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> rfl
    · intro j
      simp [standardVarInv]
  right_inv v := by
    cases v <;> simp [standardVarInv]

@[simp] theorem standardVarEquiv_apply (r : ℕ) (i : Fin (2 + r)) :
    standardVarEquiv r i = standardVar r i :=
  rfl

end StandardPolynomialCode

namespace IdealPresentation

/-- The semantic polynomial list represented by a finite presentation. -/
noncomputable def generatorPolynomials (q : IdealPresentation) :
    List (MvPolynomial (Fin q.1) ℚ) :=
  q.rawGenerators.map (RawPolynomial.toPoly q.1)

theorem ideal_eq_span_generatorPolynomials (q : IdealPresentation) :
    q.ideal = Ideal.span {f | f ∈ q.generatorPolynomials} := by
  obtain ⟨n, generators⟩ := q
  rw [ideal, generatorPolynomials, rawGenerators_eq]
  congr 1
  ext f
  simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(generators.get i).map fun term => (term.1, exponentList term.2),
      ⟨generators.get i, List.get_mem generators i, rfl⟩, ?_⟩
    exact RawPolynomial.toPoly_exponentLists (generators.get i)
  · rintro ⟨g, ⟨source, hsource, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hsource
    refine ⟨i, ?_⟩
    exact (RawPolynomial.toPoly_exponentLists (generators.get i)).symm

end IdealPresentation

/-- The variable equivalence from the actual dependent compiler output to the paper's
variable type. -/
def compilerVarEquiv {n : ℕ} (p : IntPolynomialCode n) :
    Fin (compiler ⟨n, p⟩).1 ≃ Var (numVars p) :=
  (Equiv.cast (congrArg Fin (compiler_arity p))).trans
    (StandardPolynomialCode.standardVarEquiv (numVars p))

theorem rename_toPoly_cast {a b : ℕ} {V : Type*} (h : a = b)
    (e : Fin b ≃ V) (polynomial : RawPolynomial) :
    MvPolynomial.rename ((Equiv.cast (congrArg Fin h)).trans e)
        (RawPolynomial.toPoly a polynomial) =
      MvPolynomial.rename e (RawPolynomial.toPoly b polynomial) := by
  subst b
  rfl

theorem rename_generatorPolynomials_compiler {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).generatorPolynomials.map
        (MvPolynomial.rename (compilerVarEquiv p)) =
      (generatorsOf p).map PointPoly.toPoly := by
  rw [IdealPresentation.generatorPolynomials, List.map_map,
    ← rename_toPoly_compilerGenerators p]
  apply List.map_congr_left
  intro polynomial _
  exact rename_toPoly_cast (compiler_arity p)
    (StandardPolynomialCode.standardVarEquiv (numVars p)) polynomial

theorem compiler_ideal_map {n : ℕ} (p : IntPolynomialCode n) :
    Ideal.map
        (MvPolynomial.renameEquiv ℚ
          (compilerVarEquiv p)).toRingEquiv.toRingHom
        (compiler ⟨n, p⟩).ideal =
      polyIdeal p := by
  rw [IdealPresentation.ideal_eq_span_generatorPolynomials, Ideal.map_span]
  have himage :
      (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).toRingEquiv.toRingHom ''
          {f | f ∈ (compiler ⟨n, p⟩).generatorPolynomials} =
        {f | f ∈ (compiler ⟨n, p⟩).generatorPolynomials.map
          (MvPolynomial.rename (compilerVarEquiv p))} := by
    ext f
    simp [eq_comm]
  rw [himage, rename_generatorPolynomials_compiler]
  have hgenerators :
      {f | f ∈ (generatorsOf p).map PointPoly.toPoly} =
        {f | ∃ g ∈ generatorsOf p, f = g.toPoly} := by
    ext f
    simp only [Set.mem_setOf_eq, List.mem_map]
    constructor
    · rintro ⟨g, hg, hgf⟩
      exact ⟨g, hg, hgf.symm⟩
    · rintro ⟨g, hg, hgf⟩
      exact ⟨g, hg, hgf.symm⟩
  rw [hgenerators, span_generatorsOf]

theorem supportCard_renameEquiv {R σ τ : Type*} [CommSemiring R]
    (e : σ ≃ τ) (f : MvPolynomial σ R) :
    (MvPolynomial.rename e f).support.card = f.support.card := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.card_image_of_injective _ (Finsupp.mapDomain_injective e.injective)]

theorem hasShortPoly_map_renameEquiv {R σ τ : Type*} [CommSemiring R]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ R)) (k : ℕ) :
    HasShortPoly k
        (Ideal.map (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom I) ↔
      HasShortPoly k I := by
  constructor
  · rintro ⟨g, hg, hg0, hcard⟩
    obtain ⟨f, hf, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective
        (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom
        (MvPolynomial.renameEquiv R e).surjective).mp hg
    refine ⟨f, hf, ?_, ?_⟩
    · intro hf0
      subst f
      simp at hg0
    · simpa [supportCard_renameEquiv] using hcard
  · rintro ⟨f, hf, hf0, hcard⟩
    refine ⟨MvPolynomial.rename e f, Ideal.mem_map_of_mem _ hf, ?_, ?_⟩
    · exact (MvPolynomial.renameEquiv R e).injective.ne hf0
    · simpa [supportCard_renameEquiv] using hcard

theorem containsTrinomial_map_renameEquiv {R σ τ : Type*} [CommSemiring R]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ R)) :
    (∃ f ∈ Ideal.map (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom I,
        f.support.card = 3) ↔
      ∃ f ∈ I, f.support.card = 3 := by
  constructor
  · rintro ⟨g, hg, hcard⟩
    obtain ⟨f, hf, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective
        (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom
        (MvPolynomial.renameEquiv R e).surjective).mp hg
    exact ⟨f, hf, by simpa [supportCard_renameEquiv] using hcard⟩
  · rintro ⟨f, hf, hcard⟩
    exact ⟨MvPolynomial.rename e f, Ideal.mem_map_of_mem _ hf,
      by simpa [supportCard_renameEquiv] using hcard⟩

/-! ### Correctness of the compiler as a reduction -/

/-- Hilbert's tenth problem on the dependent sparse input syntax. -/
def PolynomialHasIntegralZero (input : PolynomialInput) : Prop :=
  ∃ y : Fin input.1 → ℤ, evalPolynomial input.2 y = 0

theorem exists_supportCard_three_iff_hasShortPoly {R σ : Type*} [CommSemiring R]
    (I : Ideal (MvPolynomial σ R)) (h2 : ¬HasShortPoly 2 I) :
    (∃ f ∈ I, f.support.card = 3) ↔ HasShortPoly 3 I := by
  constructor
  · rintro ⟨f, hf, hcard⟩
    refine ⟨f, hf, ?_, by omega⟩
    intro hf0
    subst f
    simp at hcard
  · rintro ⟨f, hf, hf0, hcard⟩
    refine ⟨f, hf, ?_⟩
    by_contra hne
    have hle : f.support.card ≤ 2 := by omega
    exact h2 ⟨f, hf, hf0, hle⟩

/-- The short-support part of Theorem 4.5, transported back to the finite presentation
returned by `compiler`. -/
theorem compiler_main_theorem {n : ℕ} (p : IntPolynomialCode n) :
    ¬HasShortPoly 2 (compiler ⟨n, p⟩).ideal
    ∧ (HasShortPoly 3 (compiler ⟨n, p⟩).ideal ↔
        ∃ y : Fin n → ℤ, evalPolynomial p y = 0)
    ∧ HasShortPoly 4 (compiler ⟨n, p⟩).ideal := by
  let e := compilerVarEquiv p
  have h2 := hasShortPoly_map_renameEquiv e (compiler ⟨n, p⟩).ideal 2
  have h3 := hasShortPoly_map_renameEquiv e (compiler ⟨n, p⟩).ideal 3
  have h4 := hasShortPoly_map_renameEquiv e (compiler ⟨n, p⟩).ideal 4
  rw [compiler_ideal_map p] at h2 h3 h4
  have hmain := main_theorem_code p
  exact ⟨fun h => hmain.1 (h2.mpr h), h3.symm.trans hmain.2.1,
    h4.mp hmain.2.2⟩

theorem compiler_containsTrinomial_iff (input : PolynomialInput) :
    ContainsTrinomial (compiler input) ↔ PolynomialHasIntegralZero input := by
  obtain ⟨n, p⟩ := input
  rw [ContainsTrinomial, PolynomialHasIntegralZero,
    exists_supportCard_three_iff_hasShortPoly _ (compiler_main_theorem p).1]
  exact (compiler_main_theorem p).2.1

theorem compiler_containsAtMostThree_iff (input : PolynomialInput) :
    ContainsAtMostThree (compiler input) ↔ PolynomialHasIntegralZero input := by
  obtain ⟨n, p⟩ := input
  exact (compiler_main_theorem p).2.1

theorem compiler_tinvThreeProblem_iff (input : PolynomialInput) :
    TinvThreeProblem (compiler input) ↔ PolynomialHasIntegralZero input :=
  compiler_containsTrinomial_iff input

open Classical in
/-- The exact value of `tinv` for every compiler output. -/
theorem compiler_tinv {n : ℕ} (p : IntPolynomialCode n) :
    tinv (compiler ⟨n, p⟩).ideal =
      if ∃ y : Fin n → ℤ, evalPolynomial p y = 0 then 3 else 4 :=
  let h := compiler_main_theorem p
  tinv_eq_ite h.1 h.2.1 h.2.2

open Classical in
theorem compiler_tinv_input (input : PolynomialInput) :
    tinv (compiler input).ideal =
      if PolynomialHasIntegralZero input then 3 else 4 := by
  obtain ⟨n, p⟩ := input
  exact compiler_tinv p

theorem compiler_promise (input : PolynomialInput) :
    TinvThreeOrFour (compiler input) := by
  obtain ⟨n, p⟩ := input
  classical
  rw [TinvThreeOrFour, compiler_tinv]
  split_ifs <;> simp

/-! ### Completeness of fixed-input halting for recursively enumerable predicates -/

open Nat.Partrec
open TrinomialUndecidability.Computability.HaltingEvalnBridge

/-- Mathlib's fixed-input halting problem, transported from program syntax to its natural
number encoding. -/
def HaltingProblemAtZero (e : ℕ) : Prop :=
  HaltsAtZero (Denumerable.ofNat Code e)

/-- Every recursively enumerable predicate many-one reduces to fixed-input halting. -/
theorem REPred.manyOneReducible_haltingProblemAtZero
    {A : Type*} [Primcodable A] {predicate : A → Prop}
    (hpredicate : REPred predicate) :
    predicate ≤₀ HaltingProblemAtZero := by
  let decoded : ℕ →. ℕ := fun code =>
    Part.bind (Encodable.decode₂ A code) fun input =>
      (Part.assert (predicate input) fun _ => Part.some ()).map Encodable.encode
  have hdecoded : Nat.Partrec decoded := by
    exact Partrec.bind_decode₂_iff.mp hpredicate
  let paired : ℕ →. ℕ := fun code => decoded code.unpair.1
  have hpaired : Nat.Partrec paired := by
    simpa [paired] using hdecoded.comp Nat.Partrec.left
  obtain ⟨code, hcode⟩ := Code.exists_code.mp hpaired
  refine ⟨fun input => Encodable.encode (Code.curry code (Encodable.encode input)), ?_, ?_⟩
  · exact (Primrec.encode.comp <|
      Code.primrec₂_curry.comp (Primrec.const code) Primrec.encode).to_comp
  · intro input
    unfold HaltingProblemAtZero HaltsAtZero
    rw [Denumerable.ofNat_encode, Code.eval_curry, hcode]
    simp [paired, decoded, Part.dom_iff_mem]

/-- Recursively enumerable predicates are closed under computable precomposition. -/
theorem REPred.comp_computable {A B : Type*} [Primcodable A] [Primcodable B]
    {predicate : B → Prop} (hpredicate : REPred predicate)
    {f : A → B} (hf : Computable f) :
    REPred fun input => predicate (f input) := by
  unfold REPred at hpredicate ⊢
  exact (hpredicate.comp hf).of_eq fun _ => rfl

/-- Existential projection over natural-number certificates preserves recursive
enumerability for a computable verifier. -/
theorem ComputablePred.re_exists_nat_right {A : Type*} [Primcodable A]
    {relation : A → ℕ → Prop}
    (hrelation : ComputablePred fun input : A × ℕ => relation input.1 input.2) :
    REPred fun input => ∃ certificate, relation input certificate := by
  let decision : DecidablePred (fun input : A × ℕ => relation input.1 input.2) :=
    hrelation.choose
  let test : A → ℕ → Bool := fun input certificate =>
    @decide (relation input certificate) (decision (input, certificate))
  have htest : Computable₂ test := by
    exact hrelation.choose_spec
  have hsearch : Partrec fun input =>
      Nat.rfind fun certificate => Part.some (test input certificate) :=
    Partrec.rfind htest.partrec₂
  apply hsearch.dom_re.of_eq
  intro input
  rw [Nat.rfind_dom]
  simp [test]

/-- The complement of the natural-number fixed-input halting set is not recursively
enumerable. -/
theorem haltingProblemAtZero_complement_not_re :
    ¬REPred fun e => ¬HaltingProblemAtZero e := by
  intro hcomplement
  apply ComputablePred.halting_problem_not_re 0
  have hcodes : REPred fun code : Code =>
      ¬HaltingProblemAtZero (Encodable.encode code) :=
    Trinomial.REPred.comp_computable hcomplement Primrec.encode.to_comp
  exact hcodes.of_eq fun code => by
    simp [HaltingProblemAtZero, HaltsAtZero]

/-! ### A computable Hilbert's tenth instance for fixed-input halting -/

open TrinomialUndecidability.Computability (EffDiophRel)
open TrinomialUndecidability.Computability.EffDiophRel
  (variableExponent addExponent sumSquares squarePolynomial addPolynomial mulPolynomial
    monomialMulPolynomial)

/-- A first-order rendering of `frozenCode R e`.  Its prefix is fixed with `R`; only
the three displayed coefficient functions depend on `e`. -/
def frozenPolynomialInputRaw (R : EffDiophRel 1) (e : ℕ) : PolynomialInputRaw :=
  let xExponent := variableExponent (Fin.castAdd R.aux 0)
  let zero : Fin (1 + R.aux) → ℕ := fun _ => 0
  (1 + R.aux,
    ((sumSquares R.eqs).map fun term => (exponentList term.1, term.2)) ++
      [(exponentList (addExponent xExponent xExponent), 1),
        (exponentList (addExponent xExponent zero), -(e : ℤ)),
        (exponentList (addExponent zero xExponent), -(e : ℤ)),
        (exponentList (addExponent zero zero), (-(e : ℤ)) * (-(e : ℤ)))])

theorem frozenPolynomialInputRaw_eq (R : EffDiophRel 1) (e : ℕ) :
    frozenPolynomialInputRaw R e =
      (polynomialInputToCode ⟨1 + R.aux, frozenCode R e⟩).1 := by
  simp [frozenPolynomialInputRaw, polynomialInputToCode, frozenCode, addPolynomial,
    squarePolynomial, freezeCode, mulPolynomial, monomialMulPolynomial]

/-- The valid first-order code of `frozenCode R e`. -/
def frozenPolynomialInputCode (R : EffDiophRel 1) (e : ℕ) : PolynomialInputCode :=
  ⟨frozenPolynomialInputRaw R e, by
    rw [frozenPolynomialInputRaw_eq]
    exact (polynomialInputToCode ⟨1 + R.aux, frozenCode R e⟩).2⟩

theorem intOfNat_primrec : Primrec fun n : ℕ => (n : ℤ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun _ => rfl

theorem intNegOfNat_primrec : Primrec fun n : ℕ => -(n : ℤ) := by
  apply Primrec.encode_iff.mp
  have hzero : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  exact (Primrec.ite hzero (Primrec.const 0)
    (Primrec.succ.comp <|
      Primrec.nat_mul.comp (Primrec.const 2) Primrec.pred)).of_eq fun n => by
        cases n <;> rfl

theorem intNatSquare_primrec : Primrec fun n : ℕ => (n : ℤ) * (n : ℤ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_mul.comp Primrec.id Primrec.id)).of_eq fun _ => rfl

theorem intNegNatSquare_primrec :
    Primrec fun n : ℕ => (-(n : ℤ)) * (-(n : ℤ)) :=
  intNatSquare_primrec.of_eq fun n => by simp

theorem frozenPolynomialInputRaw_primrec (R : EffDiophRel 1) :
    Primrec (frozenPolynomialInputRaw R) := by
  let xExponent := variableExponent (Fin.castAdd R.aux (0 : Fin 1))
  let zero : Fin (1 + R.aux) → ℕ := fun _ => 0
  let exponentVV := exponentList (addExponent xExponent xExponent)
  let exponentVZ := exponentList (addExponent xExponent zero)
  let exponentZV := exponentList (addExponent zero xExponent)
  let exponentZZ := exponentList (addExponent zero zero)
  have hfirst : Primrec fun _ : ℕ => (exponentVV, (1 : ℤ)) :=
    Primrec.const _
  have hsecond : Primrec fun e : ℕ => (exponentVZ, -(e : ℤ)) :=
    Primrec.pair (Primrec.const _) intNegOfNat_primrec
  have hthird : Primrec fun e : ℕ => (exponentZV, -(e : ℤ)) :=
    Primrec.pair (Primrec.const _) intNegOfNat_primrec
  have hfourth : Primrec fun e : ℕ =>
      (exponentZZ, (-(e : ℤ)) * (-(e : ℤ))) :=
    Primrec.pair (Primrec.const _) intNegNatSquare_primrec
  have htail : Primrec fun e : ℕ =>
      [(exponentVV, (1 : ℤ)), (exponentVZ, -(e : ℤ)),
        (exponentZV, -(e : ℤ)),
        (exponentZZ, (-(e : ℤ)) * (-(e : ℤ)))] :=
    Primrec.list_cons.comp hfirst <| Primrec.list_cons.comp hsecond <|
      Primrec.list_cons.comp hthird <|
        Primrec.list_cons.comp hfourth (Primrec.const [])
  have hpolynomial : Primrec fun e : ℕ =>
      ((sumSquares R.eqs).map fun term => (exponentList term.1, term.2)) ++
        [(exponentVV, (1 : ℤ)), (exponentVZ, -(e : ℤ)),
          (exponentZV, -(e : ℤ)),
          (exponentZZ, (-(e : ℤ)) * (-(e : ℤ)))] :=
    Primrec.list_append.comp (Primrec.const _) htail
  exact (Primrec.pair (Primrec.const (1 + R.aux)) hpolynomial).of_eq fun e => by
    rfl

theorem frozenPolynomialInputCode_primrec (R : EffDiophRel 1) :
    Primrec (frozenPolynomialInputCode R) :=
  Primrec.subtype_mk (hp := polynomialInputRaw_valid_primrec)
    (frozenPolynomialInputRaw_primrec R)

/-- The dependent polynomial input represented by `frozenPolynomialInputCode`. -/
def frozenPolynomialInput (R : EffDiophRel 1) (e : ℕ) : PolynomialInput :=
  polynomialInputOfCode (frozenPolynomialInputCode R e)

theorem frozenPolynomialInput_eq (R : EffDiophRel 1) (e : ℕ) :
    frozenPolynomialInput R e = ⟨1 + R.aux, frozenCode R e⟩ := by
  apply polynomialInputEquivCode.injective
  change polynomialInputToCode (frozenPolynomialInput R e) =
    polynomialInputToCode ⟨1 + R.aux, frozenCode R e⟩
  rw [frozenPolynomialInput, polynomialInputToCode_ofCode]
  apply Subtype.ext
  exact frozenPolynomialInputRaw_eq R e

theorem frozenPolynomialInput_primrec (R : EffDiophRel 1) :
    Primrec (frozenPolynomialInput R) :=
  (Primrec.of_equiv_symm.comp (frozenPolynomialInputCode_primrec R)).of_eq fun _ => rfl

/-- The Hilbert's tenth input associated with a natural-number program code. -/
noncomputable def haltingPolynomialInput (e : ℕ) : PolynomialInput :=
  frozenPolynomialInput MRDP.haltingRel e

theorem haltingPolynomialInput_computable : Computable haltingPolynomialInput :=
  (frozenPolynomialInput_primrec MRDP.haltingRel).to_comp

theorem haltingPolynomialInput_spec (e : ℕ) :
    PolynomialHasIntegralZero (haltingPolynomialInput e) ↔ HaltingProblemAtZero e := by
  rw [haltingPolynomialInput, frozenPolynomialInput_eq]
  exact haltingCode_zero_iff e

/-! ### The three many-one equivalences -/

theorem haltingProblemAtZero_le_polynomialHasIntegralZero :
    HaltingProblemAtZero ≤₀ PolynomialHasIntegralZero :=
  ⟨haltingPolynomialInput, haltingPolynomialInput_computable,
    fun e => (haltingPolynomialInput_spec e).symm⟩

theorem polynomialHasIntegralZero_le_containsTrinomial :
    PolynomialHasIntegralZero ≤₀ ContainsTrinomial :=
  ⟨compiler, compiler_computable, fun input =>
    (compiler_containsTrinomial_iff input).symm⟩

theorem polynomialHasIntegralZero_le_containsAtMostThree :
    PolynomialHasIntegralZero ≤₀ ContainsAtMostThree :=
  ⟨compiler, compiler_computable, fun input =>
    (compiler_containsAtMostThree_iff input).symm⟩

theorem polynomialHasIntegralZero_le_tinvThreeProblem :
    PolynomialHasIntegralZero ≤₀ TinvThreeProblem :=
  ⟨compiler, compiler_computable, fun input =>
    (compiler_tinvThreeProblem_iff input).symm⟩

theorem haltingProblemAtZero_le_containsTrinomial :
    HaltingProblemAtZero ≤₀ ContainsTrinomial :=
  haltingProblemAtZero_le_polynomialHasIntegralZero.trans
    polynomialHasIntegralZero_le_containsTrinomial

theorem haltingProblemAtZero_le_containsAtMostThree :
    HaltingProblemAtZero ≤₀ ContainsAtMostThree :=
  haltingProblemAtZero_le_polynomialHasIntegralZero.trans
    polynomialHasIntegralZero_le_containsAtMostThree

theorem haltingProblemAtZero_le_tinvThreeProblem :
    HaltingProblemAtZero ≤₀ TinvThreeProblem :=
  haltingProblemAtZero_le_polynomialHasIntegralZero.trans
    polynomialHasIntegralZero_le_tinvThreeProblem

theorem containsTrinomial_le_haltingProblemAtZero :
    ContainsTrinomial ≤₀ HaltingProblemAtZero :=
  Trinomial.REPred.manyOneReducible_haltingProblemAtZero containsTrinomial_re

theorem containsAtMostThree_le_haltingProblemAtZero :
    ContainsAtMostThree ≤₀ HaltingProblemAtZero :=
  Trinomial.REPred.manyOneReducible_haltingProblemAtZero containsAtMostThree_re

theorem tinvThreeProblem_le_haltingProblemAtZero :
    TinvThreeProblem ≤₀ HaltingProblemAtZero :=
  Trinomial.REPred.manyOneReducible_haltingProblemAtZero tinvThreeProblem_re

/-- Problem (A), exact trinomial containment in a finitely presented rational ideal, is
many-one equivalent to fixed-input halting. -/
theorem haltingProblemAtZero_manyOneEquiv_containsTrinomial :
    ManyOneEquiv HaltingProblemAtZero ContainsTrinomial :=
  ⟨haltingProblemAtZero_le_containsTrinomial,
    containsTrinomial_le_haltingProblemAtZero⟩

/-- Problem (B), containment of a nonzero polynomial with at most three terms, is
many-one equivalent to fixed-input halting. -/
theorem haltingProblemAtZero_manyOneEquiv_containsAtMostThree :
    ManyOneEquiv HaltingProblemAtZero ContainsAtMostThree :=
  ⟨haltingProblemAtZero_le_containsAtMostThree,
    containsAtMostThree_le_haltingProblemAtZero⟩

/-- Problem (C)'s semidecision language is many-one equivalent to fixed-input halting.
Every input in the forward reduction satisfies `TinvThreeOrFour`, and on that promise the
language is exactly the assertion `tinv = 3`. -/
theorem haltingProblemAtZero_manyOneEquiv_tinvThreeProblem :
    ManyOneEquiv HaltingProblemAtZero TinvThreeProblem :=
  ⟨haltingProblemAtZero_le_tinvThreeProblem,
    tinvThreeProblem_le_haltingProblemAtZero⟩

/-! ### Promise-preserving and zero-dimensional reductions -/

/-- A finite presentation is zero-dimensional when its quotient ring has Krull dimension
zero. -/
def ZeroDimensionalPresentation (q : IdealPresentation) : Prop :=
  ringKrullDim (MvPolynomial (Fin q.1) ℚ ⧸ q.ideal) = 0

theorem compiler_zeroDimensional {n : ℕ} (p : IntPolynomialCode n) :
    ZeroDimensionalPresentation (compiler ⟨n, p⟩) := by
  let variableEquiv := (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).toRingEquiv
  let quotientEquiv := Ideal.quotientEquiv
    (compiler ⟨n, p⟩).ideal (polyIdeal p) variableEquiv
      (compiler_ideal_map p).symm
  unfold ZeroDimensionalPresentation
  calc
    ringKrullDim (MvPolynomial (Fin (compiler ⟨n, p⟩).1) ℚ ⧸
        (compiler ⟨n, p⟩).ideal) =
        ringKrullDim (MvPolynomial (Var (numVars p)) ℚ ⧸ polyIdeal p) :=
      ringKrullDim_eq_of_ringEquiv quotientEquiv
    _ = 0 := (theorem_main p).2.2.1

/-- A many-one reduction whose image is required to lie in a stated promise.  This is the
appropriate formulation for a promise problem because recognizing the promise is not
assumed computable. -/
def ManyOneReducibleInto {A B : Type*} [Primcodable A] [Primcodable B]
    (source : A → Prop) (target promise : B → Prop) : Prop :=
  ∃ reduction, Computable reduction ∧
    (∀ input, source input ↔ target (reduction input)) ∧
    ∀ input, promise (reduction input)

/-- The explicit presentation used by all three forward reductions. -/
noncomputable def haltingPresentation (e : ℕ) : IdealPresentation :=
  compiler (haltingPolynomialInput e)

theorem haltingPresentation_computable : Computable haltingPresentation :=
  compiler_computable.comp haltingPolynomialInput_computable

theorem haltingPresentation_containsTrinomial_iff (e : ℕ) :
    ContainsTrinomial (haltingPresentation e) ↔ HaltingProblemAtZero e :=
  (compiler_containsTrinomial_iff (haltingPolynomialInput e)).trans
    (haltingPolynomialInput_spec e)

theorem haltingPresentation_containsAtMostThree_iff (e : ℕ) :
    ContainsAtMostThree (haltingPresentation e) ↔ HaltingProblemAtZero e :=
  (compiler_containsAtMostThree_iff (haltingPolynomialInput e)).trans
    (haltingPolynomialInput_spec e)

theorem haltingPresentation_tinvThreeProblem_iff (e : ℕ) :
    TinvThreeProblem (haltingPresentation e) ↔ HaltingProblemAtZero e :=
  (compiler_tinvThreeProblem_iff (haltingPolynomialInput e)).trans
    (haltingPolynomialInput_spec e)

theorem haltingPresentation_zeroDimensional (e : ℕ) :
    ZeroDimensionalPresentation (haltingPresentation e) := by
  rw [haltingPresentation]
  obtain ⟨n, p⟩ := haltingPolynomialInput e
  exact compiler_zeroDimensional p

theorem haltingPresentation_promise (e : ℕ) :
    TinvThreeOrFour (haltingPresentation e) :=
  compiler_promise (haltingPolynomialInput e)

open Classical in
theorem haltingPresentation_tinv (e : ℕ) :
    tinv (haltingPresentation e).ideal =
      if HaltingProblemAtZero e then 3 else 4 := by
  rw [haltingPresentation, compiler_tinv_input]
  rw [show PolynomialHasIntegralZero (haltingPolynomialInput e) = HaltingProblemAtZero e
    from propext (haltingPolynomialInput_spec e)]

theorem haltingIdeal_tinv_eq_four_iff (e : ℕ) :
    tinv (haltingIdeal e) = 4 ↔ ¬HaltingProblemAtZero e := by
  classical
  unfold HaltingProblemAtZero
  rw [haltingIdeal_tinv]
  split_ifs <;> simp_all

/-- The absence of a trinomial in the paper's universal ideal family is not recursively
enumerable. -/
theorem haltingIdeal_tinv_eq_four_not_re :
    ¬REPred fun e => tinv (haltingIdeal e) = 4 := by
  intro habsence
  apply haltingProblemAtZero_complement_not_re
  exact habsence.of_eq fun e => haltingIdeal_tinv_eq_four_iff e

/-- There is no computable verifier whose existential certificates recognize absence of a
trinomial in the universal family.  This is the certificate-scheme conclusion of the
paper's search-bounds observation. -/
theorem no_computable_absence_certificate_scheme :
    ¬∃ verifier : ℕ → ℕ → Prop,
      ComputablePred (fun input : ℕ × ℕ => verifier input.1 input.2) ∧
      ∀ e, tinv (haltingIdeal e) = 4 ↔
        ∃ certificate, verifier e certificate := by
  rintro ⟨verifier, hverifier, hspec⟩
  apply haltingIdeal_tinv_eq_four_not_re
  exact (Trinomial.ComputablePred.re_exists_nat_right hverifier).of_eq fun e =>
    (hspec e).symm

/-- Problem (A) remains halting-hard when the reduction is required to output only
zero-dimensional presentations. -/
theorem haltingProblemAtZero_le_containsTrinomial_zeroDimensional :
    ManyOneReducibleInto HaltingProblemAtZero ContainsTrinomial
      ZeroDimensionalPresentation :=
  ⟨haltingPresentation, haltingPresentation_computable,
    fun e => (haltingPresentation_containsTrinomial_iff e).symm,
    haltingPresentation_zeroDimensional⟩

/-- Problem (B) remains halting-hard when the reduction is required to output only
zero-dimensional presentations. -/
theorem haltingProblemAtZero_le_containsAtMostThree_zeroDimensional :
    ManyOneReducibleInto HaltingProblemAtZero ContainsAtMostThree
      ZeroDimensionalPresentation :=
  ⟨haltingPresentation, haltingPresentation_computable,
    fun e => (haltingPresentation_containsAtMostThree_iff e).symm,
    haltingPresentation_zeroDimensional⟩

/-- Problem (C) remains halting-hard with both the `{3,4}` promise and the
zero-dimensional restriction. -/
theorem haltingProblemAtZero_le_tinvThreeProblem_promised_zeroDimensional :
    ManyOneReducibleInto HaltingProblemAtZero TinvThreeProblem
      (fun q => ZeroDimensionalPresentation q ∧ TinvThreeOrFour q) :=
  ⟨haltingPresentation, haltingPresentation_computable,
    fun e => (haltingPresentation_tinvThreeProblem_iff e).symm,
    fun e => ⟨haltingPresentation_zeroDimensional e, haltingPresentation_promise e⟩⟩

end Trinomial
