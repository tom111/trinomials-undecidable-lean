import Trinomial.Encoding.Undecidability

/-!
# The computable presentation and the fixed-ring halting family are the same family

`haltingPresentation` is the mathlib-`Computable` sequence used in the encoded
many-one reduction.  `haltingIdeal` is the fixed-ring sequence for which the paper's
algebraic properties were originally recorded.  This file gives the computable
presentation its fixed arity and transports its denoted ideal, by the standard variable
renaming only, into the fixed ring `ℚ[S,T,D₁,…,D_N]`.  The transported ideal is
`haltingIdeal e` itself (`haltingPresentationFixedIdeal_eq_haltingIdeal`); the file also
records directly that it is primary to the displayed maximal ideal, zero-dimensional, and
has the same `3/4` behavior.  The presentation itself has the generator-count and
generator-degree bounds of Corollary 5.1.

This is an extensional computability statement.  It does not make the classically chosen
MRDP relation executable and does not use a data-carrying MRDP theorem.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntPolynomialCode)

/-- The maximal ideal at `(S,T,D)=(1/2,1/2,1)` in the compiler's standard variable
ordering. -/
noncomputable def compilerPointIdeal {n : ℕ} (p : IntPolynomialCode n) :
    Ideal (MvPolynomial (Fin (compiler ⟨n, p⟩).1) ℚ) :=
  Ideal.comap
    (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).toRingEquiv.toRingHom
    (pointIdeal (numVars p))

theorem compilerPointIdeal_isMaximal {n : ℕ} (p : IntPolynomialCode n) :
    (compilerPointIdeal p).IsMaximal := by
  letI : (pointIdeal (numVars p)).IsMaximal := pointIdeal_isMaximal _
  exact Ideal.comap_isMaximal_of_equiv
    (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).toRingEquiv

theorem compiler_isPrimary {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).ideal.IsPrimary := by
  let f := (MvPolynomial.renameEquiv ℚ
    (compilerVarEquiv p)).toRingEquiv.toRingHom
  have hmap : (Ideal.map f (compiler ⟨n, p⟩).ideal).IsPrimary := by
    rw [show Ideal.map f (compiler ⟨n, p⟩).ideal = polyIdeal p from compiler_ideal_map p]
    rw [polyIdeal_eq]
    exact polyReductionIdeal_isPrimary _
  have hcomap := hmap.comap f
  rwa [Ideal.comap_map_of_bijective f
    (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).bijective] at hcomap

theorem radical_compiler {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).ideal.radical = compilerPointIdeal p := by
  let f := (MvPolynomial.renameEquiv ℚ
    (compilerVarEquiv p)).toRingEquiv.toRingHom
  unfold compilerPointIdeal
  calc
    (compiler ⟨n, p⟩).ideal.radical =
        (Ideal.comap f (Ideal.map f (compiler ⟨n, p⟩).ideal)).radical := by
      rw [Ideal.comap_map_of_bijective f
        (MvPolynomial.renameEquiv ℚ (compilerVarEquiv p)).bijective]
    _ = Ideal.comap f (Ideal.map f (compiler ⟨n, p⟩).ideal).radical := by
      rw [Ideal.comap_radical]
    _ = Ideal.comap f (pointIdeal (numVars p)) := by
      rw [show Ideal.map f (compiler ⟨n, p⟩).ideal = polyIdeal p from compiler_ideal_map p,
        polyIdeal_eq, radical_polyReductionIdeal]

theorem radical_compiler_isMaximal {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).ideal.radical.IsMaximal := by
  rw [radical_compiler p]
  exact compilerPointIdeal_isMaximal p

/-- A presentation's listed generators all have total degree at most `bound`. -/
def PresentationGeneratorsDegreeLE (q : IdealPresentation) (bound : ℕ) : Prop :=
  ∀ f ∈ q.generatorPolynomials, f.totalDegree ≤ bound

theorem compiler_generatorPolynomials_length_le {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).generatorPolynomials.length ≤
      Nat.choose (numVars p + 7) 5 := by
  have h := congrArg List.length (rename_generatorPolynomials_compiler p)
  simp only [List.length_map] at h
  rw [h]
  exact generators_length_le (quadraticForms p)

theorem compiler_generatorPolynomials_totalDegree_le {n : ℕ}
    (p : IntPolynomialCode n) {f : MvPolynomial (Fin (compiler ⟨n, p⟩).1) ℚ}
    (hf : f ∈ (compiler ⟨n, p⟩).generatorPolynomials) :
    f.totalDegree ≤ 5 := by
  have hf' : MvPolynomial.rename (compilerVarEquiv p) f ∈
      (generatorsOf p).map PointPoly.toPoly := by
    rw [← rename_generatorPolynomials_compiler p]
    exact List.mem_map_of_mem hf
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp hf'
  have hdegree := generators_totalDegree_le (quadraticForms p) hl
  rw [heq, ← MvPolynomial.renameEquiv_apply,
    MvPolynomial.totalDegree_renameEquiv] at hdegree
  exact hdegree

theorem compiler_presentationGeneratorsDegreeLE {n : ℕ} (p : IntPolynomialCode n) :
    PresentationGeneratorsDegreeLE (compiler ⟨n, p⟩) 5 :=
  fun _ hf => compiler_generatorPolynomials_totalDegree_le p hf

/-- Every presentation in the halting sequence has the same number `2 + N₀` of
variables: `S`, `T`, and the fixed `N₀` variables `Dᵢ`. -/
theorem haltingPresentation_arity (e : ℕ) :
    (haltingPresentation e).1 = 2 + N₀ := by
  rw [haltingPresentation, haltingPolynomialInput, frozenPolynomialInput_eq,
    compiler_arity, Universal.numVars_frozenCode]
  rfl

/-- The computably produced presentation is exactly the compiler output for the paper's
fixed polynomial syntax `U(e,Y)`. -/
theorem haltingPresentation_eq_compiler_frozenCode (e : ℕ) :
    haltingPresentation e =
      compiler ⟨1 + MRDP.haltingRel.aux, frozenCode MRDP.haltingRel e⟩ := by
  rw [haltingPresentation, haltingPolynomialInput, frozenPolynomialInput_eq]

theorem haltingPresentation_isPrimary (e : ℕ) :
    (haltingPresentation e).ideal.IsPrimary := by
  rw [haltingPresentation, haltingPolynomialInput, frozenPolynomialInput_eq]
  exact compiler_isPrimary _

theorem radical_haltingPresentation_isMaximal (e : ℕ) :
    (haltingPresentation e).ideal.radical.IsMaximal := by
  rw [haltingPresentation]
  obtain ⟨n, p⟩ := haltingPolynomialInput e
  exact radical_compiler_isMaximal p

theorem haltingPresentation_generatorPolynomials_length_le (e : ℕ) :
    (haltingPresentation e).generatorPolynomials.length ≤
      Nat.choose (N₀ + 7) 5 := by
  rw [haltingPresentation, haltingPolynomialInput, frozenPolynomialInput_eq]
  simpa [Universal.numVars_frozenCode] using
    compiler_generatorPolynomials_length_le (frozenCode MRDP.haltingRel e)

theorem haltingPresentation_presentationGeneratorsDegreeLE (e : ℕ) :
    PresentationGeneratorsDegreeLE (haltingPresentation e) 5 := by
  rw [haltingPresentation]
  obtain ⟨n, p⟩ := haltingPolynomialInput e
  exact compiler_presentationGeneratorsDegreeLE p

/-- The fixed standard variable ordering of the computable halting presentation. -/
noncomputable def haltingPresentationVarEquiv (e : ℕ) :
    Fin (compiler ⟨1 + MRDP.haltingRel.aux,
      frozenCode MRDP.haltingRel e⟩).1 ≃ Var N₀ :=
  (compilerVarEquiv (frozenCode MRDP.haltingRel e)).trans
    (Equiv.cast (congrArg Var
      (Universal.numVars_frozenCode MRDP.haltingRel e)))

/-- The ideal denoted by `haltingPresentation e`, transported by its standard variable
renaming to the one fixed ring used in Corollary 5.1. -/
noncomputable def haltingPresentationFixedIdeal (e : ℕ) :
    Ideal (MvPolynomial (Var N₀) ℚ) :=
  Ideal.map
    (MvPolynomial.renameEquiv ℚ
      (haltingPresentationVarEquiv e)).toRingEquiv.toRingHom
    (compiler ⟨1 + MRDP.haltingRel.aux,
      frozenCode MRDP.haltingRel e⟩).ideal

/-- **The computable presentation and the fixed-ring family are the same family**: the ideal
denoted by `haltingPresentation e`, transported to `ℚ[S, T, D₁, …, D_{N₀}]` by the standard
variable renaming, is the ideal `I_e = haltingIdeal e` of Corollary 5.1. -/
theorem haltingPresentationFixedIdeal_eq_haltingIdeal (e : ℕ) :
    haltingPresentationFixedIdeal e = haltingIdeal e := by
  have hcomp :
      (MvPolynomial.renameEquiv ℚ (haltingPresentationVarEquiv e)).toRingEquiv.toRingHom
        = ((MvPolynomial.renameEquiv ℚ
              (Equiv.cast (congrArg Var
                (Universal.numVars_frozenCode MRDP.haltingRel e)))).toRingEquiv.toRingHom).comp
            (MvPolynomial.renameEquiv ℚ
              (compilerVarEquiv (frozenCode MRDP.haltingRel e))).toRingEquiv.toRingHom := by
    rw [haltingPresentationVarEquiv, ← MvPolynomial.renameEquiv_trans]
    rfl
  rw [haltingPresentationFixedIdeal, hcomp, ← Ideal.map_map, compiler_ideal_map]
  exact Universal.ideal_eq_map_polyIdeal MRDP.haltingRel e

theorem haltingPresentationFixedIdeal_isPrimary (e : ℕ) :
    (haltingPresentationFixedIdeal e).IsPrimary := by
  let E := (MvPolynomial.renameEquiv ℚ
    (haltingPresentationVarEquiv e)).toRingEquiv
  have h := (compiler_isPrimary
    (frozenCode MRDP.haltingRel e)).comap E.symm.toRingHom
  change (Ideal.comap E.symm
    (compiler ⟨1 + MRDP.haltingRel.aux,
      frozenCode MRDP.haltingRel e⟩).ideal).IsPrimary at h
  rw [Ideal.comap_symm] at h
  simpa [haltingPresentationFixedIdeal, E] using h

theorem haltingPresentationFixedIdeal_ne_top (e : ℕ) :
    haltingPresentationFixedIdeal e ≠ ⊤ :=
  (Ideal.isPrimary_iff.mp (haltingPresentationFixedIdeal_isPrimary e)).1

theorem radical_haltingPresentationFixedIdeal_isMaximal (e : ℕ) :
    (haltingPresentationFixedIdeal e).radical.IsMaximal := by
  let E := (MvPolynomial.renameEquiv ℚ
    (haltingPresentationVarEquiv e)).toRingEquiv
  let q := compiler ⟨1 + MRDP.haltingRel.aux,
    frozenCode MRDP.haltingRel e⟩
  haveI : q.ideal.radical.IsMaximal :=
    radical_compiler_isMaximal (frozenCode MRDP.haltingRel e)
  have hmax : (Ideal.map E q.ideal.radical).IsMaximal :=
    Ideal.map_isMaximal_of_equiv E
  have hrad : (Ideal.map E q.ideal).radical = Ideal.map E q.ideal.radical := by
    simpa only [Ideal.comap_symm] using
      (Ideal.comap_radical E.symm q.ideal).symm
  change (Ideal.map E q.ideal).radical.IsMaximal
  rw [hrad]
  exact hmax

theorem haltingPresentationFixedIdeal_zeroDimensional (e : ℕ) :
    ringKrullDim (MvPolynomial (Var N₀) ℚ ⧸ haltingPresentationFixedIdeal e) = 0 := by
  let E := (MvPolynomial.renameEquiv ℚ
    (haltingPresentationVarEquiv e)).toRingEquiv
  let q := compiler ⟨1 + MRDP.haltingRel.aux,
    frozenCode MRDP.haltingRel e⟩
  let quotientEquiv := Ideal.quotientEquiv
    q.ideal (haltingPresentationFixedIdeal e) E (by
      dsimp only [q, haltingPresentationFixedIdeal, E]
      rfl)
  calc
    ringKrullDim (MvPolynomial (Var N₀) ℚ ⧸ haltingPresentationFixedIdeal e) =
        ringKrullDim (MvPolynomial (Fin q.1) ℚ ⧸ q.ideal) :=
      (ringKrullDim_eq_of_ringEquiv quotientEquiv).symm
    _ = 0 := compiler_zeroDimensional (frozenCode MRDP.haltingRel e)

theorem haltingPresentation_main (e : ℕ) :
    ¬HasShortPoly 2 (haltingPresentation e).ideal
    ∧ (HasShortPoly 3 (haltingPresentation e).ideal ↔ HaltingProblemAtZero e)
    ∧ HasShortPoly 4 (haltingPresentation e).ideal := by
  refine ⟨?_, haltingPresentation_containsAtMostThree_iff e, ?_⟩
  · rw [haltingPresentation]
    obtain ⟨n, p⟩ := haltingPolynomialInput e
    exact (compiler_main_theorem p).1
  · rw [haltingPresentation]
    obtain ⟨n, p⟩ := haltingPolynomialInput e
    exact (compiler_main_theorem p).2.2

open Classical in
theorem haltingPresentationFixedIdeal_tinv (e : ℕ) :
    tinv (haltingPresentationFixedIdeal e) =
      if HaltingProblemAtZero e then 3 else 4 := by
  let E := haltingPresentationVarEquiv e
  let q := compiler ⟨1 + MRDP.haltingRel.aux,
    frozenCode MRDP.haltingRel e⟩
  have h2 := hasShortPoly_map_renameEquiv E q.ideal 2
  have h3 := hasShortPoly_map_renameEquiv E q.ideal 3
  have h4 := hasShortPoly_map_renameEquiv E q.ideal 4
  have hmain := compiler_main_theorem (frozenCode MRDP.haltingRel e)
  change tinv (Ideal.map
    (MvPolynomial.renameEquiv ℚ E).toRingEquiv.toRingHom
      q.ideal) = _
  exact tinv_eq_ite (fun h => hmain.1 (h2.mp h))
    (h3.trans (hmain.2.1.trans (haltingCode_zero_iff e)))
    (h4.mpr hmain.2.2)

private theorem map_pointIdeal_cast {a b : ℕ} (h : a = b) :
    Ideal.map
      (MvPolynomial.renameEquiv ℚ
        (Equiv.cast (congrArg Var h))).toRingEquiv.toRingHom
      (pointIdeal a) = pointIdeal b := by
  subst b
  simp

private theorem map_comap_renameEquiv_trans {a b c : Type*}
    (u : a ≃ b) (v : b ≃ c) (I : Ideal (MvPolynomial b ℚ)) :
    Ideal.map
      (MvPolynomial.renameEquiv ℚ (u.trans v)).toRingEquiv.toRingHom
      (Ideal.comap
        (MvPolynomial.renameEquiv ℚ u).toRingEquiv.toRingHom I) =
      Ideal.map
        (MvPolynomial.renameEquiv ℚ v).toRingEquiv.toRingHom I := by
  let A := (MvPolynomial.renameEquiv ℚ u).toRingEquiv.toRingHom
  let C := (MvPolynomial.renameEquiv ℚ v).toRingEquiv.toRingHom
  have hcomp :
      (MvPolynomial.renameEquiv ℚ (u.trans v)).toRingEquiv.toRingHom = C.comp A := by
    rw [← MvPolynomial.renameEquiv_trans]
    rfl
  rw [hcomp, ← Ideal.map_map]
  rw [Ideal.map_comap_of_surjective A
    (MvPolynomial.renameEquiv ℚ u).surjective]

/-- The radical of the fixed-ring ideal denoted by the computable presentation is
exactly the paper's displayed maximal ideal. -/
theorem radical_haltingPresentationFixedIdeal (e : ℕ) :
    (haltingPresentationFixedIdeal e).radical = pointIdeal N₀ := by
  let p := frozenCode MRDP.haltingRel e
  let a := compilerVarEquiv p
  let h := Universal.numVars_frozenCode MRDP.haltingRel e
  let b : Var (numVars p) ≃ Var N₀ := Equiv.cast (congrArg Var h)
  let E := (MvPolynomial.renameEquiv ℚ
    (haltingPresentationVarEquiv e)).toRingEquiv
  have hE : E = (MvPolynomial.renameEquiv ℚ (a.trans b)).toRingEquiv := by
    rfl
  let q := compiler ⟨1 + MRDP.haltingRel.aux, p⟩
  have hradsource : q.ideal.radical = compilerPointIdeal p := radical_compiler p
  have hradmap : (Ideal.map E q.ideal).radical = Ideal.map E q.ideal.radical := by
    simpa only [Ideal.comap_symm] using
      (Ideal.comap_radical E.symm q.ideal).symm
  rw [haltingPresentationFixedIdeal]
  change (Ideal.map E q.ideal).radical = _
  rw [hradmap, hradsource, compilerPointIdeal]
  rw [hE]
  change Ideal.map
      (MvPolynomial.renameEquiv ℚ (a.trans b)).toRingEquiv
      (Ideal.comap
        (MvPolynomial.renameEquiv ℚ a).toRingEquiv.toRingHom
        (pointIdeal (numVars p))) = _
  calc
    _ = Ideal.map
        (MvPolynomial.renameEquiv ℚ b).toRingEquiv.toRingHom
        (pointIdeal (numVars p)) := by
      simpa only [RingEquiv.toRingHom_eq_coe] using
        map_comap_renameEquiv_trans a b (pointIdeal (numVars p))
    _ = pointIdeal N₀ := map_pointIdeal_cast h

end Trinomial
