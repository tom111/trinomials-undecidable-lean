import TrinomialUndecidability.Computability.MathlibDiophantinePrimrec

/-!
# Finite traces and the bounded-step boundary for primitive recursion

This module adds an explicit finite list trace to `MathlibDiophantinePrimrec` and proves its
length, base, transition, and final-value laws.  It also proves that one individual beta-coded
transition is Diophantine.  It isolates bounded universal quantification of those
transitions as the interface later discharged by the regular-cipher compiler.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineRecursionTrace

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

open TrinomialUndecidability.Computability.MathlibDiophantinePairing
open TrinomialUndecidability.Computability.MathlibDiophantinePrimrec
open TrinomialUndecidability.Computability.MathlibDiophantineSequence

/-- The complete finite recursion trace, including both the base value and the value at `length`. -/
def recursionTrace (base step : ℕ → ℕ) (parameter length : ℕ) : List ℕ :=
  List.ofFn fun index : Fin (length + 1) ↦ recursionValue base step parameter index

@[simp]
theorem recursionTrace_length (base step : ℕ → ℕ) (parameter length : ℕ) :
    (recursionTrace base step parameter length).length = length + 1 := by
  simp [recursionTrace]

/-- Every trace entry is the corresponding recursively generated value. -/
theorem recursionTrace_getElem (base step : ℕ → ℕ) (parameter length index : ℕ)
    (hindex : index < length + 1) :
    (recursionTrace base step parameter length)[index]'(by
      simpa [recursionTrace] using hindex) = recursionValue base step parameter index := by
  unfold recursionTrace
  rw [List.getElem_ofFn]

/-- The first trace entry is the primitive-recursion base value. -/
@[simp]
theorem recursionTrace_base (base step : ℕ → ℕ) (parameter length : ℕ) :
    (recursionTrace base step parameter length)[0]'(by
      simp [recursionTrace]) =
      base parameter := by
  rw [recursionTrace_getElem base step parameter length 0 (by omega)]
  rfl

/-- Every noninitial trace entry is obtained from its predecessor by the packed step function. -/
theorem recursionTrace_step (base step : ℕ → ℕ) (parameter length index : ℕ)
    (hindex : index < length) :
    (recursionTrace base step parameter length)[index + 1]'(by
      simp [recursionTrace]
      omega) =
      step (Nat.pair parameter
        (Nat.pair index ((recursionTrace base step parameter length)[index]'(by
          simp [recursionTrace]
          omega)))) := by
  rw [recursionTrace_getElem base step parameter length (index + 1) (by omega),
    recursionTrace_getElem base step parameter length index (by omega)]
  rfl

/-- The last trace entry is the value of the recursion at the requested length. -/
@[simp]
theorem recursionTrace_final (base step : ℕ → ℕ) (parameter length : ℕ) :
    (recursionTrace base step parameter length)[length]'(by
      simp [recursionTrace]) =
      recursionValue base step parameter length := by
  rw [recursionTrace_getElem base step parameter length length (by omega)]

/-- The final trace entry agrees exactly with the unary paired recursion function. -/
theorem recursionTrace_final_paired (base step : ℕ → ℕ) (input : ℕ) :
    (recursionTrace base step
      (Nat.unpair input).1 (Nat.unpair input).2)[(Nat.unpair input).2]'(by
        simp [recursionTrace]) =
      primitiveRecursion base step input := by
  rw [recursionTrace_final]
  rfl

/-- One beta code simultaneously records the base, every bounded step, and the final value of a
finite primitive recursion. -/
theorem exists_recursionTraceCode (base step : ℕ → ℕ) (parameter length : ℕ) :
    ∃ code,
      sequenceAccessor code 0 = base parameter ∧
        (∀ index < length,
          sequenceAccessor code (index + 1) =
            step (Nat.pair parameter
              (Nat.pair index (sequenceAccessor code index)))) ∧
        sequenceAccessor code length = recursionValue base step parameter length := by
  obtain ⟨code, hbase, hfinal, hsteps⟩ :=
    exists_betaComputation base step parameter length
  exact ⟨code, hbase, hsteps, hfinal⟩

/-! ## Diophantineness of one transition -/

/-- The arithmetic relation asserted at one index of a beta-coded primitive-recursion trace. -/
def BetaStep (step : ℕ → ℕ) (parameter code index : ℕ) : Prop :=
  sequenceAccessor code (index + 1) =
    step (Nat.pair parameter (Nat.pair index (sequenceAccessor code index)))

/-- Variable order for a single transition is `(parameter, code, index)`. -/
def betaStepSet (step : ℕ → ℕ) : Set (Vector3 ℕ 3) :=
  {values | BetaStep step (values &0) (values &1) (values &2)}

/-- A single beta-coded transition is Diophantine whenever the packed step function is. -/
theorem betaStepSet_dioph {step : ℕ → ℕ} (hstep : NatDiophFn step) :
    Dioph (betaStepSet step) := by
  have hcurrent :
      DiophFn fun values : Vector3 ℕ 3 ↦
        sequenceAccessor (values &1) (values &2) :=
    Dioph.diophFn_comp sequenceAccessor_diophFn
      [fun values : Vector3 ℕ 3 ↦ values &1, fun values ↦ values &2]
      ⟨D&1, D&2⟩
  have hnext :
      DiophFn fun values : Vector3 ℕ 3 ↦
        sequenceAccessor (values &1) (values &2 + 1) :=
    Dioph.diophFn_comp sequenceAccessor_diophFn
      [fun values : Vector3 ℕ 3 ↦ values &1, fun values ↦ values &2 + 1]
      ⟨D&1, (D&2) D+ D.1⟩
  have hinnerPair :
      DiophFn fun values : Vector3 ℕ 3 ↦
        Nat.pair (values &2) (sequenceAccessor (values &1) (values &2)) :=
    natPair_comp_diophFn (D&2) hcurrent
  have hstepInput :
      DiophFn fun values : Vector3 ℕ 3 ↦
        Nat.pair (values &0)
          (Nat.pair (values &2) (sequenceAccessor (values &1) (values &2))) :=
    natPair_comp_diophFn (D&0) hinnerPair
  unfold NatDiophFn at hstep
  have hstepValue :
      DiophFn fun values : Vector3 ℕ 3 ↦
        step (Nat.pair (values &0)
          (Nat.pair (values &2) (sequenceAccessor (values &1) (values &2)))) :=
    Dioph.diophFn_comp hstep
      [fun values : Vector3 ℕ 3 ↦
        Nat.pair (values &0)
          (Nat.pair (values &2) (sequenceAccessor (values &1) (values &2)))]
      hstepInput
  exact Dioph.ext (hnext D= hstepValue) fun _ ↦ Iff.rfl

/-- Bounded transition validity with visible variable order `(parameter, length, code)`. -/
def boundedBetaStepsSet (step : ℕ → ℕ) : Set (Vector3 ℕ 3) :=
  {values | ∀ index < values &1, BetaStep step (values &0) (values &2) index}

/-- The bounded-universal interface isolated after individual transitions have been proved
Diophantine; `MathlibDiophantineBounded` supplies its unconditional instance. -/
def BoundedBetaStepsAreDiophantine : Prop :=
  ∀ {step : ℕ → ℕ}, NatDiophFn step → Dioph (boundedBetaStepsSet step)

/-- The base and final-value equations, with variable order
`(parameter, length, output, code)`. -/
def betaEndpointsSet (base : ℕ → ℕ) : Set (Vector3 ℕ 4) :=
  {values |
    sequenceAccessor (values &3) 0 = base (values &0) ∧
      sequenceAccessor (values &3) (values &1) = values &2}

/-- Both non-bounded equations in a beta computation are Diophantine. -/
theorem betaEndpointsSet_dioph {base : ℕ → ℕ} (hbase : NatDiophFn base) :
    Dioph (betaEndpointsSet base) := by
  have hinitial :
      DiophFn fun values : Vector3 ℕ 4 ↦ sequenceAccessor (values &3) 0 :=
    Dioph.diophFn_comp sequenceAccessor_diophFn
      [fun values : Vector3 ℕ 4 ↦ values &3, fun _ ↦ 0]
      ⟨D&3, D.0⟩
  unfold NatDiophFn at hbase
  have hbaseValue :
      DiophFn fun values : Vector3 ℕ 4 ↦ base (values &0) :=
    Dioph.diophFn_comp hbase [fun values : Vector3 ℕ 4 ↦ values &0] (D&0)
  have hfinal :
      DiophFn fun values : Vector3 ℕ 4 ↦
        sequenceAccessor (values &3) (values &1) :=
    Dioph.diophFn_comp sequenceAccessor_diophFn
      [fun values : Vector3 ℕ 4 ↦ values &3, fun values ↦ values &1]
      ⟨D&3, D&1⟩
  exact Dioph.ext ((hinitial D= hbaseValue) D∧ (hfinal D= D&2)) fun _ ↦ Iff.rfl

/-- The complete beta-computation relation in explicit four-variable order. -/
def betaComputationSet (base step : ℕ → ℕ) : Set (Vector3 ℕ 4) :=
  {values |
    BetaComputation base step (values &0) (values &1) (values &2) (values &3)}

/-- Once bounded transition validity is Diophantine, the full beta-computation relation is
Diophantine; the endpoint equations need no further closure assumption. -/
theorem betaComputationSet_dioph
    (closure : BoundedBetaStepsAreDiophantine) {base step : ℕ → ℕ}
    (hbase : NatDiophFn base) (hstep : NatDiophFn step) :
    Dioph (betaComputationSet base step) := by
  have hbounded :
      Dioph fun values : Vector3 ℕ 4 ↦
        ∀ index < values &1, BetaStep step (values &0) (values &3) index := by
    simpa [boundedBetaStepsSet] using
      (closure hstep).reindex_dioph (Fin2 4) [&0, &1, &3]
  apply Dioph.ext ((betaEndpointsSet_dioph hbase) D∧ hbounded)
  intro values
  change
    ((sequenceAccessor (values &3) 0 = base (values &0) ∧
        sequenceAccessor (values &3) (values &1) = values &2) ∧
      ∀ index < values &1,
        sequenceAccessor (values &3) (index + 1) =
          step (Nat.pair (values &0)
            (Nat.pair index (sequenceAccessor (values &3) index)))) ↔
      sequenceAccessor (values &3) 0 = base (values &0) ∧
        sequenceAccessor (values &3) (values &1) = values &2 ∧
          ∀ index < values &1,
            sequenceAccessor (values &3) (index + 1) =
              step (Nat.pair (values &0)
                (Nat.pair index (sequenceAccessor (values &3) index)))
  tauto

/-- The existing primitive-recursion closure follows from precisely the bounded-universal
transition closure above.  Pairing, unpairing, endpoints, individual steps, composition, and the
existential beta code are all discharged concretely. -/
theorem betaRecursionGraphsAreDiophantine_of_boundedBetaSteps
    (closure : BoundedBetaStepsAreDiophantine) :
    BetaRecursionGraphsAreDiophantine := by
  intro base step hbase hstep
  have hcomputation := betaComputationSet_dioph closure hbase hstep
  have hparameter :
      DiophFn fun values : Vector3 ℕ 3 ↦ (Nat.unpair (values &2)).1 :=
    natUnpair_fst_comp_diophFn (D&2)
  have hlength :
      DiophFn fun values : Vector3 ℕ 3 ↦ (Nat.unpair (values &2)).2 :=
    natUnpair_snd_comp_diophFn (D&2)
  have hinstantiated :
      Dioph fun values : Vector3 ℕ 3 ↦
        BetaComputation base step
          (Nat.unpair (values &2)).1 (Nat.unpair (values &2)).2
          (values &1) (values &0) := by
    exact Dioph.dioph_comp hcomputation
      [fun values : Vector3 ℕ 3 ↦ (Nat.unpair (values &2)).1,
        fun values ↦ (Nat.unpair (values &2)).2,
        fun values ↦ values &1,
        fun values ↦ values &0]
      ⟨hparameter, hlength, D&1, D&0⟩
  have hgraph :
      Dioph fun values : Vector3 ℕ 2 ↦
        ∃ code,
          BetaComputation base step
            (Nat.unpair (values &1)).1 (Nat.unpair (values &1)).2
            (values &0) code := by
    exact (D∃) 2 hinstantiated
  exact Dioph.ext hgraph fun _ ↦ Iff.rfl

/-- The two bounded-transition interfaces differ only by the explicit coordinate permutation
`(parameter, length, code) ↦ (code, length, parameter)`. -/
theorem boundedBetaTransitionsAreDiophantine_of_boundedBetaSteps
    (closure : BoundedBetaStepsAreDiophantine) :
    BoundedBetaTransitionsAreDiophantine := by
  intro step hstep
  have hpermuted :=
    (closure hstep).reindex_dioph (Fin2 3) [&2, &1, &0]
  exact Dioph.ext hpermuted fun _ ↦ Iff.rfl

/-- The bounded-step closure therefore supplies the existing complete induction from unary
primitive-recursive functions to proposition-valued Diophantine functions. -/
theorem natPrimrec_diophFn_of_boundedBetaSteps
    (closure : BoundedBetaStepsAreDiophantine)
    {function : ℕ → ℕ} (hfunction : Nat.Primrec function) :
    NatDiophFn function :=
  natPrimrec_diophFn
    (boundedBetaTransitionsAreDiophantine_of_boundedBetaSteps closure) hfunction

end TrinomialUndecidability.Computability.MathlibDiophantineRecursionTrace
