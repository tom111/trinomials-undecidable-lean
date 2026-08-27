import TrinomialUndecidability.Computability.MathlibDiophantineRecursionTrace
import TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherCompiler

/-!
# The bounded-universal Diophantine interface

Mathlib proves that exponentiation is Diophantine (`Dioph.pow_dioph`) but its pinned
`NumberTheory.Dioph` module has no closure theorem for bounded universal quantification.  The
two-view regular-cipher compiler imported above supplies the Lean counterpart of
`dio_rel_fall_lt` from `theories/H10/Dio/dio_bounded.v`: one left radix view, one stretched right
view, and a geometric diagonal mask encode every bounded instance and its independent witnesses.

This module exposes that general closure through the original project interface and specializes it
to the equality and beta-transition forms consumed by primitive recursion.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineBounded

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

open TrinomialUndecidability.Computability.MathlibDiophantinePairing
open TrinomialUndecidability.Computability.MathlibDiophantinePrimrec
open TrinomialUndecidability.Computability.MathlibDiophantineRecursionTrace
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherCompiler
open TrinomialUndecidability.Computability.MathlibDiophantineSequence

/-! ## Exact bounded-universal interfaces -/

/-- The direct Lean interface corresponding to Coq's `dio_rel_fall_lt`: a Diophantine relation
remains Diophantine after universally quantifying a new leading variable below a Diophantine
bound. -/
def BoundedForallLtDiophantine : Prop :=
  ∀ {arity : ℕ} {bound : Vector3 ℕ arity → ℕ}
      {relation : Set (Vector3 ℕ (Nat.succ arity))},
    DiophFn bound → Dioph relation →
      Dioph fun values : Vector3 ℕ arity ↦
        ∀ index < bound values, relation (index :: values)

/-- Two-view regular ciphers prove closure under arbitrary bounded universal quantification. -/
theorem boundedForallLtDiophantine : BoundedForallLtDiophantine := by
  intro arity bound relation hbound hrelation
  exact boundedForallLt_dioph hbound hrelation

/-- The equality-only bounded-universal closure sufficient for beta transitions.  This is weaker
than arbitrary bounded-universal closure because the quantified relation must be the equality of
two Diophantine functions. -/
def BoundedEqualityDiophantine : Prop :=
  ∀ {arity : ℕ} {bound : Vector3 ℕ arity → ℕ}
      {left right : Vector3 ℕ (Nat.succ arity) → ℕ},
    DiophFn bound → DiophFn left → DiophFn right →
      Dioph fun values : Vector3 ℕ arity ↦
        ∀ index < bound values, left (index :: values) = right (index :: values)

/-- General bounded-universal closure implies its equality-only specialization. -/
theorem boundedEqualityDiophantine_of_boundedForallLt
    (bounded : BoundedForallLtDiophantine) :
    BoundedEqualityDiophantine := by
  intro arity bound left right hbound hleft hright
  exact bounded hbound (hleft D= hright)

/-! ## Reduction of bounded beta transitions to bounded equality -/

/-- The next beta entry, with variable order `(index, code, length, parameter)`. -/
def betaTransitionNext (values : Vector3 ℕ 4) : ℕ :=
  sequenceAccessor (values &1) (values &0 + 1)

/-- The value required by the packed recursion step, with variable order
`(index, code, length, parameter)`. -/
def betaTransitionExpected (step : ℕ → ℕ) (values : Vector3 ℕ 4) : ℕ :=
  step (Nat.pair (values &3)
    (Nat.pair (values &0) (sequenceAccessor (values &1) (values &0))))

/-- Reading the next beta entry is a Diophantine function. -/
theorem betaTransitionNext_diophFn : DiophFn betaTransitionNext := by
  unfold betaTransitionNext
  exact Dioph.diophFn_comp sequenceAccessor_diophFn
    [fun values : Vector3 ℕ 4 ↦ values &1, fun values ↦ values &0 + 1]
    ⟨D&1, (D&0) D+ D.1⟩

/-- The expected transition value is Diophantine whenever the packed step function is. -/
theorem betaTransitionExpected_diophFn {step : ℕ → ℕ} (hstep : NatDiophFn step) :
    DiophFn (betaTransitionExpected step) := by
  have hcurrent :
      DiophFn fun values : Vector3 ℕ 4 ↦
        sequenceAccessor (values &1) (values &0) :=
    Dioph.diophFn_comp sequenceAccessor_diophFn
      [fun values : Vector3 ℕ 4 ↦ values &1, fun values ↦ values &0]
      ⟨D&1, D&0⟩
  have hinnerPair :
      DiophFn fun values : Vector3 ℕ 4 ↦
        Nat.pair (values &0) (sequenceAccessor (values &1) (values &0)) :=
    natPair_comp_diophFn (D&0) hcurrent
  have hstepInput :
      DiophFn fun values : Vector3 ℕ 4 ↦
        Nat.pair (values &3)
          (Nat.pair (values &0) (sequenceAccessor (values &1) (values &0))) :=
    natPair_comp_diophFn (D&3) hinnerPair
  unfold NatDiophFn at hstep
  unfold betaTransitionExpected
  exact Dioph.diophFn_comp hstep
    [fun values : Vector3 ℕ 4 ↦
      Nat.pair (values &3)
        (Nat.pair (values &0) (sequenceAccessor (values &1) (values &0)))]
    hstepInput

/-- Equality-only bounded-universal closure proves the exact beta-transition boundary used by
primitive recursion. -/
theorem boundedBetaTransitionsAreDiophantine_of_boundedEquality
    (bounded : BoundedEqualityDiophantine) :
    BoundedBetaTransitionsAreDiophantine := by
  intro step hstep
  have hbound :
      DiophFn fun values : Vector3 ℕ 3 ↦ values &1 := D&1
  have htransitions := bounded hbound betaTransitionNext_diophFn
    (betaTransitionExpected_diophFn hstep)
  exact Dioph.ext htransitions fun _ ↦ Iff.rfl

/-- The exact Coq-style bounded-universal theorem is sufficient for the beta-transition boundary. -/
theorem boundedBetaTransitionsAreDiophantine_of_boundedForallLt
    (bounded : BoundedForallLtDiophantine) :
    BoundedBetaTransitionsAreDiophantine :=
  boundedBetaTransitionsAreDiophantine_of_boundedEquality
    (boundedEqualityDiophantine_of_boundedForallLt bounded)

/-- The recursion-trace presentation differs from the transition presentation only by the
coordinate permutation `(parameter, length, code) ↦ (code, length, parameter)`. -/
theorem boundedBetaStepsAreDiophantine_of_boundedBetaTransitions
    (closure : BoundedBetaTransitionsAreDiophantine) :
    BoundedBetaStepsAreDiophantine := by
  intro step hstep
  have hpermuted :=
    (closure hstep).reindex_dioph (Fin2 3) [&2, &1, &0]
  exact Dioph.ext hpermuted fun _ ↦ Iff.rfl

/-- Equality-only bounded-universal closure proves the trace presentation consumed by the
bounded-halting source module. -/
theorem boundedBetaStepsAreDiophantine_of_boundedEquality
    (bounded : BoundedEqualityDiophantine) :
    BoundedBetaStepsAreDiophantine :=
  boundedBetaStepsAreDiophantine_of_boundedBetaTransitions
    (boundedBetaTransitionsAreDiophantine_of_boundedEquality bounded)

/-- The exact Coq-style bounded-universal theorem proves the sole trace closure needed by the
bounded-halting source module. -/
theorem boundedBetaStepsAreDiophantine_of_boundedForallLt
    (bounded : BoundedForallLtDiophantine) :
    BoundedBetaStepsAreDiophantine :=
  boundedBetaStepsAreDiophantine_of_boundedEquality
    (boundedEqualityDiophantine_of_boundedForallLt bounded)

/-- The beta-step closure required by the primitive-recursion graph is unconditional. -/
theorem boundedBetaStepsAreDiophantine : BoundedBetaStepsAreDiophantine :=
  boundedBetaStepsAreDiophantine_of_boundedForallLt boundedForallLtDiophantine

end TrinomialUndecidability.Computability.MathlibDiophantineBounded
