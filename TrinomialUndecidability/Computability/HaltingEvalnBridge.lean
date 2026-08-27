import Mathlib.Computability.Halting

/-!
# The bounded-evaluator entry point for an effective MRDP construction

This module isolates the primitive-recursive predicate whose effective Diophantine
representation would complete the source side of the trinomial-containment reduction.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.HaltingEvalnBridge

open Nat.Partrec

/-- The standard fixed-input halting predicate from mathlib. -/
def HaltsAtZero (code : Code) : Prop :=
  (Code.eval code 0).Dom

/-- A bounded run of `code` on input zero has produced an output. -/
def BoundedHaltsAtZero (input : ℕ × Code) : Bool :=
  (Code.evaln input.1 input.2 0).isSome

/-- The bounded-halting test is primitive recursive. -/
theorem boundedHaltsAtZero_primrec : Primrec BoundedHaltsAtZero := by
  exact Primrec.option_isSome.comp
    (Code.primrec_evaln.comp (Primrec.id.pair (Primrec.const 0)))

/-- The proposition tested by `BoundedHaltsAtZero` is a primitive-recursive predicate. -/
theorem boundedHaltsAtZero_primrecPred :
    PrimrecPred (fun input ↦ BoundedHaltsAtZero input = true) := by
  apply Primrec.primrecPred
  simpa using boundedHaltsAtZero_primrec

/-- Fixed-input halting is existential closure of the concrete primitive-recursive
bounded-evaluator predicate. -/
theorem haltsAtZero_iff_exists_bounded (code : Code) :
    HaltsAtZero code ↔ ∃ fuel, BoundedHaltsAtZero (fuel, code) = true := by
  unfold HaltsAtZero
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨output, houtput⟩
    obtain ⟨fuel, hfuel⟩ := Code.evaln_complete.mp houtput
    have heq : Code.evaln fuel code 0 = some output := by
      simpa only [Option.mem_def] using hfuel
    exact ⟨fuel, by simp [BoundedHaltsAtZero, heq]⟩
  · rintro ⟨fuel, hfuel⟩
    obtain ⟨output, houtput⟩ : ∃ output, output ∈ Code.evaln fuel code 0 := by
      simpa [BoundedHaltsAtZero, Option.isSome_iff_exists] using hfuel
    exact ⟨output, Code.evaln_complete.mpr ⟨fuel, houtput⟩⟩

end TrinomialUndecidability.Computability.HaltingEvalnBridge
