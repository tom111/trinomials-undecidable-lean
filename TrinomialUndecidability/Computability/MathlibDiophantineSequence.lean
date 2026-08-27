import Mathlib.Logic.Godel.GodelBetaFunction
import TrinomialUndecidability.Computability.MathlibDiophantinePairing

/-!
# Diophantine access to finite natural-number sequences

This module connects mathlib's proposition-valued `DiophFn` API to its checked Gödel beta
function lemma.  `betaAccessor` is the arithmetic CRT remainder operation with its two
parameters exposed.  `sequenceAccessor` packs those parameters into one natural number using
`Nat.unpair`, exactly as `Nat.beta` does.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineSequence

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

open TrinomialUndecidability.Computability.MathlibDiophantinePairing

/-- The arithmetic core of Gödel's beta function, with the CRT remainder and modulus-scale
parameters exposed separately. -/
def betaAccessor (remainder modulusScale index : ℕ) : ℕ :=
  remainder % ((index + 1) * modulusScale + 1)

/-- The exposed-parameter beta accessor is a Diophantine ternary function. -/
theorem betaAccessor_diophFn :
    DiophFn fun values : Vector3 ℕ 3 =>
      betaAccessor (values &0) (values &1) (values &2) := by
  exact (D&0) D% (((D&2 D+ D.1) D* D&1) D+ D.1)

/-- One-natural-number coding of the beta parameters.  This is definitionally mathlib's
`Nat.beta`, but is stated locally to expose the source compiler's intended interface. -/
def sequenceAccessor (code index : ℕ) : ℕ :=
  betaAccessor (Nat.unpair code).1 (Nat.unpair code).2 index

@[simp]
theorem sequenceAccessor_eq_beta (code index : ℕ) :
    sequenceAccessor code index = Nat.beta code index := rfl

/-- Accessing an entry of a beta-coded sequence is a Diophantine binary function. -/
theorem sequenceAccessor_diophFn :
    DiophFn fun values : Vector3 ℕ 2 => sequenceAccessor (values &0) (values &1) := by
  have hleft :
      DiophFn fun values : Vector3 ℕ 2 => (Nat.unpair (values &0)).1 :=
    natUnpair_fst_comp_diophFn (D&0)
  have hright :
      DiophFn fun values : Vector3 ℕ 2 => (Nat.unpair (values &0)).2 :=
    natUnpair_snd_comp_diophFn (D&0)
  exact hleft D% (((D&1 D+ D.1) D* hright) D+ D.1)

/-- The canonical mathlib CRT code recovers every entry of a finite list. -/
@[simp]
theorem sequenceAccessor_unbeta (values : List ℕ) (index : Fin values.length) :
    sequenceAccessor (Nat.unbeta values) index = values[index] := by
  change Nat.beta (Nat.unbeta values) index = values[index]
  exact Nat.beta_unbeta_coe values index

/-- Every finite list of naturals has one code whose beta values recover all its entries. -/
theorem exists_sequenceCode (values : List ℕ) :
    ∃ code, ∀ index : Fin values.length,
      sequenceAccessor code index = values[index] := by
  exact ⟨Nat.unbeta values, sequenceAccessor_unbeta values⟩

/-- Every finite natural sequence has exposed CRT parameters recovering all its entries. -/
theorem exists_betaParameters (values : List ℕ) :
    ∃ remainder modulusScale, ∀ index : Fin values.length,
      betaAccessor remainder modulusScale index = values[index] := by
  refine ⟨(Nat.unpair (Nat.unbeta values)).1, (Nat.unpair (Nat.unbeta values)).2, ?_⟩
  exact sequenceAccessor_unbeta values

/-- Function-valued form of the finite sequence coding theorem. -/
theorem exists_sequenceCode_fin {length : ℕ} (values : Fin length → ℕ) :
    ∃ code, ∀ index : Fin length, sequenceAccessor code index = values index := by
  refine ⟨Nat.unbeta (List.ofFn values), ?_⟩
  intro index
  let listIndex : Fin (List.ofFn values).length :=
    ⟨index.val, by simp⟩
  have hrecover := sequenceAccessor_unbeta (List.ofFn values) listIndex
  simpa [listIndex] using hrecover

end TrinomialUndecidability.Computability.MathlibDiophantineSequence
