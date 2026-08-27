import Mathlib.Data.Nat.Pairing
import Mathlib.NumberTheory.Dioph

/-!
# Diophantine graphs for the natural pairing equivalence

This module supplies the proposition-valued `DiophFn` facts for `Nat.pair` and the two
projections of `Nat.unpair`.  The pairing graph is the union of its two polynomial branches.
Each unpairing graph is obtained from that graph by existentially hiding the other output
coordinate and using the inverse laws for `Nat.pair` and `Nat.unpair`.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantinePairing

open Dioph Fin2 Function Nat
open Vector3
open scoped Dioph Vector3

/-- The standard natural pairing function is Diophantine as a binary function. -/
theorem natPair_diophFn :
    DiophFn fun values : Vector3 ℕ 2 => Nat.pair (values &0) (values &1) := by
  apply (Dioph.diophFn_vec _).2
  have hgraph :
      Dioph fun values : Vector3 ℕ 3 =>
        (values &1 < values &2 ∧
            values &0 = values &2 * values &2 + values &1) ∨
          (values &2 ≤ values &1 ∧
            values &0 = values &1 * values &1 + values &1 + values &2) :=
    ((D&1 D< D&2) D∧ (D&0 D= (D&2 D* D&2) D+ D&1)) D∨
      ((D&2 D≤ D&1) D∧ (D&0 D= ((D&1 D* D&1) D+ D&1) D+ D&2))
  apply Dioph.ext hgraph
  intro values
  change
    ((values &1 < values &2 ∧
        values &0 = values &2 * values &2 + values &1) ∨
      (values &2 ≤ values &1 ∧
        values &0 = values &1 * values &1 + values &1 + values &2)) ↔
      Nat.pair (values &1) (values &2) = values &0
  rw [Nat.pair]
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h, Nat.le_of_not_gt h, eq_comm]

/-- The relation `Nat.pair left right = paired` is Diophantine. -/
theorem natPair_graph_dioph :
    Dioph fun values : Vector3 ℕ 3 =>
      Nat.pair (values &0) (values &1) = values &2 := by
  exact (Dioph.diophFn_comp2 (D&0) (D&1) natPair_diophFn) D= D&2

/-- Pairing two Diophantine functions gives another Diophantine function. -/
theorem natPair_comp_diophFn {α : Type} {left right : (α → ℕ) → ℕ}
    (hleft : DiophFn left) (hright : DiophFn right) :
    DiophFn fun values => Nat.pair (left values) (right values) :=
  Dioph.diophFn_comp2 hleft hright natPair_diophFn

/-- The first projection of `Nat.unpair` is a Diophantine unary function. -/
theorem natUnpair_fst_diophFn :
    DiophFn fun values : Vector3 ℕ 1 => (Nat.unpair (values &0)).1 := by
  apply (Dioph.diophFn_vec _).2
  have hgraph :
      Dioph fun values : Vector3 ℕ 2 =>
        ∃ right, Nat.pair (values &0) right = values &1 := by
    exact (D∃) 2 <|
      (Dioph.diophFn_comp2 (D&1) (D&0) natPair_diophFn) D= D&2
  apply Dioph.ext hgraph
  intro values
  change
    (∃ right, Nat.pair (values &0) right = values &1) ↔
      (Nat.unpair (values &1)).1 = values &0
  constructor
  · rintro ⟨right, hpair⟩
    rw [← hpair, Nat.unpair_pair]
  · intro hleft
    refine ⟨(Nat.unpair (values &1)).2, ?_⟩
    rw [← hleft, Nat.pair_unpair]

/-- The second projection of `Nat.unpair` is a Diophantine unary function. -/
theorem natUnpair_snd_diophFn :
    DiophFn fun values : Vector3 ℕ 1 => (Nat.unpair (values &0)).2 := by
  apply (Dioph.diophFn_vec _).2
  have hgraph :
      Dioph fun values : Vector3 ℕ 2 =>
        ∃ left, Nat.pair left (values &0) = values &1 := by
    exact (D∃) 2 <|
      (Dioph.diophFn_comp2 (D&0) (D&1) natPair_diophFn) D= D&2
  apply Dioph.ext hgraph
  intro values
  change
    (∃ left, Nat.pair left (values &0) = values &1) ↔
      (Nat.unpair (values &1)).2 = values &0
  constructor
  · rintro ⟨left, hpair⟩
    rw [← hpair, Nat.unpair_pair]
  · intro hright
    refine ⟨(Nat.unpair (values &1)).1, ?_⟩
    rw [← hright, Nat.pair_unpair]

/-- Taking the first unpairing projection of a Diophantine function preserves
Diophantineness. -/
theorem natUnpair_fst_comp_diophFn {α : Type} {paired : (α → ℕ) → ℕ}
    (hpaired : DiophFn paired) :
    DiophFn fun values => (Nat.unpair (paired values)).1 :=
  Dioph.diophFn_comp natUnpair_fst_diophFn [paired] hpaired

/-- Taking the second unpairing projection of a Diophantine function preserves
Diophantineness. -/
theorem natUnpair_snd_comp_diophFn {α : Type} {paired : (α → ℕ) → ℕ}
    (hpaired : DiophFn paired) :
    DiophFn fun values => (Nat.unpair (paired values)).2 :=
  Dioph.diophFn_comp natUnpair_snd_diophFn [paired] hpaired

end TrinomialUndecidability.Computability.MathlibDiophantinePairing
