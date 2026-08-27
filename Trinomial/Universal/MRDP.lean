import TrinomialUndecidability.Computability.MathlibDiophantineBounded
import TrinomialUndecidability.Computability.MathlibDiophantineBridge
import TrinomialUndecidability.Computability.HaltingEvalnBridge
import Trinomial.Encoding.StraightLineProgram

/-!
# MRDP and the undecidability of trinomial containment

[Corollary 4.6 and §5].  This module connects the machine-checked MRDP
source layer (vendored from the earlier formalization in
`TrinomialUndecidability/Computability/` — same mathlib pin, route-independent) to the
reduction of Theorem 4.5:

1. fixed-input halting is the existential closure of the primitive-recursive bounded
   evaluator (`haltsAtZero_iff_exists_bounded`), and the bounded evaluator is
   Diophantine over `ℕ` (unconditional bounded-universal closure via the vendored
   regular-cipher construction);
2. the vendored bridge converts the resulting mathlib `Dioph` set into an explicit
   finite integer-polynomial relation with exact `ℕ→ℤ` four-square witness semantics;
3. the relation is packed into a **single** integer polynomial `haltingPoly e` (a sum
   of squares, with the program code frozen by an extra square), so that
   `haltingPoly e` has an integral zero iff machine `e` halts on input `0`
   (`haltingPoly_zero_iff`; this is eq. (8) of the paper).

The family of ideals `I_e` of Corollary 5.1 is built from `haltingRel` in
`Trinomial/Universal/HaltingFamily.lean`.
-/

set_option autoImplicit false

namespace Trinomial.MRDP

open Nat.Partrec
open TrinomialUndecidability.Computability
open TrinomialUndecidability.Computability.EffDiophRel
open TrinomialUndecidability.Computability.HaltingEvalnBridge
open TrinomialUndecidability.Computability.MathlibDiophantinePairing
open TrinomialUndecidability.Computability.MathlibDiophantineBounded
open TrinomialUndecidability.Computability.MathlibDiophantinePrimrec
open TrinomialUndecidability.Computability.MathlibDiophantineBridge
open Vector3
open scoped Dioph Vector3

/-- A two-coordinate natural assignment (as in the earlier formalization). -/
def naturalPairAssignment (left right : ℕ) : Fin 2 → ℕ :=
  Fin.cases left fun _ ↦ right

@[simp] theorem naturalPairAssignment_zero (l r : ℕ) :
    naturalPairAssignment l r 0 = l := rfl

@[simp] theorem naturalPairAssignment_one (l r : ℕ) :
    naturalPairAssignment l r 1 = r := rfl

/-! ### Step 1: bounded halting is Diophantine

Adapted from the earlier formalization's `BoundedHaltingDiophantineSource` (whose file
is entangled with the old route's target side and is therefore not vendored whole). -/

/-- The zero-one characteristic function of the bounded-halting set:
coordinate `0` is the program code, coordinate `1` the fuel. -/
def boundedHaltingIndicator (assignment : Fin 2 → ℕ) : ℕ :=
  Bool.toNat (BoundedHaltsAtZero (assignment 1, Denumerable.ofNat Code (assignment 0)))

theorem primrec_boundedHaltingIndicator : Primrec boundedHaltingIndicator := by
  have hcoordinate (index : Fin 2) :
      Primrec (fun assignment : Fin 2 → ℕ ↦ assignment index) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const index)
  exact (Primrec.dom_bool Bool.toNat).comp (boundedHaltsAtZero_primrec.comp
    ((hcoordinate 1).pair ((Primrec.ofNat Code).comp (hcoordinate 0))))

/-- Unary paired-input form of the bounded-halting characteristic function. -/
def boundedHaltingPairedIndicator (input : ℕ) : ℕ :=
  boundedHaltingIndicator
    (naturalPairAssignment (Nat.unpair input).1 (Nat.unpair input).2)

theorem natPrimrec_boundedHaltingPairedIndicator :
    Nat.Primrec boundedHaltingPairedIndicator := by
  apply Primrec.nat_iff.mp
  have hleft : Primrec fun input : ℕ ↦ (Nat.unpair input).1 :=
    Primrec.nat_iff.mpr Nat.Primrec.left
  have hright : Primrec fun input : ℕ ↦ (Nat.unpair input).2 :=
    Primrec.nat_iff.mpr Nat.Primrec.right
  have hinput : Primrec fun input : ℕ ↦
      ((Nat.unpair input).2, Denumerable.ofNat Code (Nat.unpair input).1) :=
    hright.pair ((Primrec.ofNat Code).comp hleft)
  exact ((Primrec.dom_bool Bool.toNat).comp
    (boundedHaltsAtZero_primrec.comp hinput)).of_eq fun input ↦ by
      unfold boundedHaltingPairedIndicator boundedHaltingIndicator
      rw [naturalPairAssignment_zero, naturalPairAssignment_one]

/-- The paired indicator is a Diophantine function — **the MRDP core**, unconditional
via the vendored regular-cipher bounded-universal closure. -/
theorem diophFn_boundedHaltingPairedIndicator :
    NatDiophFn boundedHaltingPairedIndicator :=
  natPrimrec_diophFn
    (boundedBetaTransitionsAreDiophantine_of_boundedForallLt boundedForallLtDiophantine)
    natPrimrec_boundedHaltingPairedIndicator

theorem diophFn_boundedHaltingIndicator :
    Dioph.DiophFn boundedHaltingIndicator := by
  have hpair : Dioph.DiophFn fun assignment : Fin 2 → ℕ ↦
      Nat.pair (assignment 0) (assignment 1) :=
    natPair_comp_diophFn (Dioph.proj_dioph 0) (Dioph.proj_dioph 1)
  have hcomposition := Dioph.diophFn_comp diophFn_boundedHaltingPairedIndicator
    [fun assignment : Fin 2 → ℕ ↦ Nat.pair (assignment 0) (assignment 1)] hpair
  have hequality :
      (fun assignment : Fin 2 → ℕ ↦
        boundedHaltingPairedIndicator (Nat.pair (assignment 0) (assignment 1))) =
        boundedHaltingIndicator := by
    funext assignment
    unfold boundedHaltingPairedIndicator boundedHaltingIndicator
    rw [Nat.unpair_pair, naturalPairAssignment_zero, naturalPairAssignment_one]
  exact hequality ▸ hcomposition

/-- The bounded-halting set: code at coordinate `0`, fuel at coordinate `1`. -/
def boundedHaltingSet : Set (Fin 2 → ℕ) :=
  {assignment |
    BoundedHaltsAtZero (assignment 1, Denumerable.ofNat Code (assignment 0)) = true}

theorem dioph_boundedHaltingSet : Dioph boundedHaltingSet := by
  have hindicator : Dioph {assignment : Fin 2 → ℕ |
      boundedHaltingIndicator assignment =
        Function.const (Fin 2 → ℕ) 1 assignment} :=
    Dioph.eq_dioph diophFn_boundedHaltingIndicator (Dioph.const_dioph 1)
  refine Dioph.ext hindicator fun assignment ↦ ?_
  cases hvalue : BoundedHaltsAtZero
      (assignment 1, Denumerable.ofNat Code (assignment 0)) <;>
    simp [boundedHaltingIndicator, boundedHaltingSet, hvalue, Function.const]

/-! ### Step 2: the halting set over one variable -/

/-- The unbounded halting set: machine `v 0` halts on input `0`. -/
def haltingSet : Set (Fin 1 → ℕ) :=
  {v | HaltsAtZero (Denumerable.ofNat Code (v 0))}

/-- The coordinate assignment identifying `Fin 2` with `Fin 1 ⊕ Fin 1`
(code free, fuel existential). -/
def fuelSplit : Fin 2 → (Fin 1 ⊕ Fin 1) := ![Sum.inl 0, Sum.inr 0]

theorem dioph_haltingSet : Dioph haltingSet := by
  have hreindexed : Dioph {w : Fin 1 ⊕ Fin 1 → ℕ | w ∘ fuelSplit ∈ boundedHaltingSet} :=
    Dioph.reindex_dioph (Fin 1 ⊕ Fin 1) fuelSplit dioph_boundedHaltingSet
  have hexists := Dioph.ex_dioph hreindexed
  refine Dioph.ext hexists fun v ↦ ?_
  show (∃ x : Fin 1 → ℕ, (Sum.elim v x) ∘ fuelSplit ∈ boundedHaltingSet) ↔ _
  have hcomp : ∀ x : Fin 1 → ℕ,
      ((Sum.elim v x) ∘ fuelSplit ∈ boundedHaltingSet ↔
        BoundedHaltsAtZero (x 0, Denumerable.ofNat Code (v 0)) = true) := by
    intro x
    rfl
  constructor
  · rintro ⟨x, hx⟩
    exact (haltsAtZero_iff_exists_bounded _).mpr ⟨x 0, (hcomp x).mp hx⟩
  · intro hv
    obtain ⟨fuel, hfuel⟩ := (haltsAtZero_iff_exists_bounded _).mp hv
    exact ⟨fun _ ↦ fuel, (hcomp _).mpr hfuel⟩

/-! ### Step 3: one integer polynomial per program -/

/-- The fixed effective Diophantine relation representing halting. -/
noncomputable def haltingRel : EffDiophRel 1 :=
  effDiophRelOfDioph dioph_haltingSet

theorem haltingRel_spec (e : ℕ) :
    haltingRel.Realizes (fun _ ↦ (e : ℤ)) ↔
      HaltsAtZero (Denumerable.ofNat Code e) := by
  have h := realizes_effDiophRelOfDioph dioph_haltingSet (fun _ : Fin 1 ↦ e)
  exact h

/-- One integer polynomial per program: the sum of the squares of the relation's
equations, plus a square freezing the free coordinate at the program code `e`. -/
noncomputable def haltingPoly (e : ℕ) : MvPolynomial (Fin (1 + haltingRel.aux)) ℤ :=
  codeToMv (sumSquares haltingRel.eqs)
    + (MvPolynomial.X 0 - MvPolynomial.C (e : ℤ)) ^ 2

/-- `haltingPoly e` has an integral zero iff machine `e` halts on input `0`
[§5].  This is a frozen-parameter equivalent of the paper's substitution
`U(e,Y)` into the universal polynomial: the parameter coordinate is kept and pinned
to `e` by the added square, so the source arity is fixed and the semantics agree. -/
theorem haltingPoly_zero_iff (e : ℕ) :
    (∃ x : Fin (1 + haltingRel.aux) → ℤ, MvPolynomial.eval x (haltingPoly e) = 0)
      ↔ HaltsAtZero (Denumerable.ofNat Code e) := by
  rw [← haltingRel_spec]
  have heval : ∀ x : Fin (1 + haltingRel.aux) → ℤ,
      MvPolynomial.eval x (haltingPoly e) = 0 ↔
        Satisfies haltingRel.eqs x ∧ x 0 = (e : ℤ) := by
    intro x
    rw [haltingPoly, map_add, map_pow, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [eval_codeToMv]
    have hnn1 : (0 : ℤ) ≤ evalPolynomial (sumSquares haltingRel.eqs) x :=
      eval_sumSquares_nonneg x haltingRel.eqs
    constructor
    · intro h
      have hsq : evalPolynomial (sumSquares haltingRel.eqs) x = 0 := by
        nlinarith [sq_nonneg (x 0 - (e : ℤ))]
      have hx0 : (x 0 - (e : ℤ)) ^ 2 = 0 := by nlinarith
      refine ⟨?_, ?_⟩
      · exact (eval_sumSquares_eq_zero_iff_satisfies haltingRel.eqs x).mp hsq
      · have := pow_eq_zero_iff two_ne_zero |>.mp hx0
        omega
    · rintro ⟨hsat, hx0⟩
      rw [(eval_sumSquares_eq_zero_iff_satisfies haltingRel.eqs x).mpr hsat,
        hx0]
      norm_num
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hsat, hx0⟩ := (heval x).mp hx
    have happ : Fin.append (fun _ : Fin 1 ↦ (e : ℤ)) (fun j ↦ x (Fin.natAdd 1 j)) = x := by
      funext i
      induction i using Fin.addCases with
      | left j =>
          rw [Fin.append_left,
            show Fin.castAdd haltingRel.aux j = (0 : Fin (1 + haltingRel.aux)) by
              rw [Subsingleton.elim j (0 : Fin 1)]
              exact Fin.ext rfl, hx0]
      | right j => rw [Fin.append_right]
    exact ⟨fun j ↦ x (Fin.natAdd 1 j), by rw [happ]; exact hsat⟩
  · rintro ⟨y, hy⟩
    refine ⟨Fin.append (fun _ : Fin 1 ↦ (e : ℤ)) y, (heval _).mpr ⟨hy, ?_⟩⟩
    have h0 : (0 : Fin (1 + haltingRel.aux)) = Fin.castAdd haltingRel.aux (0 : Fin 1) :=
      Fin.ext rfl
    rw [h0, Fin.append_left]

end Trinomial.MRDP
