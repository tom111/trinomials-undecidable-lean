import Mathlib.NumberTheory.Dioph
import Mathlib.NumberTheory.SumFourSquares
import TrinomialUndecidability.Computability.EffectiveDiophantineReindex
import TrinomialUndecidability.Computability.EffectiveDiophantineSingle

/-!
# Bridging mathlib Diophantine polynomials to executable sparse syntax

Mathlib's `Poly` type records a polynomial extensionally together with an `IsPoly`
derivation.  This module extracts, by induction on that derivation, finite sparse syntax
for every such polynomial.  Variables on the left of the sum are retained as free
variables.  Every occurrence of a variable on the right is assigned a finite auxiliary
slot and labelled by the original variable, so later code can identify repeated labels.

The extraction is intentionally proposition-valued (`Nonempty`).  A fixed Diophantine
representation may therefore be chosen classically without pretending that mathlib's
proof-valued `Dioph` API is itself an executable compiler.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineBridge

open TrinomialUndecidability.Computability
open TrinomialUndecidability.Computability.EffDiophRel

/-- Negate every coefficient in a sparse integer polynomial. -/
def negatePolynomial {n : ℕ} (polynomial : IntPolynomialCode n) :
    IntPolynomialCode n :=
  polynomial.map fun term ↦ (term.1, -term.2)

/-- Coefficient-wise sparse negation has the expected evaluation semantics. -/
theorem eval_negatePolynomial {n : ℕ} (polynomial : IntPolynomialCode n)
    (assignment : Fin n → ℤ) :
    evalPolynomial (negatePolynomial polynomial) assignment =
      -evalPolynomial polynomial assignment := by
  induction polynomial with
  | nil => simp [negatePolynomial, evalPolynomial]
  | cons term polynomial ih =>
      rcases term with ⟨exponent, coefficient⟩
      simp only [negatePolynomial, List.map_cons, evalPolynomial]
      change
        -coefficient * evalMonomial exponent assignment +
            evalPolynomial (negatePolynomial polynomial) assignment =
          -(coefficient * evalMonomial exponent assignment +
            evalPolynomial polynomial assignment)
      rw [ih]
      ring

/-- Finite executable syntax presenting one mathlib polynomial.

The label map records which original right-hand variable occupies each auxiliary slot.
Correctness is stated on assignments obtained from one common right-hand assignment; this
is exactly the consistency condition needed to identify duplicate labels later.
-/
structure NaturalPolynomialPresentation {free : ℕ} {β : Type*}
    (polynomial : Poly (Fin free ⊕ β)) where
  aux : ℕ
  label : Fin aux → β
  code : IntPolynomialCode (free + aux)
  correct : ∀ (freeAssignment : Fin free → ℕ) (auxAssignment : β → ℕ),
    evalPolynomial code
        (Fin.append (fun index ↦ Int.ofNat (freeAssignment index))
          (fun index ↦ Int.ofNat (auxAssignment (label index)))) =
      polynomial (Sum.elim freeAssignment auxAssignment)

/-- The one-term sparse code for a selected variable. -/
def variableCode {n : ℕ} (index : Fin n) : IntPolynomialCode n :=
  [(variableExponent index, 1)]

/-- The one-term sparse code for an integer constant. -/
def integerConstantCode (n : ℕ) (constant : ℤ) : IntPolynomialCode n :=
  [(zeroExponent n, constant)]

@[simp]
theorem eval_variableCode {n : ℕ} (index : Fin n) (assignment : Fin n → ℤ) :
    evalPolynomial (variableCode index) assignment = assignment index := by
  simp [variableCode, evalPolynomial]

@[simp]
theorem eval_integerConstantCode (n : ℕ) (constant : ℤ)
    (assignment : Fin n → ℤ) :
    evalPolynomial (integerConstantCode n constant) assignment = constant := by
  simp [integerConstantCode, evalPolynomial]

/-- Combining two auxiliary label blocks and then reading either block recovers the
corresponding original label assignment. -/
private theorem append_label_assignment {leftAux rightAux : ℕ} {β : Type*}
    (left : Fin leftAux → β) (right : Fin rightAux → β)
    (assignment : β → ℕ) :
    (fun index ↦ Int.ofNat (assignment (Fin.append left right index))) =
      Fin.append (fun index ↦ Int.ofNat (assignment (left index)))
        (fun index ↦ Int.ofNat (assignment (right index))) := by
  funext index
  refine Fin.addCases ?_ ?_ index <;> simp

/-- Every mathlib polynomial in a finite free block and an arbitrary witness block has a
finite sparse presentation. -/
theorem exists_naturalPolynomialPresentation {free : ℕ} {β : Type*}
    (polynomial : Poly (Fin free ⊕ β)) :
    Nonempty (NaturalPolynomialPresentation polynomial) := by
  apply Poly.induction
    (C := fun candidate ↦ Nonempty (NaturalPolynomialPresentation candidate))
  · intro index
    rcases index with freeIndex | auxiliaryLabel
    · refine ⟨{
          aux := 0
          label := Fin.elim0
          code := variableCode (Fin.castAdd 0 freeIndex)
          correct := ?_
        }⟩
      intro freeAssignment auxAssignment
      rw [eval_variableCode]
      exact Fin.append_left _ _ freeIndex
    · refine ⟨{
          aux := 1
          label := fun _ ↦ auxiliaryLabel
          code := variableCode (Fin.natAdd free (0 : Fin 1))
          correct := ?_
        }⟩
      intro freeAssignment auxAssignment
      simp
  · intro constant
    refine ⟨{
        aux := 0
        label := Fin.elim0
        code := integerConstantCode free constant
        correct := ?_
      }⟩
    intro freeAssignment auxAssignment
    simp
  · intro left right hleft hright
    obtain ⟨leftPresentation⟩ := hleft
    obtain ⟨rightPresentation⟩ := hright
    refine ⟨{
        aux := leftPresentation.aux + rightPresentation.aux
        label := Fin.append leftPresentation.label rightPresentation.label
        code := addPolynomial
          (liftLeftPolynomial (rightAux := rightPresentation.aux)
            leftPresentation.code)
          (negatePolynomial
            (liftRightPolynomial (leftAux := leftPresentation.aux)
              rightPresentation.code))
        correct := ?_
      }⟩
    intro freeAssignment auxAssignment
    rw [eval_addPolynomial, eval_negatePolynomial]
    rw [append_label_assignment leftPresentation.label rightPresentation.label
      auxAssignment]
    rw [evalPolynomial_liftLeft, evalPolynomial_liftRight]
    rw [leftPresentation.correct, rightPresentation.correct]
    rfl
  · intro left right hleft hright
    obtain ⟨leftPresentation⟩ := hleft
    obtain ⟨rightPresentation⟩ := hright
    refine ⟨{
        aux := leftPresentation.aux + rightPresentation.aux
        label := Fin.append leftPresentation.label rightPresentation.label
        code := mulPolynomial
          (liftLeftPolynomial (rightAux := rightPresentation.aux)
            leftPresentation.code)
          (liftRightPolynomial (leftAux := leftPresentation.aux)
            rightPresentation.code)
        correct := ?_
      }⟩
    intro freeAssignment auxAssignment
    rw [eval_mulPolynomial]
    rw [append_label_assignment leftPresentation.label rightPresentation.label
      auxAssignment]
    rw [evalPolynomial_liftLeft, evalPolynomial_liftRight]
    rw [leftPresentation.correct, rightPresentation.correct]
    rfl

/-- Choose one finite sparse presentation for a fixed mathlib polynomial. -/
noncomputable def naturalPolynomialPresentation {free : ℕ} {β : Type*}
    (polynomial : Poly (Fin free ⊕ β)) :
    NaturalPolynomialPresentation polynomial :=
  Classical.choice (exists_naturalPolynomialPresentation polynomial)

/-! ## Identifying repeated witness labels -/

/-- The finite set of original witness variables actually named by a presentation. -/
noncomputable def NaturalPolynomialPresentation.witnessSupport {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) : Finset β := by
  classical
  exact Finset.univ.image presentation.label

theorem NaturalPolynomialPresentation.label_mem_witnessSupport {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) (index : Fin presentation.aux) :
    presentation.label index ∈ presentation.witnessSupport := by
  classical
  simp [NaturalPolynomialPresentation.witnessSupport]

/-- The deduplicated slot occupied by one labelled auxiliary occurrence. -/
noncomputable def NaturalPolynomialPresentation.supportIndex {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (index : Fin presentation.aux) : Fin presentation.witnessSupport.card :=
  presentation.witnessSupport.equivFin
    ⟨presentation.label index, presentation.label_mem_witnessSupport index⟩

/-- Rename a presentation so that equal original witness labels use the same finite slot. -/
noncomputable def NaturalPolynomialPresentation.dedupIndex {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) :
    Fin (free + presentation.aux) → Fin (free + presentation.witnessSupport.card) :=
  Fin.addCases
    (fun index ↦ Fin.castAdd presentation.witnessSupport.card index)
    (fun index ↦ Fin.natAdd free (presentation.supportIndex index))

/-- Sparse code with one auxiliary coordinate per distinct original witness label. -/
noncomputable def NaturalPolynomialPresentation.deduplicatedCode {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) :
    IntPolynomialCode (free + presentation.witnessSupport.card) :=
  reindexPolynomial presentation.dedupIndex presentation.code

/-- Restrict an original witness assignment to the finite deduplicated support. -/
noncomputable def NaturalPolynomialPresentation.supportAssignment {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) (
      assignment : β → ℕ) : Fin presentation.witnessSupport.card → ℕ :=
  fun index ↦ assignment ((presentation.witnessSupport.equivFin.symm index).1)

@[simp]
theorem NaturalPolynomialPresentation.supportAssignment_supportIndex {free : ℕ}
    {β : Type*} {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) (assignment : β → ℕ)
    (index : Fin presentation.aux) :
    presentation.supportAssignment assignment (presentation.supportIndex index) =
      assignment (presentation.label index) := by
  classical
  simp [NaturalPolynomialPresentation.supportAssignment,
    NaturalPolynomialPresentation.supportIndex]

/-- Deduplication preserves exact evaluation on every common witness assignment. -/
theorem NaturalPolynomialPresentation.eval_deduplicatedCode {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (freeAssignment : Fin free → ℕ) (auxAssignment : β → ℕ) :
    evalPolynomial presentation.deduplicatedCode
        (Fin.append (fun index ↦ Int.ofNat (freeAssignment index))
          (fun index ↦ Int.ofNat
            (presentation.supportAssignment auxAssignment index))) =
      polynomial (Sum.elim freeAssignment auxAssignment) := by
  rw [NaturalPolynomialPresentation.deduplicatedCode,
    evalPolynomial_reindexPolynomial]
  have hassignment :
      (fun index ↦
        Fin.append (fun freeIndex ↦ Int.ofNat (freeAssignment freeIndex))
          (fun auxIndex ↦ Int.ofNat
            (presentation.supportAssignment auxAssignment auxIndex))
          (presentation.dedupIndex index)) =
        Fin.append (fun freeIndex ↦ Int.ofNat (freeAssignment freeIndex))
          (fun auxIndex ↦ Int.ofNat
            (auxAssignment (presentation.label auxIndex))) := by
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro freeIndex
      simp [NaturalPolynomialPresentation.dedupIndex]
    · intro auxIndex
      simp [NaturalPolynomialPresentation.dedupIndex]
  rw [hassignment]
  exact presentation.correct freeAssignment auxAssignment

/-! ## Enforcing natural-valued witnesses over the integers -/

/-- The primary slot for one distinct witness variable in the full relation layout. -/
noncomputable def NaturalPolynomialPresentation.primaryIndex {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (index : Fin presentation.witnessSupport.card) :
    Fin (free + (presentation.witnessSupport.card +
      presentation.witnessSupport.card * 4)) :=
  Fin.natAdd free
    (Fin.castAdd (presentation.witnessSupport.card * 4) index)

/-- One of the four square-witness slots attached to a distinct witness variable. -/
noncomputable def NaturalPolynomialPresentation.squareIndex {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (index : Fin presentation.witnessSupport.card) (square : Fin 4) :
    Fin (free + (presentation.witnessSupport.card +
      presentation.witnessSupport.card * 4)) :=
  Fin.natAdd free
    (Fin.natAdd presentation.witnessSupport.card
      (finProdFinEquiv (index, square)))

/-- The equation saying that one primary witness slot is a sum of four integer squares. -/
noncomputable def NaturalPolynomialPresentation.naturalWitnessPolynomial
    {free : ℕ} {β : Type*} {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (index : Fin presentation.witnessSupport.card) :
    IntPolynomialCode (free + (presentation.witnessSupport.card +
      presentation.witnessSupport.card * 4)) :=
  [
    (variableExponent (presentation.primaryIndex index), 1),
    (addExponent (variableExponent (presentation.squareIndex index 0))
      (variableExponent (presentation.squareIndex index 0)), -1),
    (addExponent (variableExponent (presentation.squareIndex index 1))
      (variableExponent (presentation.squareIndex index 1)), -1),
    (addExponent (variableExponent (presentation.squareIndex index 2))
      (variableExponent (presentation.squareIndex index 2)), -1),
    (addExponent (variableExponent (presentation.squareIndex index 3))
      (variableExponent (presentation.squareIndex index 3)), -1)
  ]

/-- Exact evaluation of one natural-witness equation. -/
theorem NaturalPolynomialPresentation.eval_naturalWitnessPolynomial
    {free : ℕ} {β : Type*} {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (index : Fin presentation.witnessSupport.card) (freeAssignment : Fin free → ℤ)
    (primary : Fin presentation.witnessSupport.card → ℤ)
    (squares : Fin (presentation.witnessSupport.card * 4) → ℤ) :
    evalPolynomial (presentation.naturalWitnessPolynomial index)
        (Fin.append freeAssignment (Fin.append primary squares)) =
      primary index -
        (squares (finProdFinEquiv (index, 0)) ^ 2 +
          squares (finProdFinEquiv (index, 1)) ^ 2 +
          squares (finProdFinEquiv (index, 2)) ^ 2 +
          squares (finProdFinEquiv (index, 3)) ^ 2) := by
  simp [NaturalPolynomialPresentation.naturalWitnessPolynomial,
    NaturalPolynomialPresentation.primaryIndex,
    NaturalPolynomialPresentation.squareIndex, evalPolynomial,
    evalMonomial_addExponent]
  ring

/-- The explicit integer-polynomial relation obtained from one mathlib polynomial.

Its first equation is the original polynomial after deduplicating witness labels.  One
four-square equation per distinct witness variable forces those integer slots to denote
natural numbers.
-/
noncomputable def NaturalPolynomialPresentation.toEffDiophRel {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) : EffDiophRel free where
  aux := presentation.witnessSupport.card + presentation.witnessSupport.card * 4
  eqs :=
    liftLeftPolynomial
        (rightAux := presentation.witnessSupport.card * 4)
        presentation.deduplicatedCode ::
      List.ofFn presentation.naturalWitnessPolynomial

@[simp]
theorem NaturalPolynomialPresentation.toEffDiophRel_aux {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial) :
    presentation.toEffDiophRel.aux =
      presentation.witnessSupport.card + presentation.witnessSupport.card * 4 := rfl

/-- The explicit relation represents exactly the natural-number zero set of the original
mathlib polynomial. -/
theorem NaturalPolynomialPresentation.realizes_toEffDiophRel {free : ℕ} {β : Type*}
    {polynomial : Poly (Fin free ⊕ β)}
    (presentation : NaturalPolynomialPresentation polynomial)
    (freeAssignment : Fin free → ℕ) :
    presentation.toEffDiophRel.Realizes
        (fun index ↦ Int.ofNat (freeAssignment index)) ↔
      ∃ auxAssignment : β → ℕ,
        polynomial (Sum.elim freeAssignment auxAssignment) = 0 := by
  classical
  constructor
  · rintro ⟨combined, hcombined⟩
    let primary : Fin presentation.witnessSupport.card → ℤ :=
      fun index ↦ combined
        (Fin.castAdd (presentation.witnessSupport.card * 4) index)
    let squares : Fin (presentation.witnessSupport.card * 4) → ℤ :=
      fun index ↦ combined (Fin.natAdd presentation.witnessSupport.card index)
    have hsplit : Fin.append primary squares = combined :=
      append_aux_split combined
    have hsatisfies :
        Satisfies presentation.toEffDiophRel.eqs
          (Fin.append (fun index ↦ Int.ofNat (freeAssignment index))
            (Fin.append primary squares)) := by
      simpa [hsplit] using hcombined
    have hmainFull := hsatisfies
      (liftLeftPolynomial
        (rightAux := presentation.witnessSupport.card * 4)
        presentation.deduplicatedCode)
      (List.mem_cons_self)
    have hmain :
        evalPolynomial presentation.deduplicatedCode
          (Fin.append (fun index ↦ Int.ofNat (freeAssignment index)) primary) = 0 := by
      simpa only [evalPolynomial_liftLeft] using hmainFull
    have hnatural (index : Fin presentation.witnessSupport.card) :
        primary index =
          squares (finProdFinEquiv (index, 0)) ^ 2 +
            squares (finProdFinEquiv (index, 1)) ^ 2 +
            squares (finProdFinEquiv (index, 2)) ^ 2 +
            squares (finProdFinEquiv (index, 3)) ^ 2 := by
      have hmem : presentation.naturalWitnessPolynomial index ∈
          presentation.toEffDiophRel.eqs := by
        apply List.mem_cons_of_mem
        exact List.mem_ofFn.mpr ⟨index, rfl⟩
      have hequation := hsatisfies (presentation.naturalWitnessPolynomial index) hmem
      rw [presentation.eval_naturalWitnessPolynomial, sub_eq_zero] at hequation
      exact hequation
    have hnonnegative (index : Fin presentation.witnessSupport.card) :
        0 ≤ primary index := by
      rw [hnatural index]
      positivity
    let originalAssignment : β → ℕ := fun label ↦
      if hlabel : label ∈ presentation.witnessSupport then
        (primary (presentation.witnessSupport.equivFin ⟨label, hlabel⟩)).toNat
      else 0
    have horiginal (index : Fin presentation.witnessSupport.card) :
        originalAssignment ((presentation.witnessSupport.equivFin.symm index).1) =
          (primary index).toNat := by
      simp [originalAssignment]
    have hcast (index : Fin presentation.witnessSupport.card) :
        Int.ofNat (presentation.supportAssignment originalAssignment index) =
          primary index := by
      rw [NaturalPolynomialPresentation.supportAssignment, horiginal]
      exact Int.toNat_of_nonneg (hnonnegative index)
    have hsupportAssignment :
        (fun index ↦ Int.ofNat
          (presentation.supportAssignment originalAssignment index)) = primary := by
      funext index
      exact hcast index
    have hcorrect :=
      presentation.eval_deduplicatedCode freeAssignment originalAssignment
    rw [hsupportAssignment] at hcorrect
    refine ⟨originalAssignment, ?_⟩
    rw [← hcorrect]
    exact hmain
  · rintro ⟨originalAssignment, hpolynomial⟩
    let primary : Fin presentation.witnessSupport.card → ℤ := fun index ↦
      Int.ofNat (presentation.supportAssignment originalAssignment index)
    have hexists (index : Fin presentation.witnessSupport.card) :
        ∃ a b c d : ℕ,
          a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
            presentation.supportAssignment originalAssignment index :=
      Nat.sum_four_squares _
    choose a b c d hsquares using hexists
    let squares : Fin (presentation.witnessSupport.card * 4) → ℤ := fun index ↦
      let pair := finProdFinEquiv.symm index
      ![(a pair.1 : ℤ), (b pair.1 : ℤ), (c pair.1 : ℤ), (d pair.1 : ℤ)] pair.2
    have hsquaresApply (index : Fin presentation.witnessSupport.card)
        (square : Fin 4) :
        squares (finProdFinEquiv (index, square)) =
          ![(a index : ℤ), (b index : ℤ), (c index : ℤ), (d index : ℤ)] square := by
      simp only [squares]
      rw [Equiv.symm_apply_apply]
    have hsquaresValue (index : Fin presentation.witnessSupport.card) :
        primary index =
          squares (finProdFinEquiv (index, 0)) ^ 2 +
            squares (finProdFinEquiv (index, 1)) ^ 2 +
            squares (finProdFinEquiv (index, 2)) ^ 2 +
            squares (finProdFinEquiv (index, 3)) ^ 2 := by
      have hcast :
          (a index : ℤ) ^ 2 + (b index : ℤ) ^ 2 +
              (c index : ℤ) ^ 2 + (d index : ℤ) ^ 2 =
            Int.ofNat (presentation.supportAssignment originalAssignment index) := by
        have hnat := hsquares index
        norm_cast
        exact congrArg Int.ofNat hnat
      rw [hsquaresApply index 0, hsquaresApply index 1,
        hsquaresApply index 2, hsquaresApply index 3]
      simpa [primary] using hcast.symm
    refine ⟨Fin.append primary squares, ?_⟩
    intro equation hequation
    rcases List.mem_cons.mp hequation with hmain | hnatural
    · subst equation
      rw [evalPolynomial_liftLeft]
      calc
        evalPolynomial presentation.deduplicatedCode
            (Fin.append (fun index ↦ Int.ofNat (freeAssignment index)) primary) =
            polynomial (Sum.elim freeAssignment originalAssignment) := by
          simpa [primary] using
            presentation.eval_deduplicatedCode freeAssignment originalAssignment
        _ = 0 := hpolynomial
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hnatural
      rw [presentation.eval_naturalWitnessPolynomial, sub_eq_zero]
      exact hsquaresValue index

/-! ## From mathlib's proposition-valued API to explicit relation data -/

/-- Every mathlib `Dioph` proof over a finite free-variable block yields explicit sparse
integer-polynomial relation data with a finite auxiliary arity.

This theorem is an existence statement, not a uniform executable compiler from proofs.
That is sufficient for a fixed source predicate: after choosing the finite relation once,
all later instance-to-polynomial compilation remains primitive recursive.
-/
theorem exists_effDiophRel_of_dioph {free : ℕ} {set : Set (Fin free → ℕ)}
    (hdioph : Dioph set) :
    ∃ relation : EffDiophRel free, ∀ assignment : Fin free → ℕ,
      relation.Realizes (fun index ↦ Int.ofNat (assignment index)) ↔ set assignment := by
  rcases hdioph with ⟨β, polynomial, hpolynomial⟩
  let presentation := naturalPolynomialPresentation polynomial
  refine ⟨presentation.toEffDiophRel, ?_⟩
  intro assignment
  exact (presentation.realizes_toEffDiophRel assignment).trans (hpolynomial assignment).symm

/-- Choose explicit effective relation data from a fixed mathlib `Dioph` proof. -/
noncomputable def effDiophRelOfDioph {free : ℕ} {set : Set (Fin free → ℕ)}
    (hdioph : Dioph set) : EffDiophRel free :=
  Classical.choose (exists_effDiophRel_of_dioph hdioph)

/-- The chosen effective relation has exactly the semantics of the source `Dioph` set on
natural assignments. -/
theorem realizes_effDiophRelOfDioph {free : ℕ} {set : Set (Fin free → ℕ)}
    (hdioph : Dioph set) (assignment : Fin free → ℕ) :
    (effDiophRelOfDioph hdioph).Realizes
        (fun index ↦ Int.ofNat (assignment index)) ↔
      set assignment :=
  Classical.choose_spec (exists_effDiophRel_of_dioph hdioph) assignment

end TrinomialUndecidability.Computability.MathlibDiophantineBridge
