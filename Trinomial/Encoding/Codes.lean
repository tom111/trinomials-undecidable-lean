import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Trinomial.Encoding.Generators
import TrinomialUndecidability.Computability.EffectiveDiophantine

/-!
# Codes for polynomial inputs and ideal presentations

This module supplies the `Primcodable` input and output types used in the formal statement
of Corollary 4.6.  A polynomial input is a number of variables together with sparse
integer-polynomial syntax.  An ideal presentation is a number of variables together with
a finite list of rational sparse generators.  Rational coefficients use a first-order code
whose denominator is one more than a stored natural number.  Thus every code is valid and
all operations needed by the semidecision procedures are computable.

The dependent exponent vectors are encoded as ordinary lists together with a primitive
recursive length predicate.  This makes the dependence on the ambient number of variables
visible in the code and prevents ill-sized exponent vectors from decoding.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntPolynomialCode)

/-! ### First-order coefficient and polynomial codes -/

/-- A first-order code for an integer.  The pair `(p, n)` represents `p - n`.
The representation is deliberately not canonical because its arithmetic is primitive
recursive without normalization. -/
abbrev SignedCode := ℕ × ℕ

namespace SignedCode

/-- The integer represented by a signed code. -/
def value (z : SignedCode) : ℤ := (z.1 : ℤ) - (z.2 : ℤ)

/-- The canonical signed code of an integer. -/
def ofInt (z : ℤ) : SignedCode := (z.toNat, (-z).toNat)

@[simp] theorem value_ofInt (z : ℤ) : value (ofInt z) = z :=
  z.toNat_sub_toNat_neg

end SignedCode

/-- A first-order code for a rational number.  The pair `(z, d)` represents
`z / (d + 1)`, where `z` is a `SignedCode`. -/
abbrev RationalCode := SignedCode × ℕ

namespace RationalCode

/-- The positive denominator represented by a rational code. -/
def denominator (q : RationalCode) : ℕ := q.2 + 1

/-- The rational number represented by a rational code. -/
def value (q : RationalCode) : ℚ :=
  mkRat q.1.value q.denominator

/-- The canonical first-order code of a rational number. -/
def ofRat (q : ℚ) : RationalCode :=
  (SignedCode.ofInt q.num, q.den - 1)

@[simp] theorem denominator_ofRat (q : ℚ) : denominator (ofRat q) = q.den := by
  simp only [denominator, ofRat]
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)

@[simp] theorem value_ofRat (q : ℚ) : value (ofRat q) = q := by
  change mkRat (SignedCode.ofInt q.num).value (denominator (ofRat q)) = q
  rw [SignedCode.value_ofInt, denominator_ofRat]
  exact Rat.mkRat_self q

end RationalCode

/-- A rational sparse polynomial in `n` standard variables.  Repeated exponent vectors
are permitted; `CodedPolynomial.toPoly` later sums their coefficients. -/
abbrev CodedPolynomial (n : ℕ) := List (RationalCode × (Fin n → ℕ))

/-- Encoded inputs to Hilbert's tenth problem: the arity and sparse integer-polynomial
syntax. -/
abbrev PolynomialInput := Σ n : ℕ, IntPolynomialCode n

/-- Encoded finite presentations of ideals: the number of variables and a finite list of
rational sparse generators. -/
abbrev IdealPresentation := Σ n : ℕ, List (CodedPolynomial n)

/-! ### Nondependent representations -/

/-- The nondependent representation of `PolynomialInput`. -/
abbrev PolynomialInputRaw := ℕ × List (List ℕ × ℤ)

/-- Every exponent list in a raw polynomial input has the declared arity. -/
def PolynomialInputRaw.Valid (q : PolynomialInputRaw) : Prop :=
  ∀ term ∈ q.2, term.1.length = q.1

/-- Raw polynomial inputs satisfying their exponent-length invariant. -/
abbrev PolynomialInputCode := {q : PolynomialInputRaw // q.Valid}

/-- The nondependent representation of `IdealPresentation`.  The outer list is the
generator list and each inner list is one sparse polynomial. -/
abbrev IdealPresentationRaw := ℕ × List (List (RationalCode × List ℕ))

/-- Every exponent list in a raw presentation has the declared arity. -/
def IdealPresentationRaw.Valid (q : IdealPresentationRaw) : Prop :=
  ∀ term ∈ q.2.flatten, term.2.length = q.1

/-- Raw ideal presentations satisfying their exponent-length invariant. -/
abbrev IdealPresentationCode := {q : IdealPresentationRaw // q.Valid}

/-! ### Exponent vectors and lists -/

/-- Write a dense exponent vector as a list in coordinate order. -/
def exponentList {n : ℕ} (e : Fin n → ℕ) : List ℕ :=
  List.ofFn e

/-- Read the first `n` entries of a list as an exponent vector, using zero only for an
ill-sized raw list.  Valid encoded inputs never use the default. -/
def exponentOfList (n : ℕ) (l : List ℕ) : Fin n → ℕ := fun i => l.getD i 0

@[simp] theorem exponentList_length {n : ℕ} (e : Fin n → ℕ) :
    (exponentList e).length = n :=
  List.length_ofFn

@[simp] theorem exponentOfList_exponentList {n : ℕ} (e : Fin n → ℕ) :
    exponentOfList n (exponentList e) = e := by
  funext i
  rw [exponentOfList, List.getD_eq_getElem]
  simp [exponentList]
  rw [exponentList_length]
  exact i.isLt

theorem exponentList_exponentOfList (n : ℕ) (l : List ℕ) (h : l.length = n) :
    exponentList (exponentOfList n l) = l := by
  subst n
  change List.ofFn (fun i : Fin l.length => l.getD i 0) = l
  rw [show (fun i : Fin l.length => l.getD i 0) = l.get by
    funext i
    exact List.getD_eq_get l 0 i]
  exact List.ofFn_get l

/-! ### Polynomial-input equivalence -/

/-- Encode a dependent polynomial input by ordinary exponent lists. -/
def polynomialInputToCode : PolynomialInput → PolynomialInputCode
  | ⟨n, p⟩ =>
      ⟨(n, p.map fun term => (exponentList term.1, term.2)), by
        intro term hterm
        obtain ⟨source, _, rfl⟩ := List.mem_map.mp hterm
        exact exponentList_length source.1⟩

/-- Decode a valid list representation to dependent exponent vectors. -/
def polynomialInputOfCode (q : PolynomialInputCode) : PolynomialInput :=
  ⟨q.1.1, q.1.2.map fun term => (exponentOfList q.1.1 term.1, term.2)⟩

theorem polynomialInputOfCode_toCode (p : PolynomialInput) :
    polynomialInputOfCode (polynomialInputToCode p) = p := by
  obtain ⟨n, p⟩ := p
  simp only [polynomialInputOfCode, polynomialInputToCode]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  rw [List.map_map]
  exact List.map_id'' (fun term => by
    rcases term with ⟨e, c⟩
    change (exponentOfList n (exponentList e), c) = (e, c)
    exact Prod.ext (exponentOfList_exponentList e) rfl) p

theorem polynomialInputToCode_ofCode (q : PolynomialInputCode) :
    polynomialInputToCode (polynomialInputOfCode q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  dsimp only [polynomialInputToCode, polynomialInputOfCode]
  rw [List.map_map]
  calc
    List.map
        ((fun term => (exponentList term.1, term.2)) ∘
          fun term => (exponentOfList q.1.1 term.1, term.2)) q.1.2 =
        List.map (fun term => term) q.1.2 := by
      apply List.map_congr_left
      intro term hterm
      rcases term with ⟨e, c⟩
      rw [Function.comp_apply]
      exact Prod.ext (exponentList_exponentOfList q.1.1 e (q.2 (e, c) hterm)) rfl
    _ = q.1.2 := List.map_id' _

/-- The coding equivalence used for the `Primcodable PolynomialInput` instance. -/
def polynomialInputEquivCode : PolynomialInput ≃ PolynomialInputCode where
  toFun := polynomialInputToCode
  invFun := polynomialInputOfCode
  left_inv := polynomialInputOfCode_toCode
  right_inv := polynomialInputToCode_ofCode

/-! ### Ideal-presentation equivalence -/

/-- Encode a dependent ideal presentation by ordinary exponent lists. -/
def idealPresentationToCode : IdealPresentation → IdealPresentationCode
  | ⟨N, generators⟩ =>
      ⟨(N, generators.map fun p => p.map fun term => (term.1, exponentList term.2)), by
        intro term hterm
        rw [List.mem_flatten] at hterm
        obtain ⟨p, hp, hterm⟩ := hterm
        obtain ⟨sourcePoly, _, rfl⟩ := List.mem_map.mp hp
        obtain ⟨source, _, rfl⟩ := List.mem_map.mp hterm
        exact exponentList_length source.2⟩

/-- Decode a valid raw ideal presentation. -/
def idealPresentationOfCode (q : IdealPresentationCode) : IdealPresentation :=
  ⟨q.1.1, q.1.2.map fun p => p.map fun term => (term.1, exponentOfList q.1.1 term.2)⟩

theorem idealPresentationOfCode_toCode (q : IdealPresentation) :
    idealPresentationOfCode (idealPresentationToCode q) = q := by
  obtain ⟨N, generators⟩ := q
  simp only [idealPresentationOfCode, idealPresentationToCode]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  rw [List.map_map]
  apply List.map_id''
  intro p
  rw [Function.comp_apply, List.map_map]
  exact List.map_id'' (fun term => by rcases term with ⟨c, e⟩; simp) p

theorem idealPresentationToCode_ofCode (q : IdealPresentationCode) :
    idealPresentationToCode (idealPresentationOfCode q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  dsimp only [idealPresentationToCode, idealPresentationOfCode]
  rw [List.map_map]
  calc
    List.map
        ((fun p => p.map fun term => (term.1, exponentList term.2)) ∘
          fun p => p.map fun term => (term.1, exponentOfList q.1.1 term.2)) q.1.2 =
        List.map (fun p => p) q.1.2 := by
      apply List.map_congr_left
      intro p hp
      rw [Function.comp_apply, List.map_map]
      calc
        List.map
            ((fun term => (term.1, exponentList term.2)) ∘
              fun term => (term.1, exponentOfList q.1.1 term.2)) p =
            List.map (fun term => term) p := by
          apply List.map_congr_left
          intro term hterm
          rcases term with ⟨c, e⟩
          rw [Function.comp_apply]
          change (c, exponentList (exponentOfList q.1.1 e)) = (c, e)
          apply Prod.ext
          · rfl
          apply exponentList_exponentOfList
          exact q.2 (c, e) (List.mem_flatten.mpr ⟨p, hp, hterm⟩)
        _ = p := List.map_id' _
    _ = q.1.2 := List.map_id' _

/-- The coding equivalence used for the `Primcodable IdealPresentation` instance. -/
def idealPresentationEquivCode : IdealPresentation ≃ IdealPresentationCode where
  toFun := idealPresentationToCode
  invFun := idealPresentationOfCode
  left_inv := idealPresentationOfCode_toCode
  right_inv := idealPresentationToCode_ofCode

/-! ### Primitive-recursive validity and instances -/

theorem polynomialInputRaw_valid_primrec : PrimrecPred PolynomialInputRaw.Valid := by
  have hterm : PrimrecRel fun (term : List ℕ × ℤ) (n : ℕ) => term.1.length = n := by
    exact Primrec.eq.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact hterm.forall_mem_list.comp Primrec.snd Primrec.fst

theorem idealPresentationRaw_valid_primrec : PrimrecPred IdealPresentationRaw.Valid := by
  have hterm : PrimrecRel fun (term : RationalCode × List ℕ) (n : ℕ) =>
      term.2.length = n := by
    exact Primrec.eq.comp
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact hterm.forall_mem_list.comp (Primrec.list_flatten.comp Primrec.snd) Primrec.fst

instance instDecidablePolynomialInputRawValid : DecidablePred PolynomialInputRaw.Valid :=
  fun q => by
    change Decidable (∀ term ∈ q.2, term.1.length = q.1)
    exact List.decidableBAll (fun term : List ℕ × ℤ => term.1.length = q.1) q.2

instance instDecidableIdealPresentationRawValid : DecidablePred IdealPresentationRaw.Valid :=
  fun q => by
    change Decidable (∀ term ∈ q.2.flatten, term.2.length = q.1)
    exact List.decidableBAll
      (fun term : RationalCode × List ℕ => term.2.length = q.1) q.2.flatten

instance instPrimcodablePolynomialInputCode : Primcodable PolynomialInputCode :=
  Primcodable.subtype polynomialInputRaw_valid_primrec

instance instPrimcodableIdealPresentationCode : Primcodable IdealPresentationCode :=
  Primcodable.subtype idealPresentationRaw_valid_primrec

instance instPrimcodablePolynomialInput : Primcodable PolynomialInput :=
  Primcodable.ofEquiv PolynomialInputCode polynomialInputEquivCode

instance instPrimcodableIdealPresentation : Primcodable IdealPresentation :=
  Primcodable.ofEquiv IdealPresentationCode idealPresentationEquivCode

@[simp] theorem decode_encode_polynomialInput (p : PolynomialInput) :
    Encodable.decode (Encodable.encode p) = some p :=
  Encodable.encodek p

@[simp] theorem decode_encode_idealPresentation (q : IdealPresentation) :
    Encodable.decode (Encodable.encode q) = some q :=
  Encodable.encodek q

end Trinomial
