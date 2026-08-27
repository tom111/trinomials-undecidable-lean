import Mathlib.Computability.Halting
import Mathlib.RingTheory.Ideal.Operations
import Trinomial.Encoding.Codes
import Trinomial.ShortestPolynomial

/-!
# Semidecision procedures for short polynomials in finitely presented ideals

This module gives first-order arithmetic on the coefficient codes from
`Trinomial.Encoding.Codes`, a decidable sparse-polynomial equality test, and finite
cofactor certificates for ideal membership.  Projecting the certificate predicates proves
that the three presentation problems in Corollary 4.6 are recursively enumerable.
-/

set_option autoImplicit false

namespace Trinomial

/-! ### Arithmetic on signed and rational codes -/

namespace SignedCode

/-- The signed code for zero. -/
def zero : SignedCode := (0, 0)

/-- The signed code for one. -/
def one : SignedCode := (1, 0)

/-- Negation of a signed code. -/
def neg (a : SignedCode) : SignedCode := (a.2, a.1)

/-- Addition of signed codes. -/
def add (a b : SignedCode) : SignedCode := (a.1 + b.1, a.2 + b.2)

/-- Multiplication of signed codes. -/
def mul (a b : SignedCode) : SignedCode :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Multiplication of a signed code by a natural number. -/
def nsmul (a : SignedCode) (d : ℕ) : SignedCode := (a.1 * d, a.2 * d)

/-- Equality of the represented integers without normalizing their codes. -/
def Equivalent (a b : SignedCode) : Prop :=
  a.1 + b.2 = b.1 + a.2

instance instDecidableEquivalent : DecidableRel Equivalent :=
  fun _ _ => Nat.decEq _ _

@[simp] theorem value_zero : zero.value = 0 := by
  simp [zero, value]

@[simp] theorem value_one : one.value = 1 := by
  simp [one, value]

@[simp] theorem value_neg (a : SignedCode) : (neg a).value = -a.value := by
  simp [neg, value]

@[simp] theorem value_add (a b : SignedCode) : (add a b).value = a.value + b.value := by
  simp [add, value]
  ring

@[simp] theorem value_mul (a b : SignedCode) : (mul a b).value = a.value * b.value := by
  simp [mul, value]
  ring

@[simp] theorem value_nsmul (a : SignedCode) (d : ℕ) :
    (nsmul a d).value = a.value * d := by
  simp [nsmul, value]
  ring

theorem equivalent_iff_value_eq (a b : SignedCode) :
    Equivalent a b ↔ a.value = b.value := by
  simp only [Equivalent, value]
  omega

theorem zero_primrec : Primrec fun _ : Unit => zero :=
  Primrec.const zero

theorem one_primrec : Primrec fun _ : Unit => one :=
  Primrec.const one

theorem neg_primrec : Primrec neg :=
  Primrec.pair Primrec.snd Primrec.fst

theorem add_primrec : Primrec₂ add := by
  exact (Primrec.pair
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem mul_primrec : Primrec₂ mul := by
  exact (Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))).to₂

theorem nsmul_primrec : Primrec₂ nsmul := by
  exact (Primrec.pair
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂

theorem equivalent_primrec : PrimrecRel Equivalent := by
  exact Primrec.eq.comp₂
    (Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) (Primrec.snd.comp₂ Primrec₂.right))
    (Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.left))

end SignedCode

namespace RationalCode

/-- The rational code for zero. -/
def zero : RationalCode := (SignedCode.zero, 0)

/-- The rational code for one. -/
def one : RationalCode := (SignedCode.one, 0)

/-- Negation of a rational code. -/
def neg (a : RationalCode) : RationalCode := (SignedCode.neg a.1, a.2)

/-- The stored denominator whose represented denominator is a product. -/
def productDenominatorCode (a b : RationalCode) : ℕ :=
  a.denominator * b.denominator - 1

/-- Addition of rational codes by an unreduced common denominator. -/
def add (a b : RationalCode) : RationalCode :=
  (SignedCode.add (SignedCode.nsmul a.1 b.denominator)
      (SignedCode.nsmul b.1 a.denominator),
    productDenominatorCode a b)

/-- Multiplication of rational codes without fraction reduction. -/
def mul (a b : RationalCode) : RationalCode :=
  (SignedCode.mul a.1 b.1, productDenominatorCode a b)

/-- Equality of represented rationals by cross multiplication. -/
def Equivalent (a b : RationalCode) : Prop :=
  SignedCode.Equivalent
    (SignedCode.nsmul a.1 b.denominator)
    (SignedCode.nsmul b.1 a.denominator)

instance instDecidableEquivalent : DecidableRel Equivalent :=
  fun _ _ => SignedCode.instDecidableEquivalent _ _

theorem denominator_pos (a : RationalCode) : 0 < a.denominator := by
  simp [denominator]

theorem denominator_ne_zero (a : RationalCode) : a.denominator ≠ 0 :=
  (denominator_pos a).ne'

@[simp] theorem denominator_zero : zero.denominator = 1 := rfl

@[simp] theorem denominator_one : one.denominator = 1 := rfl

@[simp] theorem denominator_neg (a : RationalCode) : (neg a).denominator = a.denominator :=
  rfl

@[simp] theorem denominator_productDenominatorCode (a b : RationalCode) :
    productDenominatorCode a b + 1 = a.denominator * b.denominator := by
  apply Nat.sub_add_cancel
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero a.denominator_ne_zero b.denominator_ne_zero)

@[simp] theorem value_zero : zero.value = 0 := by
  simp [zero, value]

@[simp] theorem value_one : one.value = 1 := by
  change mkRat 1 1 = 1
  norm_num

@[simp] theorem value_neg (a : RationalCode) : (neg a).value = -a.value := by
  simp only [neg, value, SignedCode.value_neg]
  exact (Rat.neg_mkRat _ _).symm

@[simp] theorem value_add (a b : RationalCode) : (add a b).value = a.value + b.value := by
  simp only [value]
  simp only [add, denominator, denominator_productDenominatorCode,
    SignedCode.value_add, SignedCode.value_nsmul]
  exact (Rat.mkRat_add_mkRat _ _ a.denominator_ne_zero b.denominator_ne_zero).symm

@[simp] theorem value_mul (a b : RationalCode) : (mul a b).value = a.value * b.value := by
  rw [value, value]
  simp only [mul, denominator, denominator_productDenominatorCode, SignedCode.value_mul]
  exact (Rat.mkRat_mul_mkRat _ _ _ _).symm

theorem equivalent_iff_value_eq (a b : RationalCode) :
    Equivalent a b ↔ a.value = b.value := by
  rw [Equivalent, SignedCode.equivalent_iff_value_eq]
  simp only [SignedCode.value_nsmul, value]
  rw [Rat.mkRat_eq_iff a.denominator_ne_zero b.denominator_ne_zero]

theorem denominator_primrec : Primrec denominator :=
  Primrec.succ.comp Primrec.snd

theorem neg_primrec : Primrec neg :=
  Primrec.pair (SignedCode.neg_primrec.comp Primrec.fst) Primrec.snd

theorem productDenominatorCode_primrec : Primrec₂ productDenominatorCode := by
  exact Primrec.nat_sub.comp
    (Primrec.nat_mul.comp
      (denominator_primrec.comp Primrec.fst) (denominator_primrec.comp Primrec.snd))
    (Primrec.const 1) |>.to₂

theorem add_primrec : Primrec₂ add := by
  have hleft : Primrec fun p : RationalCode × RationalCode =>
      SignedCode.nsmul p.1.1 p.2.denominator :=
    SignedCode.nsmul_primrec.comp
      (Primrec.fst.comp Primrec.fst) (denominator_primrec.comp Primrec.snd)
  have hright : Primrec fun p : RationalCode × RationalCode =>
      SignedCode.nsmul p.2.1 p.1.denominator :=
    SignedCode.nsmul_primrec.comp
      (Primrec.fst.comp Primrec.snd) (denominator_primrec.comp Primrec.fst)
  exact (Primrec.pair
    (SignedCode.add_primrec.comp hleft hright)
    productDenominatorCode_primrec).to₂

theorem mul_primrec : Primrec₂ mul := by
  exact (Primrec.pair
    (SignedCode.mul_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    productDenominatorCode_primrec).to₂

theorem equivalent_primrec : PrimrecRel Equivalent := by
  exact SignedCode.equivalent_primrec.comp₂
    (SignedCode.nsmul_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) (denominator_primrec.comp₂ Primrec₂.right))
    (SignedCode.nsmul_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right) (denominator_primrec.comp₂ Primrec₂.left))

end RationalCode

/-! ### Sparse polynomials and their semantics -/

/-- A nondependent sparse polynomial.  Its exponent lists are checked against an ambient
arity by `RawPolynomial.Valid`. -/
abbrev RawPolynomial := List (RationalCode × List ℕ)

namespace RawPolynomial

/-- Every term of a raw sparse polynomial has the specified number of exponents. -/
def Valid (n : ℕ) (p : RawPolynomial) : Prop :=
  ∀ term ∈ p, term.2.length = n

instance instDecidableValid : DecidableRel Valid :=
  fun n p => List.decidableBAll (fun term : RationalCode × List ℕ => term.2.length = n) p

/-- Interpret a raw sparse polynomial in the standard variables indexed by `Fin n`. -/
noncomputable def toPoly (n : ℕ) (p : RawPolynomial) : MvPolynomial (Fin n) ℚ :=
  (p.map fun term =>
    MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (exponentOfList n term.2)) term.1.value).sum

@[simp] theorem toPoly_nil (n : ℕ) : toPoly n [] = 0 := rfl

@[simp] theorem toPoly_cons (n : ℕ) (term : RationalCode × List ℕ)
    (p : RawPolynomial) :
    toPoly n (term :: p) =
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (exponentOfList n term.2)) term.1.value +
        toPoly n p := by
  simp [toPoly]

/-- The standard semantics of a dependent coded polynomial. -/
noncomputable def codedToPoly {n : ℕ} (p : CodedPolynomial n) :
    MvPolynomial (Fin n) ℚ :=
  (p.map fun term =>
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm term.2) term.1.value).sum

@[simp] theorem codedToPoly_nil (n : ℕ) :
    codedToPoly ([] : CodedPolynomial n) = 0 := rfl

@[simp] theorem codedToPoly_cons {n : ℕ} (term : RationalCode × (Fin n → ℕ))
    (p : CodedPolynomial n) :
    codedToPoly (term :: p) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm term.2) term.1.value +
        codedToPoly p := by
  simp [codedToPoly]

@[simp] theorem toPoly_exponentLists {n : ℕ} (p : CodedPolynomial n) :
    RawPolynomial.toPoly n
        (p.map fun term => (term.1, exponentList term.2)) =
      codedToPoly p := by
  induction p with
  | nil => simp
  | cons term p ih =>
      simp only [List.map_cons, RawPolynomial.toPoly_cons, codedToPoly_cons,
        exponentOfList_exponentList, ih]

/-- Add two exponent lists in exactly `n` coordinates.  Entries beyond the declared
arity are ignored and missing entries are read as zero. -/
def exponentAdd (n : ℕ) (e f : List ℕ) : List ℕ :=
  (List.range n).map fun i => e.getD i 0 + f.getD i 0

theorem exponentAdd_eq_exponentList (n : ℕ) (e f : List ℕ) :
    exponentAdd n e f =
      exponentList fun i => exponentOfList n e i + exponentOfList n f i := by
  apply List.ext_getElem
  · simp [exponentAdd]
  intro i hi h'i
  simp only [exponentAdd, List.getElem_map, List.getElem_range,
    exponentList, List.getElem_ofFn]
  rfl

theorem exponentAdd_primrec :
    Primrec fun input : ℕ × (List ℕ × List ℕ) =>
      exponentAdd input.1 input.2.1 input.2.2 := by
  have he : Primrec₂ fun (input : ℕ × (List ℕ × List ℕ)) (i : ℕ) =>
      input.2.1.getD i 0 :=
    Primrec.list_getD 0 |>.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hf : Primrec₂ fun (input : ℕ × (List ℕ × List ℕ)) (i : ℕ) =>
      input.2.2.getD i 0 :=
    Primrec.list_getD 0 |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.nat_add.comp₂ he hf)

@[simp] theorem exponentOfList_exponentAdd (n : ℕ) (e f : List ℕ) :
    exponentOfList n (exponentAdd n e f) =
      fun i => exponentOfList n e i + exponentOfList n f i := by
  rw [exponentAdd_eq_exponentList]
  exact exponentOfList_exponentList _

/-- Addition is concatenation of sparse term lists. -/
def add (p q : RawPolynomial) : RawPolynomial := p ++ q

/-- Negate every coefficient of a sparse polynomial. -/
def neg (p : RawPolynomial) : RawPolynomial :=
  p.map fun term => (RationalCode.neg term.1, term.2)

/-- Multiply sparse polynomials by distributing termwise. -/
def mul (n : ℕ) (p q : RawPolynomial) : RawPolynomial :=
  p.flatMap fun a =>
    q.map fun b =>
      (RationalCode.mul a.1 b.1, exponentAdd n a.2 b.2)

@[simp] theorem toPoly_add (n : ℕ) (p q : RawPolynomial) :
    toPoly n (add p q) = toPoly n p + toPoly n q := by
  simp [add, toPoly]

@[simp] theorem toPoly_append (n : ℕ) (p q : RawPolynomial) :
    toPoly n (p ++ q) = toPoly n p + toPoly n q :=
  toPoly_add n p q

@[simp] theorem toPoly_neg (n : ℕ) (p : RawPolynomial) :
    toPoly n (neg p) = -toPoly n p := by
  induction p with
  | nil => simp [neg]
  | cons term p ih =>
      rw [show neg (term :: p) = (RationalCode.neg term.1, term.2) :: neg p by rfl]
      rw [toPoly_cons, RationalCode.value_neg, ih, toPoly_cons, neg_add]
      simp

private theorem toPoly_termwiseMul (n : ℕ) (a : RationalCode × List ℕ)
    (q : RawPolynomial) :
    toPoly n
        (q.map fun b =>
          (RationalCode.mul a.1 b.1, exponentAdd n a.2 b.2)) =
      MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm (exponentOfList n a.2)) a.1.value *
        toPoly n q := by
  induction q with
  | nil => simp
  | cons b q ih =>
      simp only [List.map_cons, toPoly_cons, RationalCode.value_mul,
        exponentOfList_exponentAdd, ih, mul_add]
      rw [MvPolynomial.monomial_mul]
      have hexponent :
          Finsupp.equivFunOnFinite.symm
              (fun i => exponentOfList n a.2 i + exponentOfList n b.2 i) =
            Finsupp.equivFunOnFinite.symm (exponentOfList n a.2) +
              Finsupp.equivFunOnFinite.symm (exponentOfList n b.2) := by
        ext i
        simp
      rw [hexponent]

@[simp] theorem toPoly_mul (n : ℕ) (p q : RawPolynomial) :
    toPoly n (mul n p q) = toPoly n p * toPoly n q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      rw [show mul n (a :: p) q =
          (q.map fun b =>
              (RationalCode.mul a.1 b.1, exponentAdd n a.2 b.2)) ++ mul n p q by
        rfl]
      rw [toPoly_append, toPoly_termwiseMul, ih, toPoly_cons, add_mul]

theorem valid_primrec : PrimrecRel Valid := by
  have hterm : PrimrecRel fun (term : RationalCode × List ℕ) (n : ℕ) =>
      term.2.length = n := by
    exact Primrec.eq.comp₂
      (Primrec.list_length.comp₂ (Primrec.snd.comp₂ Primrec₂.left)) Primrec₂.right
  exact hterm.forall_mem_list.swap

theorem valid_tail {n : ℕ} {term : RationalCode × List ℕ} {p : RawPolynomial}
    (h : Valid n (term :: p)) : Valid n p := by
  intro source hsource
  exact h source (List.mem_cons_of_mem term hsource)

theorem valid_head {n : ℕ} {term : RationalCode × List ℕ} {p : RawPolynomial}
    (h : Valid n (term :: p)) : term.2.length = n :=
  h term (by simp)

theorem valid_add {n : ℕ} {p q : RawPolynomial} (hp : Valid n p) (hq : Valid n q) :
    Valid n (add p q) := by
  intro term hterm
  exact (List.mem_append.mp hterm).elim (hp term) (hq term)

theorem valid_neg {n : ℕ} {p : RawPolynomial} (hp : Valid n p) :
    Valid n (neg p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

theorem valid_exponentAdd (n : ℕ) (e f : List ℕ) :
    (exponentAdd n e f).length = n :=
  by simp [exponentAdd]

theorem valid_mul (n : ℕ) (p q : RawPolynomial) : Valid n (mul n p q) := by
  intro term hterm
  change term ∈ p.flatMap (fun a =>
    q.map fun b => (RationalCode.mul a.1 b.1, exponentAdd n a.2 b.2)) at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨a, _, hterm⟩ := hterm
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hterm
  exact valid_exponentAdd n a.2 b.2

/-- The coefficient of a raw exponent list, computed without rational normalization. -/
def coefficient (p : RawPolynomial) (e : List ℕ) : RationalCode :=
  p.foldr
    (fun term result =>
      if term.2 = e then RationalCode.add term.1 result else result)
    RationalCode.zero

@[simp] theorem coefficient_nil (e : List ℕ) : coefficient [] e = RationalCode.zero :=
  rfl

@[simp] theorem coefficient_cons (term : RationalCode × List ℕ) (p : RawPolynomial)
    (e : List ℕ) :
    coefficient (term :: p) e =
      if term.2 = e then RationalCode.add term.1 (coefficient p e) else coefficient p e :=
  rfl

theorem coefficient_eq_zero_of_not_mem {p : RawPolynomial} {e : List ℕ}
    (h : e ∉ p.map Prod.snd) : coefficient p e = RationalCode.zero := by
  induction p with
  | nil => rfl
  | cons term p ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [coefficient_cons, if_neg (Ne.symm h.1), ih h.2]

theorem exponentOfList_injective_of_length {n : ℕ} {e f : List ℕ}
    (he : e.length = n) (hf : f.length = n)
    (h : exponentOfList n e = exponentOfList n f) : e = f := by
  rw [← exponentList_exponentOfList n e he, ← exponentList_exponentOfList n f hf, h]

theorem coeff_toPoly_eq_value_coefficient {n : ℕ} {p : RawPolynomial}
    (hp : Valid n p) {e : List ℕ} (he : e.length = n) :
    MvPolynomial.coeff
        (Finsupp.equivFunOnFinite.symm (exponentOfList n e)) (toPoly n p) =
      (coefficient p e).value := by
  induction p with
  | nil => simp
  | cons term p ih =>
      have hterm := valid_head hp
      have htail := valid_tail hp
      by_cases h : term.2 = e
      · subst e
        simp [ih htail]
      · have hexponent : exponentOfList n term.2 ≠ exponentOfList n e := by
          intro heq
          exact h (exponentOfList_injective_of_length hterm he heq)
        simp [h, hexponent, ih htail]

/-- Sparse equality checks precisely the finitely many exponent lists occurring in either
input. -/
def Equal (p q : RawPolynomial) : Prop :=
  ∀ e ∈ p.map Prod.snd ++ q.map Prod.snd,
    RationalCode.Equivalent (coefficient p e) (coefficient q e)

instance instDecidableEqual : DecidableRel Equal :=
  fun p q =>
    List.decidableBAll
      (fun e => RationalCode.Equivalent (coefficient p e) (coefficient q e))
      (p.map Prod.snd ++ q.map Prod.snd)

theorem add_primrec : Primrec₂ add :=
  Primrec.list_append

theorem neg_primrec : Primrec neg := by
  have hterm : Primrec₂ fun (_ : RawPolynomial) (term : RationalCode × List ℕ) =>
      (RationalCode.neg term.1, term.2) := by
    exact (Primrec.pair
      (RationalCode.neg_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_map Primrec.id hterm

abbrev RawTerm := RationalCode × List ℕ

abbrev MultiplyTermInput := ℕ × (RawTerm × RawTerm)

/-- First-order term multiplication, bundled to simplify the computability proof. -/
def multiplyTerm (input : MultiplyTermInput) : RawTerm :=
  (RationalCode.mul input.2.1.1 input.2.2.1,
    exponentAdd input.1 input.2.1.2 input.2.2.2)

theorem multiplyTermCoefficient_primrec : Primrec fun input : MultiplyTermInput =>
    RationalCode.mul input.2.1.1 input.2.2.1 := by
  exact RationalCode.mul_primrec.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

theorem multiplyTermExponent_primrec : Primrec fun input : MultiplyTermInput =>
    exponentAdd input.1 input.2.1.2 input.2.2.2 := by
  have he : Primrec₂ fun (input : MultiplyTermInput) (i : ℕ) =>
      input.2.1.2.getD i 0 :=
    Primrec.list_getD 0 |>.comp₂
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).comp₂ Primrec₂.left)
      Primrec₂.right
  have hf : Primrec₂ fun (input : MultiplyTermInput) (i : ℕ) =>
      input.2.2.2.getD i 0 :=
    Primrec.list_getD 0 |>.comp₂
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp₂ Primrec₂.left)
      Primrec₂.right
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.nat_add.comp₂ he hf)

theorem multiplyTerm_primrec : Primrec multiplyTerm := by
  exact Primrec.pair multiplyTermCoefficient_primrec
    multiplyTermExponent_primrec

theorem mul_primrec : Primrec fun input : ℕ × (RawPolynomial × RawPolynomial) =>
    mul input.1 input.2.1 input.2.2 := by
  let X := ℕ × (RawPolynomial × RawPolynomial)
  have hinner : Primrec₂ fun (input : X) (a : RationalCode × List ℕ) =>
      input.2.2.map fun b =>
        (RationalCode.mul a.1 b.1, exponentAdd input.1 a.2 b.2) := by
    have hgenerators : Primrec fun z : X × (RationalCode × List ℕ) => z.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hterm : Primrec₂ fun (z : X × (RationalCode × List ℕ))
        (b : RationalCode × List ℕ) =>
        (RationalCode.mul z.2.1 b.1, exponentAdd z.1.1 z.2.2 b.2) := by
      have hinput : Primrec fun w :
          (X × (RationalCode × List ℕ)) × (RationalCode × List ℕ) =>
          (w.1.1.1, (w.1.2, w.2)) :=
        Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
      exact (multiplyTerm_primrec.comp hinput).to₂
    exact (Primrec.list_map hgenerators hterm).to₂
  exact Primrec.list_flatMap (Primrec.fst.comp Primrec.snd) hinner

/-- The sparse sum `Σ hᵢ gᵢ`, truncated to the shorter of the two lists. -/
def linearCombination (n : ℕ) (cofactors generators : List RawPolynomial) : RawPolynomial :=
  (List.range (min cofactors.length generators.length)).flatMap fun i =>
    mul n (cofactors.getD i []) (generators.getD i [])

theorem linearCombination_primrec :
    Primrec fun input : ℕ × (List RawPolynomial × List RawPolynomial) =>
      linearCombination input.1 input.2.1 input.2.2 := by
  let X := ℕ × (List RawPolynomial × List RawPolynomial)
  have hbound : Primrec fun input : X => min input.2.1.length input.2.2.length :=
    Primrec.nat_min.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hcofactor : Primrec₂ fun (input : X) (i : ℕ) => input.2.1.getD i [] :=
    Primrec.list_getD [] |>.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hgenerator : Primrec₂ fun (input : X) (i : ℕ) => input.2.2.getD i [] :=
    Primrec.list_getD [] |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hmulInput : Primrec₂ fun (input : X) (i : ℕ) =>
      (input.1, (input.2.1.getD i [], input.2.2.getD i [])) :=
    Primrec₂.pair.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec₂.pair.comp₂ hcofactor hgenerator)
  exact Primrec.list_flatMap (Primrec.list_range.comp hbound)
    (mul_primrec.comp₂ hmulInput)

theorem toPoly_flatten (n : ℕ) (polynomials : List RawPolynomial) :
    toPoly n polynomials.flatten = (polynomials.map (toPoly n)).sum := by
  induction polynomials with
  | nil => simp
  | cons p polynomials ih =>
      simp [toPoly_append, ih]

@[simp] theorem toPoly_linearCombination (n : ℕ)
    (cofactors generators : List RawPolynomial) :
    toPoly n (linearCombination n cofactors generators) =
      ((List.range (min cofactors.length generators.length)).map fun i =>
        toPoly n (cofactors.getD i []) * toPoly n (generators.getD i [])).sum := by
  rw [linearCombination, List.flatMap_def, toPoly_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp [Function.comp_apply]

theorem valid_linearCombination (n : ℕ) (cofactors generators : List RawPolynomial) :
    Valid n (linearCombination n cofactors generators) := by
  intro term hterm
  rw [linearCombination, List.mem_flatMap] at hterm
  obtain ⟨i, _, hterm⟩ := hterm
  exact valid_mul n _ _ term hterm

theorem coefficient_primrec : Primrec₂ coefficient := by
  let X := RawPolynomial × List ℕ
  have hcondition : PrimrecPred fun z : X × ((RationalCode × List ℕ) × RationalCode) =>
      z.2.1.2 = z.1.2 :=
    Primrec.eq.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  have hadd : Primrec fun z : X × ((RationalCode × List ℕ) × RationalCode) =>
      RationalCode.add z.2.1.1 z.2.2 :=
    RationalCode.add_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ fun (input : X) (termResult :
      (RationalCode × List ℕ) × RationalCode) =>
      if termResult.1.2 = input.2 then
        RationalCode.add termResult.1.1 termResult.2
      else termResult.2 :=
    (Primrec.ite hcondition hadd (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.fst (Primrec.const RationalCode.zero) hstep).to₂

theorem equal_primrec : PrimrecRel Equal := by
  have hterm : Primrec₂ fun (_ : RawPolynomial × RawPolynomial)
      (term : RationalCode × List ℕ) => term.2 :=
    (Primrec.snd.comp Primrec.snd).to₂
  have hleftExponents : Primrec fun pq : RawPolynomial × RawPolynomial =>
      pq.1.map Prod.snd :=
    Primrec.list_map Primrec.fst hterm
  have hrightExponents : Primrec fun pq : RawPolynomial × RawPolynomial =>
      pq.2.map Prod.snd :=
    Primrec.list_map Primrec.snd hterm
  have hexponents : Primrec fun pq : RawPolynomial × RawPolynomial =>
      pq.1.map Prod.snd ++ pq.2.map Prod.snd :=
    Primrec.list_append.comp hleftExponents hrightExponents
  have hcoefficientLeft : Primrec₂ fun (e : List ℕ)
      (pq : RawPolynomial × RawPolynomial) => coefficient pq.1 e :=
    coefficient_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right) Primrec₂.left
  have hcoefficientRight : Primrec₂ fun (e : List ℕ)
      (pq : RawPolynomial × RawPolynomial) => coefficient pq.2 e :=
    coefficient_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left
  have htermEqual : PrimrecRel fun (e : List ℕ) (pq : RawPolynomial × RawPolynomial) =>
      RationalCode.Equivalent (coefficient pq.1 e) (coefficient pq.2 e) :=
    RationalCode.equivalent_primrec.comp₂ hcoefficientLeft hcoefficientRight
  exact htermEqual.forall_mem_list.comp hexponents Primrec.id

theorem equal_iff_toPoly_eq {n : ℕ} {p q : RawPolynomial}
    (hp : Valid n p) (hq : Valid n q) :
    Equal p q ↔ toPoly n p = toPoly n q := by
  constructor
  · intro hequal
    apply MvPolynomial.ext
    intro exponent
    let e := exponentList fun i => exponent i
    have he : e.length = n := exponentList_length _
    have hexponent :
        Finsupp.equivFunOnFinite.symm (exponentOfList n e) = exponent := by
      ext i
      simp [e]
    rw [← hexponent, coeff_toPoly_eq_value_coefficient hp he,
      coeff_toPoly_eq_value_coefficient hq he]
    rw [← RationalCode.equivalent_iff_value_eq]
    by_cases hmem : e ∈ p.map Prod.snd ++ q.map Prod.snd
    · exact hequal e hmem
    · rw [List.mem_append, not_or] at hmem
      rw [coefficient_eq_zero_of_not_mem hmem.1,
        coefficient_eq_zero_of_not_mem hmem.2]
      exact (RationalCode.equivalent_iff_value_eq _ _).mpr rfl
  · intro hpoly e he
    rw [RationalCode.equivalent_iff_value_eq]
    have helength : e.length = n := by
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp he
        exact hp term hterm
      · obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp he
        exact hq term hterm
    rw [← coeff_toPoly_eq_value_coefficient hp helength,
      ← coeff_toPoly_eq_value_coefficient hq helength, hpoly]

end RawPolynomial

/-! ### Canonical sparse representatives and presentation ideals -/

/-- Encode a polynomial by its actual finite support. -/
noncomputable def codeOfPolynomial {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    CodedPolynomial n :=
  f.support.toList.map fun exponent =>
    (RationalCode.ofRat (MvPolynomial.coeff exponent f), fun i => exponent i)

@[simp] theorem codedToPoly_codeOfPolynomial {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    RawPolynomial.codedToPoly (codeOfPolynomial f) = f := by
  classical
  rw [MvPolynomial.as_sum f]
  simp [codeOfPolynomial, RawPolynomial.codedToPoly, List.map_map, Function.comp_def]

theorem codeOfPolynomial_length {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    (codeOfPolynomial f).length = f.support.card := by
  classical
  simp [codeOfPolynomial]

theorem codeOfPolynomial_exponents_nodup {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    ((codeOfPolynomial f).map Prod.snd).Nodup := by
  classical
  simp only [codeOfPolynomial, List.map_map]
  apply List.Nodup.map
  · intro a b h
    ext i
    exact congrFun h i
  · exact f.support.nodup_toList

theorem codeOfPolynomial_coefficients_nonzero {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    ∀ term ∈ codeOfPolynomial f, term.1.value ≠ 0 := by
  classical
  intro term hterm
  obtain ⟨exponent, hexponent, rfl⟩ := List.mem_map.mp hterm
  simp only [RationalCode.value_ofRat]
  exact MvPolynomial.mem_support_iff.mp (Finset.mem_toList.mp hexponent)

theorem codeOfPolynomial_raw_valid {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    RawPolynomial.Valid n
      ((codeOfPolynomial f).map fun term => (term.1, exponentList term.2)) := by
  intro term hterm
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hterm
  exact exponentList_length _

/-! ### Primitive-recursive candidate shapes -/

/-- Boolean duplicate test used to make `List.Nodup` visibly primitive recursive. -/
def listNodupBool {α : Type*} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: l => decide (a ∉ l) && listNodupBool l

theorem listNodupBool_eq_true_iff {α : Type*} [DecidableEq α] (l : List α) :
    listNodupBool l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [listNodupBool]
  | cons a l ih => simp [listNodupBool, ih]

theorem listNodupBool_primrec {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (@listNodupBool α _) := by
  have hmem : PrimrecRel fun (l : List α) (a : α) => a ∈ l :=
    Primrec.eq.exists_mem_list.of_eq fun l a => by simp
  have hnotmem : PrimrecPred fun z : α × (List α × Bool) => z.1 ∉ z.2.1 :=
    (hmem.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).not
  have hstep : Primrec₂ fun (_ : List α) (z : α × (List α × Bool)) =>
      decide (z.1 ∉ z.2.1) && z.2.2 := by
    exact (Primrec.and.comp
      (hnotmem.decide.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const true) hstep).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih =>
        change (decide (a ∉ l) &&
            (List.recOn (id l) true fun b l IH => decide (b ∉ l) && IH)) =
          (decide (a ∉ l) && listNodupBool l)
        rw [ih]

theorem list_nodup_primrec {α : Type*} [Primcodable α] [DecidableEq α] :
    PrimrecPred (@List.Nodup α) :=
  (Primrec.eq.comp listNodupBool_primrec (Primrec.const true)).of_eq
    listNodupBool_eq_true_iff

namespace RawPolynomial

/-- No two written terms have the same exponent list. -/
def DistinctExponents (p : RawPolynomial) : Prop :=
  (p.map Prod.snd).Nodup

/-- Every written coefficient represents a nonzero rational. -/
def CoefficientsNonzero (p : RawPolynomial) : Prop :=
  ∀ term ∈ p, ¬RationalCode.Equivalent term.1 RationalCode.zero

/-- A canonical three-term candidate. -/
def IsTrinomial (p : RawPolynomial) : Prop :=
  p.length = 3 ∧ DistinctExponents p ∧ CoefficientsNonzero p

/-- A canonical nonzero candidate with at most three terms. -/
def IsAtMostThree (p : RawPolynomial) : Prop :=
  0 < p.length ∧ p.length ≤ 3 ∧ DistinctExponents p ∧ CoefficientsNonzero p

instance instDecidableDistinctExponents : DecidablePred DistinctExponents :=
  fun p => inferInstanceAs (Decidable (p.map Prod.snd).Nodup)

instance instDecidableCoefficientsNonzero : DecidablePred CoefficientsNonzero :=
  fun p => by
    change Decidable (∀ term ∈ p,
      ¬RationalCode.Equivalent term.1 RationalCode.zero)
    exact List.decidableBAll
      (fun term : RationalCode × List ℕ =>
        ¬RationalCode.Equivalent term.1 RationalCode.zero) p

instance instDecidableIsTrinomial : DecidablePred IsTrinomial :=
  fun p => by
    unfold IsTrinomial
    infer_instance

instance instDecidableIsAtMostThree : DecidablePred IsAtMostThree :=
  fun p => by
    unfold IsAtMostThree
    infer_instance

theorem distinctExponents_primrec : PrimrecPred DistinctExponents := by
  have hterm : Primrec₂ fun (_ : RawPolynomial) (term : RationalCode × List ℕ) =>
      term.2 :=
    (Primrec.snd.comp Primrec.snd).to₂
  exact list_nodup_primrec.comp (Primrec.list_map Primrec.id hterm)

theorem coefficientsNonzero_primrec : PrimrecPred CoefficientsNonzero := by
  have hterm : PrimrecPred fun term : RationalCode × List ℕ =>
      ¬RationalCode.Equivalent term.1 RationalCode.zero :=
    (RationalCode.equivalent_primrec.comp Primrec.fst
      (Primrec.const RationalCode.zero)).not
  exact hterm.forall_mem_list

theorem isTrinomial_primrec : PrimrecPred IsTrinomial := by
  have hlength : PrimrecPred fun p : RawPolynomial => p.length = 3 :=
    Primrec.eq.comp Primrec.list_length (Primrec.const 3)
  exact hlength.and (distinctExponents_primrec.and coefficientsNonzero_primrec)

theorem isAtMostThree_primrec : PrimrecPred IsAtMostThree := by
  have hpositive : PrimrecPred fun p : RawPolynomial => 0 < p.length :=
    Primrec.nat_lt.comp (Primrec.const 0) Primrec.list_length
  have hbound : PrimrecPred fun p : RawPolynomial => p.length ≤ 3 :=
    Primrec.nat_le.comp Primrec.list_length (Primrec.const 3)
  exact hpositive.and <| hbound.and <|
    distinctExponents_primrec.and coefficientsNonzero_primrec

theorem coefficientsNonzero_iff (p : RawPolynomial) :
    CoefficientsNonzero p ↔ ∀ term ∈ p, term.1.value ≠ 0 := by
  simp only [CoefficientsNonzero, RationalCode.equivalent_iff_value_eq,
    RationalCode.value_zero]

/-- The monomial exponent denoted by a raw exponent list. -/
noncomputable abbrev semanticExponent (n : ℕ) (e : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (exponentOfList n e)

theorem semanticExponents_nodup {n : ℕ} {p : RawPolynomial}
    (hp : Valid n p) (hdistinct : DistinctExponents p) :
    (p.map fun term => semanticExponent n term.2).Nodup := by
  induction p with
  | nil => simp
  | cons term p ih =>
      have hhead := valid_head hp
      have htail := valid_tail hp
      have hdistinct := List.nodup_cons.mp hdistinct
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
        apply hdistinct.1
        apply List.mem_map.mpr
        refine ⟨source, hsource, ?_⟩
        apply exponentOfList_injective_of_length (htail source hsource) hhead
        exact Finsupp.equivFunOnFinite.symm.injective heq
      · exact ih htail hdistinct.2

theorem support_toPoly_eq_toFinset {n : ℕ} {p : RawPolynomial}
    (hp : Valid n p) (hdistinct : DistinctExponents p)
    (hnonzero : CoefficientsNonzero p) :
    (toPoly n p).support =
      (p.map fun term => semanticExponent n term.2).toFinset := by
  classical
  induction p with
  | nil => simp
  | cons term p ih =>
      have htail := valid_tail hp
      have hdistinct := List.nodup_cons.mp hdistinct
      have hnonzeroValue := (coefficientsNonzero_iff (term :: p)).mp hnonzero
      have hheadNonzero := hnonzeroValue term (by simp)
      have htailNonzero : CoefficientsNonzero p := by
        rw [coefficientsNonzero_iff]
        intro source hsource
        exact hnonzeroValue source (List.mem_cons_of_mem term hsource)
      have ih' := ih htail hdistinct.2 htailNonzero
      have hsemantic := semanticExponents_nodup hp
        (List.nodup_cons.mpr hdistinct)
      have hnotmem : semanticExponent n term.2 ∉ (toPoly n p).support := by
        rw [ih']
        simpa using (List.nodup_cons.mp hsemantic).1
      have htailCoeff :
          MvPolynomial.coeff (semanticExponent n term.2) (toPoly n p) = 0 :=
        MvPolynomial.notMem_support_iff.mp hnotmem
      ext exponent
      rw [MvPolynomial.mem_support_iff]
      simp only [toPoly_cons, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial,
        List.map_cons, List.toFinset_cons, Finset.mem_insert]
      by_cases heq :
          Finsupp.equivFunOnFinite.symm (exponentOfList n term.2) = exponent
      · subst exponent
        rw [if_pos rfl, htailCoeff]
        simp [hheadNonzero]
      · rw [if_neg heq, zero_add, ← MvPolynomial.mem_support_iff, ih']
        simp [Ne.symm heq]

theorem supportCard_toPoly_eq_length {n : ℕ} {p : RawPolynomial}
    (hp : Valid n p) (hdistinct : DistinctExponents p)
    (hnonzero : CoefficientsNonzero p) :
    (toPoly n p).support.card = p.length := by
  rw [support_toPoly_eq_toFinset hp hdistinct hnonzero]
  simpa using List.toFinset_card_of_nodup (semanticExponents_nodup hp hdistinct)

/-- The raw canonical sparse representative of a polynomial. -/
noncomputable def rawCodeOfPolynomial {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    RawPolynomial :=
  (codeOfPolynomial f).map fun term => (term.1, exponentList term.2)

@[simp] theorem toPoly_rawCodeOfPolynomial {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    toPoly n (rawCodeOfPolynomial f) = f := by
  rw [rawCodeOfPolynomial, toPoly_exponentLists, codedToPoly_codeOfPolynomial]

theorem rawCodeOfPolynomial_valid {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    Valid n (rawCodeOfPolynomial f) :=
  codeOfPolynomial_raw_valid f

theorem rawCodeOfPolynomial_length {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    (rawCodeOfPolynomial f).length = f.support.card := by
  simp [rawCodeOfPolynomial, codeOfPolynomial_length]

theorem rawCodeOfPolynomial_distinct {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    DistinctExponents (rawCodeOfPolynomial f) := by
  classical
  have hinjective : Function.Injective (@exponentList n) := by
    intro a b h
    apply_fun exponentOfList n at h
    simpa using h
  simpa [DistinctExponents, rawCodeOfPolynomial, List.map_map, Function.comp_def] using
    (codeOfPolynomial_exponents_nodup f).map hinjective

theorem rawCodeOfPolynomial_nonzero {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    CoefficientsNonzero (rawCodeOfPolynomial f) := by
  rw [coefficientsNonzero_iff]
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact codeOfPolynomial_coefficients_nonzero f source hsource

theorem rawCodeOfPolynomial_isTrinomial_iff {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    IsTrinomial (rawCodeOfPolynomial f) ↔ f.support.card = 3 := by
  rw [IsTrinomial, rawCodeOfPolynomial_length]
  simp [rawCodeOfPolynomial_distinct, rawCodeOfPolynomial_nonzero]

theorem rawCodeOfPolynomial_isAtMostThree_iff {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    IsAtMostThree (rawCodeOfPolynomial f) ↔ f ≠ 0 ∧ f.support.card ≤ 3 := by
  rw [IsAtMostThree, rawCodeOfPolynomial_length]
  simp only [rawCodeOfPolynomial_distinct, rawCodeOfPolynomial_nonzero, and_true]
  rw [← MvPolynomial.support_nonempty, Finset.card_pos]

theorem isTrinomial_supportCard {n : ℕ} {p : RawPolynomial} (hp : Valid n p)
    (h : IsTrinomial p) : (toPoly n p).support.card = 3 := by
  rw [supportCard_toPoly_eq_length hp h.2.1 h.2.2, h.1]

theorem isAtMostThree_spec {n : ℕ} {p : RawPolynomial} (hp : Valid n p)
    (h : IsAtMostThree p) :
    toPoly n p ≠ 0 ∧ (toPoly n p).support.card ≤ 3 := by
  have hcard := supportCard_toPoly_eq_length hp h.2.2.1 h.2.2.2
  refine ⟨?_, hcard.trans_le h.2.1⟩
  rw [← MvPolynomial.support_nonempty, ← Finset.card_pos, hcard]
  exact h.1

end RawPolynomial

namespace IdealPresentation

/-- The ideal generated by a finite coded presentation. -/
noncomputable def ideal (q : IdealPresentation) : Ideal (MvPolynomial (Fin q.1) ℚ) :=
  Ideal.span (Set.range fun i : Fin q.2.length =>
    RawPolynomial.codedToPoly (q.2.get i))

/-- A presentation's raw generator list. -/
def rawGenerators (q : IdealPresentation) : List RawPolynomial :=
  (idealPresentationToCode q).1.2

theorem rawGenerators_eq {n : ℕ} (generators : List (CodedPolynomial n)) :
    rawGenerators ⟨n, generators⟩ =
      generators.map fun p => p.map fun term => (term.1, exponentList term.2) :=
  rfl

theorem rawGenerators_valid (q : IdealPresentation) :
    ∀ p ∈ q.rawGenerators, RawPolynomial.Valid q.1 p := by
  intro p hp term hterm
  exact (idealPresentationToCode q).2 term
    (List.mem_flatten.mpr ⟨p, hp, hterm⟩)

@[simp] theorem rawGenerators_length (q : IdealPresentation) :
    q.rawGenerators.length = q.2.length := by
  obtain ⟨n, generators⟩ := q
  simp [rawGenerators_eq]

theorem toPoly_rawGenerator_getD {n : ℕ} (generators : List (CodedPolynomial n))
    (i : ℕ) (hi : i < generators.length) :
    RawPolynomial.toPoly n
        ((rawGenerators ⟨n, generators⟩).getD i []) =
      RawPolynomial.codedToPoly generators[i] := by
  rw [rawGenerators_eq]
  rw [List.getD_eq_getElem _ [] (by simpa using hi), List.getElem_map]
  exact RawPolynomial.toPoly_exponentLists generators[i]

theorem rawGenerator_mem_ideal (q : IdealPresentation) (i : ℕ)
    (hi : i < q.rawGenerators.length) :
    RawPolynomial.toPoly q.1 (q.rawGenerators.getD i []) ∈ q.ideal := by
  obtain ⟨n, generators⟩ := q
  have hi' : i < generators.length := by simpa using hi
  rw [toPoly_rawGenerator_getD generators i hi']
  apply Ideal.subset_span
  exact ⟨⟨i, hi'⟩, rfl⟩

end IdealPresentation

theorem listSum_map_range_eq_finSum {M : Type*} [AddCommMonoid M]
    {n : ℕ} (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [← List.sum_toFinset f List.nodup_range]
  rw [List.toFinset_range, Finset.sum_range]

/-! ### Finite cofactor certificates -/

namespace IdealPresentationCode

/-- The declared arity of a valid raw presentation code. -/
def arity (q : IdealPresentationCode) : ℕ := q.1.1

/-- The generator list of a valid raw presentation code. -/
def polynomials (q : IdealPresentationCode) : List RawPolynomial := q.1.2

/-- The first polynomial stored in a certificate, or zero for an empty certificate. -/
def candidate (q : IdealPresentationCode) : RawPolynomial :=
  q.polynomials.getD 0 []

/-- The remaining polynomials stored in a certificate are its cofactors. -/
def cofactors (q : IdealPresentationCode) : List RawPolynomial :=
  q.polynomials.tail

theorem arity_primrec : Primrec arity :=
  Primrec.fst.comp Primrec.subtype_val

theorem polynomials_primrec : Primrec polynomials :=
  Primrec.snd.comp Primrec.subtype_val

theorem candidate_primrec : Primrec candidate :=
  Primrec.list_getD [] |>.comp polynomials_primrec (Primrec.const 0)

theorem cofactors_primrec : Primrec cofactors :=
  Primrec.list_tail.comp polynomials_primrec

theorem polynomial_valid (q : IdealPresentationCode) {p : RawPolynomial}
    (hp : p ∈ q.polynomials) : RawPolynomial.Valid q.arity p := by
  intro term hterm
  exact q.2 term (List.mem_flatten.mpr ⟨p, hp, hterm⟩)

end IdealPresentationCode

/-- A certificate stores a candidate followed by one cofactor for every generator.  Its
last conjunct checks the sparse identity `f = Σ hᵢgᵢ`. -/
def RawMembershipCertificate (q certificate : IdealPresentationCode) : Prop :=
  q.arity = certificate.arity ∧
    certificate.polynomials.length = q.polynomials.length + 1 ∧
      RawPolynomial.Equal certificate.candidate
        (RawPolynomial.linearCombination q.arity certificate.cofactors q.polynomials)

instance instDecidableRawMembershipCertificate : DecidableRel RawMembershipCertificate :=
  fun q certificate => by
    unfold RawMembershipCertificate
    infer_instance

theorem rawMembershipCertificate_primrec : PrimrecRel RawMembershipCertificate := by
  have harity : PrimrecPred fun qc : IdealPresentationCode × IdealPresentationCode =>
      qc.1.arity = qc.2.arity :=
    Primrec.eq.comp
      (IdealPresentationCode.arity_primrec.comp Primrec.fst)
      (IdealPresentationCode.arity_primrec.comp Primrec.snd)
  have hlength : PrimrecPred fun qc : IdealPresentationCode × IdealPresentationCode =>
      qc.2.polynomials.length = qc.1.polynomials.length + 1 :=
    Primrec.eq.comp
      (Primrec.list_length.comp <|
        IdealPresentationCode.polynomials_primrec.comp Primrec.snd)
      (Primrec.succ.comp <|
        Primrec.list_length.comp <|
          IdealPresentationCode.polynomials_primrec.comp Primrec.fst)
  have hlinearInput : Primrec fun qc : IdealPresentationCode × IdealPresentationCode =>
      (qc.1.arity, (qc.2.cofactors, qc.1.polynomials)) :=
    Primrec.pair
      (IdealPresentationCode.arity_primrec.comp Primrec.fst)
      (Primrec.pair
        (IdealPresentationCode.cofactors_primrec.comp Primrec.snd)
        (IdealPresentationCode.polynomials_primrec.comp Primrec.fst))
  have hequal : PrimrecPred fun qc : IdealPresentationCode × IdealPresentationCode =>
      RawPolynomial.Equal qc.2.candidate
        (RawPolynomial.linearCombination qc.1.arity qc.2.cofactors qc.1.polynomials) :=
    RawPolynomial.equal_primrec.comp
      (IdealPresentationCode.candidate_primrec.comp Primrec.snd)
      (RawPolynomial.linearCombination_primrec.comp hlinearInput)
  exact harity.and (hlength.and hequal)

theorem RawMembershipCertificate.cofactors_length {q certificate : IdealPresentationCode}
    (h : RawMembershipCertificate q certificate) :
    certificate.cofactors.length = q.polynomials.length := by
  unfold RawMembershipCertificate at h
  rw [IdealPresentationCode.cofactors, List.length_tail]
  omega

theorem RawMembershipCertificate.candidate_valid
    {q certificate : IdealPresentationCode}
    (h : RawMembershipCertificate q certificate) :
    RawPolynomial.Valid q.arity certificate.candidate := by
  unfold RawMembershipCertificate at h
  have hnonempty : certificate.polynomials ≠ [] := by
    intro hempty
    rw [hempty] at h
    simp at h
  obtain ⟨head, tail, hpolynomials⟩ := List.exists_cons_of_ne_nil hnonempty
  have hhead : RawPolynomial.Valid certificate.arity head := by
    apply certificate.polynomial_valid
    rw [hpolynomials]
    simp
  rw [h.1]
  change RawPolynomial.Valid certificate.arity (certificate.polynomials.getD 0 [])
  rw [hpolynomials]
  exact hhead

/-- A presentation-level cofactor certificate. -/
def MembershipCertificate (q certificate : IdealPresentation) : Prop :=
  RawMembershipCertificate (idealPresentationToCode q)
    (idealPresentationToCode certificate)

instance instDecidableMembershipCertificate : DecidableRel MembershipCertificate :=
  fun q certificate => by
    unfold MembershipCertificate
    infer_instance

theorem idealPresentationToCode_primrec : Primrec idealPresentationToCode :=
  Primrec.of_equiv

theorem membershipCertificate_primrec : PrimrecRel MembershipCertificate :=
  rawMembershipCertificate_primrec.comp₂
    (idealPresentationToCode_primrec.comp₂ Primrec₂.left)
    (idealPresentationToCode_primrec.comp₂ Primrec₂.right)

theorem membershipCertificate_candidate_mem {q certificate : IdealPresentation}
    (h : MembershipCertificate q certificate) :
    RawPolynomial.toPoly q.1 (idealPresentationToCode certificate).candidate ∈ q.ideal := by
  unfold MembershipCertificate at h
  have hcvalid := h.candidate_valid
  have hcombinationValid := RawPolynomial.valid_linearCombination
    (idealPresentationToCode q).arity
    (idealPresentationToCode certificate).cofactors
    (idealPresentationToCode q).polynomials
  have hequality := (RawPolynomial.equal_iff_toPoly_eq hcvalid hcombinationValid).mp h.2.2
  change RawPolynomial.toPoly (idealPresentationToCode q).arity
      (idealPresentationToCode certificate).candidate ∈ q.ideal
  rw [hequality, RawPolynomial.toPoly_linearCombination]
  rw [h.cofactors_length, min_self]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  apply Ideal.sum_mem
  intro i hi
  apply Ideal.mul_mem_left
  have hi' : i < q.rawGenerators.length := by
    exact Finset.mem_range.mp hi
  simpa [IdealPresentation.rawGenerators, IdealPresentationCode.polynomials,
    IdealPresentationCode.arity] using q.rawGenerator_mem_ideal i hi'

theorem toPoly_getD_ofFn_rawCodeOfPolynomial {n k : ℕ}
    (polynomials : Fin k → MvPolynomial (Fin n) ℚ) (i : ℕ) (hi : i < k) :
    RawPolynomial.toPoly n
        ((List.ofFn fun j => RawPolynomial.rawCodeOfPolynomial (polynomials j)).getD i []) =
      polynomials ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ [] (by simp [hi]), List.getElem_ofFn]
  exact RawPolynomial.toPoly_rawCodeOfPolynomial _

theorem exists_membershipCertificate_of_mem {q : IdealPresentation}
    {f : MvPolynomial (Fin q.1) ℚ} (hf : f ∈ q.ideal) :
    ∃ certificate : IdealPresentation,
      MembershipCertificate q certificate ∧
        (idealPresentationToCode certificate).candidate =
          RawPolynomial.rawCodeOfPolynomial f := by
  obtain ⟨n, generators⟩ := q
  obtain ⟨coefficients, hcoefficients⟩ :=
    (Ideal.mem_span_range_iff_exists_fun.mp hf)
  let cofactors : List RawPolynomial :=
    List.ofFn fun i : Fin generators.length =>
      RawPolynomial.rawCodeOfPolynomial (coefficients i)
  have hcertificateValid : IdealPresentationRaw.Valid
      (n, RawPolynomial.rawCodeOfPolynomial f :: cofactors) := by
    intro term hterm
    rw [List.mem_flatten] at hterm
    obtain ⟨p, hp, hterm⟩ := hterm
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact RawPolynomial.rawCodeOfPolynomial_valid f term hterm
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact RawPolynomial.rawCodeOfPolynomial_valid (coefficients i) term hterm
  let certificateCode : IdealPresentationCode :=
    ⟨(n, RawPolynomial.rawCodeOfPolynomial f :: cofactors), hcertificateValid⟩
  refine ⟨idealPresentationOfCode certificateCode, ?_, ?_⟩
  · unfold MembershipCertificate
    rw [idealPresentationToCode_ofCode]
    unfold RawMembershipCertificate
    refine ⟨rfl, ?_, ?_⟩
    · simp [certificateCode, cofactors, IdealPresentationCode.polynomials,
        idealPresentationToCode]
    · change RawPolynomial.Equal (RawPolynomial.rawCodeOfPolynomial f)
        (RawPolynomial.linearCombination n cofactors
          (IdealPresentation.rawGenerators ⟨n, generators⟩))
      apply (RawPolynomial.equal_iff_toPoly_eq
        (RawPolynomial.rawCodeOfPolynomial_valid f)
        (RawPolynomial.valid_linearCombination n _ _)).mpr
      rw [RawPolynomial.toPoly_rawCodeOfPolynomial,
        RawPolynomial.toPoly_linearCombination]
      simp only [cofactors, List.length_ofFn,
        IdealPresentation.rawGenerators_length, min_self]
      rw [listSum_map_range_eq_finSum]
      symm
      calc
        _ = ∑ i, coefficients i * RawPolynomial.codedToPoly (generators.get i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [toPoly_getD_ofFn_rawCodeOfPolynomial coefficients i i.isLt]
          rw [IdealPresentation.toPoly_rawGenerator_getD generators i i.isLt]
          congr
        _ = f := hcoefficients
  · rw [idealPresentationToCode_ofCode]
    simp [certificateCode, IdealPresentationCode.candidate,
      IdealPresentationCode.polynomials]

/-! ### The three recursively enumerable presentation problems -/

/-- Problem (A): the presented ideal contains a polynomial with exactly three terms. -/
def ContainsTrinomial (q : IdealPresentation) : Prop :=
  ∃ f ∈ q.ideal, f.support.card = 3

/-- Problem (B): the presented ideal contains a nonzero polynomial with at most three
terms. -/
def ContainsAtMostThree (q : IdealPresentation) : Prop :=
  HasShortPoly 3 q.ideal

/-- A certificate for problem (A). -/
def TrinomialCertificate (q certificate : IdealPresentation) : Prop :=
  MembershipCertificate q certificate ∧
    RawPolynomial.IsTrinomial (idealPresentationToCode certificate).candidate

/-- A certificate for problem (B). -/
def AtMostThreeCertificate (q certificate : IdealPresentation) : Prop :=
  MembershipCertificate q certificate ∧
    RawPolynomial.IsAtMostThree (idealPresentationToCode certificate).candidate

instance instDecidableTrinomialCertificate : DecidableRel TrinomialCertificate :=
  fun q certificate => by
    unfold TrinomialCertificate
    infer_instance

instance instDecidableAtMostThreeCertificate : DecidableRel AtMostThreeCertificate :=
  fun q certificate => by
    unfold AtMostThreeCertificate
    infer_instance

theorem trinomialCertificate_primrec : PrimrecRel TrinomialCertificate := by
  have hshape : PrimrecRel fun (_ : IdealPresentation) (certificate : IdealPresentation) =>
      RawPolynomial.IsTrinomial (idealPresentationToCode certificate).candidate :=
    RawPolynomial.isTrinomial_primrec.comp <|
      IdealPresentationCode.candidate_primrec.comp <|
        idealPresentationToCode_primrec.comp Primrec.snd
  exact membershipCertificate_primrec.and hshape

theorem atMostThreeCertificate_primrec : PrimrecRel AtMostThreeCertificate := by
  have hshape : PrimrecRel fun (_ : IdealPresentation) (certificate : IdealPresentation) =>
      RawPolynomial.IsAtMostThree (idealPresentationToCode certificate).candidate :=
    RawPolynomial.isAtMostThree_primrec.comp <|
      IdealPresentationCode.candidate_primrec.comp <|
        idealPresentationToCode_primrec.comp Primrec.snd
  exact membershipCertificate_primrec.and hshape

theorem containsTrinomial_iff_certificate (q : IdealPresentation) :
    ContainsTrinomial q ↔ ∃ certificate, TrinomialCertificate q certificate := by
  constructor
  · rintro ⟨f, hf, hcard⟩
    obtain ⟨certificate, hcertificate, hcanonical⟩ :=
      exists_membershipCertificate_of_mem hf
    refine ⟨certificate, hcertificate, ?_⟩
    rw [hcanonical]
    exact (RawPolynomial.rawCodeOfPolynomial_isTrinomial_iff f).mpr hcard
  · rintro ⟨certificate, hmembership, hshape⟩
    let candidate := (idealPresentationToCode certificate).candidate
    have hraw : RawMembershipCertificate (idealPresentationToCode q)
        (idealPresentationToCode certificate) := hmembership
    have hvalid := hraw.candidate_valid
    refine ⟨RawPolynomial.toPoly q.1 candidate,
      membershipCertificate_candidate_mem hmembership, ?_⟩
    exact RawPolynomial.isTrinomial_supportCard hvalid hshape

theorem containsAtMostThree_iff_certificate (q : IdealPresentation) :
    ContainsAtMostThree q ↔ ∃ certificate, AtMostThreeCertificate q certificate := by
  constructor
  · rintro ⟨f, hf, hf0, hcard⟩
    obtain ⟨certificate, hcertificate, hcanonical⟩ :=
      exists_membershipCertificate_of_mem hf
    refine ⟨certificate, hcertificate, ?_⟩
    rw [hcanonical]
    exact (RawPolynomial.rawCodeOfPolynomial_isAtMostThree_iff f).mpr ⟨hf0, hcard⟩
  · rintro ⟨certificate, hmembership, hshape⟩
    let candidate := (idealPresentationToCode certificate).candidate
    have hraw : RawMembershipCertificate (idealPresentationToCode q)
        (idealPresentationToCode certificate) := hmembership
    have hvalid := hraw.candidate_valid
    have hspec := RawPolynomial.isAtMostThree_spec hvalid hshape
    exact ⟨RawPolynomial.toPoly q.1 candidate,
      membershipCertificate_candidate_mem hmembership, hspec.1, hspec.2⟩

theorem containsTrinomial_iff_containsAtMostThree_of_no_two (q : IdealPresentation)
    (h2 : ¬HasShortPoly 2 q.ideal) :
    ContainsTrinomial q ↔ ContainsAtMostThree q := by
  constructor
  · rintro ⟨f, hf, hcard⟩
    refine ⟨f, hf, ?_, by omega⟩
    intro hf0
    rw [hf0] at hcard
    simp at hcard
  · rintro ⟨f, hf, hf0, hcard⟩
    refine ⟨f, hf, ?_⟩
    by_contra hne
    have hle : f.support.card ≤ 2 := by omega
    exact h2 ⟨f, hf, hf0, hle⟩

/-- The promise in problem (C).  It is kept as a predicate rather than made part of the
encoded input type, since recognizing the promise is not itself assumed computable. -/
def TinvThreeOrFour (q : IdealPresentation) : Prop :=
  tinv q.ideal = 3 ∨ tinv q.ideal = 4

/-- The semidecision language used for problem (C).  On promised inputs it is exactly the
question whether `tinv = 3`. -/
def TinvThreeProblem (q : IdealPresentation) : Prop :=
  ContainsTrinomial q

theorem tinvThreeProblem_iff (q : IdealPresentation) (hpromise : TinvThreeOrFour q) :
    TinvThreeProblem q ↔ tinv q.ideal = 3 := by
  have h2 : ¬HasShortPoly 2 q.ideal := by
    intro hshort
    have hle : tinv q.ideal ≤ 2 := tinv_le_iff.mpr hshort
    rcases hpromise with h | h <;> rw [h] at hle <;> norm_num at hle
  rw [TinvThreeProblem,
    containsTrinomial_iff_containsAtMostThree_of_no_two q h2,
    ContainsAtMostThree, ← tinv_le_iff]
  rcases hpromise with h | h
  · simp [h]
  · rw [h]
    norm_num

/-! ### Projection to recursively enumerable predicates -/

/-- The existential projection of a primitive-recursive relation is recursively
enumerable. -/
theorem PrimrecRel.re_exists_right {α β : Type*} [Primcodable α] [Primcodable β]
    {relation : α → β → Prop} [DecidableRel relation] (hrelation : PrimrecRel relation) :
    REPred fun a => ∃ b, relation a b := by
  let test : α → ℕ → Bool := fun a n =>
    match @Encodable.decode β _ n with
    | some b => decide (relation a b)
    | none => false
  have htest : Primrec₂ test := by
    have hsome : Primrec₂ fun (input : α × ℕ) (b : β) =>
        decide (relation input.1 b) :=
      hrelation.decide.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
    exact (Primrec.option_casesOn
      (Primrec.decode.comp Primrec.snd) (Primrec.const false) hsome).of_eq
        fun ⟨a, n⟩ => by
          cases hdecode : @Encodable.decode β _ n <;> simp [test, hdecode]
  have hsearch : Partrec fun a => Nat.rfind fun n => Part.some (test a n) :=
    Partrec.rfind htest.to_comp.partrec₂
  apply hsearch.dom_re.of_eq
  intro a
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, _⟩
    rw [Part.mem_some_iff] at hn
    dsimp only [test] at hn
    split at hn
    · rename_i b hdecode
      exact ⟨b, of_decide_eq_true hn.symm⟩
    · cases hn
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, ?_, fun {_} _ => Part.some_dom _⟩
    rw [Part.mem_some_iff]
    simp [test, hb]

theorem containsTrinomial_re : REPred ContainsTrinomial :=
  (PrimrecRel.re_exists_right trinomialCertificate_primrec).of_eq fun q =>
    (containsTrinomial_iff_certificate q).symm

theorem containsAtMostThree_re : REPred ContainsAtMostThree :=
  (PrimrecRel.re_exists_right atMostThreeCertificate_primrec).of_eq fun q =>
    (containsAtMostThree_iff_certificate q).symm

theorem tinvThreeProblem_re : REPred TinvThreeProblem := by
  exact containsTrinomial_re

end Trinomial
