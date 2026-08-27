import Mathlib.Computability.Reduce
import Mathlib.Data.Int.NatAbs
import Trinomial.Encoding.MainTheorem
import Trinomial.Encoding.Semidecision

/-!
# A computable compiler to finite ideal presentations

This module implements the compiler used in Corollary 4.6 on the first-order
coefficient codes of `Trinomial.Encoding.Codes`.  Its intermediate matrices and vectors
are lists of `RationalCode`, rather than functions with values in `ℚ`.  The decoding
lemmas identify every stage with the executable generator construction in
`Trinomial.Encoding.Generators`.

The generators produced there are written in the point coordinates
`s = 2S - 1`, `t = 2T - 1`, and `c_i = D_i - 1`.  The last compiler pass expands these
coordinates and returns a presentation in the standard variables `S, T, D_i`.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntPolynomialCode)

/-! ### Remaining arithmetic on first-order coefficient codes -/

namespace SignedCode

/-- Absolute value of the represented integer, computed without normalization. -/
def natAbs (a : SignedCode) : ℕ :=
  (a.1 - a.2) + (a.2 - a.1)

/-- Whether the represented integer is strictly negative. -/
def isNegative (a : SignedCode) : Bool :=
  a.1 < a.2

@[simp] theorem natAbs_value (a : SignedCode) :
    natAbs a = a.value.natAbs := by
  rcases le_total a.1 a.2 with h | h
  · rw [natAbs, Nat.sub_eq_zero_of_le h, zero_add]
    symm
    exact Int.natAbs_natCast_sub_natCast_of_le h
  · rw [natAbs, Nat.sub_eq_zero_of_le h, add_zero]
    symm
    exact Int.natAbs_natCast_sub_natCast_of_ge h

theorem neg_ofInt (z : ℤ) : neg (ofInt z) = ofInt (-z) := by
  simp only [neg, ofInt, Int.neg_neg]

/-- Conversion of the constructive integer encoding to signed-pair form is primitive
recursive. -/
theorem ofInt_primrec : Primrec ofInt := by
  rw [Primrec.ofNat_iff]
  let f : ℕ → SignedCode := fun n =>
    bif n.bodd then (0, n.div2 + 1) else (n.div2, 0)
  have hf : Primrec f := by
    exact Primrec.cond Primrec.nat_bodd
      (Primrec.pair (Primrec.const 0) (Primrec.succ.comp Primrec.nat_div2))
      (Primrec.pair Primrec.nat_div2 (Primrec.const 0))
  apply hf.of_eq
  intro n
  change f n = ofInt (Denumerable.ofNat ℤ n)
  rw [show Denumerable.ofNat ℤ n = Equiv.intEquivNat.symm n by rfl]
  conv_lhs => rw [← Nat.bit_bodd_div2 n]
  conv_rhs => rw [← Nat.bit_bodd_div2 n]
  cases n.bodd <;>
    simp [f, ofInt, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
      Equiv.natSumNatEquivNat, Equiv.boolProdNatEquivNat]

theorem natAbs_primrec : Primrec natAbs := by
  exact Primrec.nat_add.comp
    (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
    (Primrec.nat_sub.comp Primrec.snd Primrec.fst)

theorem isNegative_primrec : Primrec isNegative := by
  exact Primrec.nat_lt.decide.comp Primrec.fst Primrec.snd

end SignedCode

namespace RationalCode

/-- The rational code for `2`. -/
def two : RationalCode := ((2, 0), 0)

/-- Reciprocal of a rational code.  The reciprocal of zero is defined to be zero, as in
the field structure on `ℚ`. -/
def inv (a : RationalCode) : RationalCode :=
  if a.1.1 = a.1.2 then zero
  else if a.1.1 < a.1.2 then
    ((0, a.denominator), a.1.2 - a.1.1 - 1)
  else
    ((a.denominator, 0), a.1.1 - a.1.2 - 1)

/-- Division of rational codes. -/
def div (a b : RationalCode) : RationalCode :=
  mul a (inv b)

@[simp] theorem value_two : two.value = 2 := by
  norm_num [two, value, SignedCode.value, denominator]

@[simp] theorem value_inv (a : RationalCode) : (inv a).value = a.value⁻¹ := by
  by_cases hzero : a.1.1 = a.1.2
  · rw [inv, if_pos hzero, value_zero]
    have : a.value = 0 := by
      simp [value, SignedCode.value, hzero]
    simp [this]
  · rw [inv, if_neg hzero]
    by_cases hneg : a.1.1 < a.1.2
    · rw [if_pos hneg]
      have hdiff : 0 < a.1.2 - a.1.1 := Nat.sub_pos_of_lt hneg
      simp only [value, SignedCode.value, denominator]
      rw [Nat.sub_add_cancel hdiff, Rat.inv_mkRat]
      rw [Rat.mkRat_eq_divInt]
      have hz : ((a.1.1 : ℤ) - a.1.2) = -((a.1.2 - a.1.1 : ℕ) : ℤ) := by
        omega
      rw [hz, Rat.divInt_neg]
      simp
    · rw [if_neg hneg]
      have hlt : a.1.2 < a.1.1 :=
        lt_of_le_of_ne (Nat.le_of_not_gt hneg) (Ne.symm hzero)
      have hdiff : 0 < a.1.1 - a.1.2 := Nat.sub_pos_of_lt hlt
      simp only [value, SignedCode.value, denominator]
      rw [Nat.sub_add_cancel hdiff, Rat.inv_mkRat]
      rw [Rat.mkRat_eq_divInt]
      have hz : ((a.1.1 : ℤ) - a.1.2) = ((a.1.1 - a.1.2 : ℕ) : ℤ) := by
        omega
      rw [hz]
      simp

@[simp] theorem value_div (a b : RationalCode) :
    (div a b).value = a.value / b.value := by
  simp [div, div_eq_mul_inv]

theorem inv_primrec : Primrec inv := by
  have heq : PrimrecPred fun a : RationalCode => a.1.1 = a.1.2 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hlt : PrimrecPred fun a : RationalCode => a.1.1 < a.1.2 :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hnegative : Primrec (fun a : RationalCode =>
      (((0, a.denominator), a.1.2 - a.1.1 - 1) : RationalCode)) := by
    exact Primrec.pair
      (Primrec.pair (Primrec.const 0) denominator_primrec)
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
        (Primrec.const 1))
  have hpositive : Primrec (fun a : RationalCode =>
      (((a.denominator, 0), a.1.1 - a.1.2 - 1) : RationalCode)) := by
    exact Primrec.pair
      (Primrec.pair denominator_primrec (Primrec.const 0))
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
        (Primrec.const 1))
  exact Primrec.ite heq (Primrec.const zero)
    (Primrec.ite hlt hnegative hpositive)

theorem div_primrec : Primrec₂ div :=
  mul_primrec.comp₂ Primrec₂.left (inv_primrec.comp₂ Primrec₂.right)

end RationalCode

/-! ### First-order straight-line programs -/

/-- A degree-two equation with natural-number variable indices.  A quadratic term is
stored as `((coefficient, firstIndex), secondIndex)`. -/
abbrev EquationCode :=
  List ((SignedCode × ℕ) × ℕ) × (List (SignedCode × ℕ) × SignedCode)

/-- A straight-line program code: auxiliary-variable count, gate list, and output index. -/
abbrev ProgramCode := ℕ × (List EquationCode × ℕ)

instance instPrimcodableEquationCode : Primcodable EquationCode :=
  inferInstanceAs (Primcodable
    (List ((SignedCode × ℕ) × ℕ) × (List (SignedCode × ℕ) × SignedCode)))

instance instPrimcodableProgramCode : Primcodable ProgramCode :=
  inferInstanceAs (Primcodable (ℕ × (List EquationCode × ℕ)))

namespace EquationCode

/-- Encode a semantic degree-two equation by forgetting the proofs on its finite
indices. -/
def ofEquation {r : ℕ} (F : DegreeTwoEquation r) : EquationCode :=
  (F.quad.map fun term => ((SignedCode.ofInt term.1, term.2.1.val), term.2.2.val),
    F.lin.map fun term => (SignedCode.ofInt term.1, term.2.val),
    SignedCode.ofInt F.const)

/-- Rename every variable index in an equation code. -/
def rename (f : ℕ → ℕ) (F : EquationCode) : EquationCode :=
  (F.1.map fun term => ((term.1.1, f term.1.2), f term.2),
    F.2.1.map fun term => (term.1, f term.2), F.2.2)

/-- The gate `x_o = a`. -/
def eqConst (o : ℕ) (a : SignedCode) : EquationCode :=
  ([], ([(SignedCode.one, o)], SignedCode.neg a))

/-- The gate `x_o = x_i + x_j`. -/
def eqAdd (o i j : ℕ) : EquationCode :=
  ([], ([(SignedCode.one, o), (SignedCode.neg SignedCode.one, i),
    (SignedCode.neg SignedCode.one, j)], SignedCode.zero))

/-- The gate `x_o = x_i x_j`. -/
def eqMul (o i j : ℕ) : EquationCode :=
  ([((SignedCode.neg SignedCode.one, i), j)],
    ([(SignedCode.one, o)], SignedCode.zero))

/-- The gate `x_o = x_i`. -/
def eqCopy (o i : ℕ) : EquationCode :=
  ([], ([(SignedCode.one, o), (SignedCode.neg SignedCode.one, i)], SignedCode.zero))

/-- The gate `x_o = c x_i`. -/
def eqScale (o : ℕ) (c : SignedCode) (i : ℕ) : EquationCode :=
  ([], ([(SignedCode.one, o), (SignedCode.neg c, i)], SignedCode.zero))

/-- The equation `x_o = 0`. -/
def eqZero (o : ℕ) : EquationCode :=
  ([], ([(SignedCode.one, o)], SignedCode.zero))

/-- Shift the auxiliary-variable part of an index by `k`, leaving the first `n`
input indices fixed. -/
def shiftAux (n k i : ℕ) : ℕ :=
  if i < n then i else i + k

/-- The Pell equation in a guarded system with `r` old variables. -/
def pell (r : ℕ) : EquationCode :=
  ([((SignedCode.one, r), r), (((0, 3), r + 1), r + 1)],
    ([], ((0, 1))))

/-- The four-squares equation in a guarded system with `r` old variables. -/
def squares (r : ℕ) : EquationCode :=
  (((List.range r).map fun i => ((SignedCode.one, i), i)) ++
      ((List.range 4).map fun j => ((SignedCode.one, r + 2 + j), r + 2 + j)),
    ([(SignedCode.neg SignedCode.one, r)], SignedCode.zero))

end EquationCode

namespace ProgramCode

/-- Encode a semantic straight-line program. -/
def ofProgram {n : ℕ} (program : StraightLineProgram n) : ProgramCode :=
  (program.k, (program.gates.map EquationCode.ofEquation, program.out.val))

/-- The program with one constant gate. -/
def const (n : ℕ) (a : SignedCode) : ProgramCode :=
  (1, ([EquationCode.eqConst n a], n))

/-- The program copying the input at index `i`. -/
def var (n i : ℕ) : ProgramCode :=
  (1, ([EquationCode.eqCopy n i], n))

/-- Put two programs into disjoint auxiliary-variable blocks and append a binary gate. -/
def binary (gate : ℕ → ℕ → ℕ → EquationCode) (n : ℕ)
    (left right : ProgramCode) : ProgramCode :=
  let k := left.1 + right.1 + 1
  let renameRight := EquationCode.rename (EquationCode.shiftAux n left.1)
  (k, (left.2.1 ++ right.2.1.map renameRight ++
      [gate (n + left.1 + right.1) left.2.2
        (EquationCode.shiftAux n left.1 right.2.2)],
    n + left.1 + right.1))

/-- Put two programs into disjoint auxiliary-variable blocks and append an addition
gate. -/
def add (n : ℕ) (left right : ProgramCode) : ProgramCode :=
  binary EquationCode.eqAdd n left right

/-- Put two programs into disjoint auxiliary-variable blocks and append a
multiplication gate. -/
def mul (n : ℕ) (left right : ProgramCode) : ProgramCode :=
  binary EquationCode.eqMul n left right

/-- Append a scaling gate. -/
def scale (n : ℕ) (c : SignedCode) (program : ProgramCode) : ProgramCode :=
  (program.1 + 1,
    (program.2.1 ++
      [EquationCode.eqScale (n + program.1) c program.2.2], n + program.1))

/-- Append a multiplication by an input variable. -/
def mulVar (n : ℕ) (program : ProgramCode) (i : ℕ) : ProgramCode :=
  (program.1 + 1,
    (program.2.1 ++
      [EquationCode.eqMul (n + program.1) program.2.2 i], n + program.1))

/-- One iteration step, with the parameters bundled in primitive-recursion order. -/
def iterateMulVarStep (input : ℕ × (ℕ × ProgramCode)) : ProgramCode :=
  mulVar input.1 input.2.2 input.2.1

/-- Iterate multiplication by one input variable. -/
def iterateMulVar (n i : ℕ) : ℕ → ProgramCode → ProgramCode
  | 0, program => program
  | steps + 1, program => iterateMulVarStep (n, i, iterateMulVar n i steps program)

/-- The program computing `x_i^power`. -/
def pow (n i : ℕ) : ℕ → ProgramCode
  | 0 => const n SignedCode.one
  | power + 1 =>
      if power = 0 then var n i else mulVar n (pow n i power) i

/-- The raw counterpart of `StraightLineProgram.monomialAux`. -/
def monomialAux (n : ℕ) (exponents indices : List ℕ) : Option ProgramCode :=
  indices.foldr
    (fun i result =>
      match result with
      | none =>
          if exponents.getD i 0 = 0 then none
          else some (pow n i (exponents.getD i 0))
      | some program =>
          some (iterateMulVar n i (exponents.getD i 0) program))
    none

@[simp] theorem monomialAux_nil (n : ℕ) (exponents : List ℕ) :
    monomialAux n exponents [] = none := rfl

@[simp] theorem monomialAux_cons (n : ℕ) (exponents : List ℕ) (i : ℕ)
    (indices : List ℕ) :
    monomialAux n exponents (i :: indices) =
      match monomialAux n exponents indices with
      | none =>
          if exponents.getD i 0 = 0 then none
          else some (pow n i (exponents.getD i 0))
      | some program =>
          some (iterateMulVar n i (exponents.getD i 0) program) := by
  simp [monomialAux]

/-- The program computing a monomial whose dense exponent vector is an ordinary list. -/
def monomial (n : ℕ) (exponents : List ℕ) : ProgramCode :=
  (monomialAux n exponents (List.range n)).getD (const n SignedCode.one)

/-- Compile one sparse term. -/
def termProgram (n : ℕ) (term : List ℕ × ℤ) : ProgramCode :=
  scale n (SignedCode.ofInt term.2) (monomial n term.1)

/-- Compile a nonempty sparse polynomial, using `none` only for the empty list. -/
def ofPolynomialAux (n : ℕ) (polynomial : List (List ℕ × ℤ)) : Option ProgramCode :=
  polynomial.foldr
    (fun term result =>
      some <| match result with
        | none => termProgram n term
        | some program => add n (termProgram n term) program)
    none

/-- Compile sparse integer-polynomial syntax represented with exponent lists. -/
def ofPolynomial (n : ℕ) (polynomial : List (List ℕ × ℤ)) : ProgramCode :=
  (ofPolynomialAux n polynomial).getD (const n SignedCode.zero)

@[simp] theorem ofPolynomialAux_nil (n : ℕ) : ofPolynomialAux n [] = none := rfl

@[simp] theorem ofPolynomialAux_cons (n : ℕ) (term : List ℕ × ℤ)
    (polynomial : List (List ℕ × ℤ)) :
    ofPolynomialAux n (term :: polynomial) =
      some (match ofPolynomialAux n polynomial with
        | none => termProgram n term
        | some program => add n (termProgram n term) program) := by
  simp [ofPolynomialAux]

theorem ofPolynomialAux_eq_some_ofPolynomial (n : ℕ) (term : List ℕ × ℤ)
    (polynomial : List (List ℕ × ℤ)) :
    ofPolynomialAux n (term :: polynomial) =
      some (ofPolynomial n (term :: polynomial)) := by
  rw [ofPolynomial, ofPolynomialAux_cons]
  rfl

/-- Append the output-zero equation of Lemma 4.1. -/
def degreeTwoSystem (n : ℕ) (polynomial : List (List ℕ × ℤ)) :
    ℕ × List EquationCode :=
  let program := ofPolynomial n polynomial
  (n + program.1, program.2.1 ++ [EquationCode.eqZero program.2.2])

/-- Add the six variables and the two equations of Lemma 4.2. -/
def guardedSystem (n : ℕ) (polynomial : List (List ℕ × ℤ)) :
    ℕ × List EquationCode :=
  let system := degreeTwoSystem n polynomial
  let r := system.1
  (r + 6, system.2 ++ [EquationCode.pell r, EquationCode.squares r])

end ProgramCode

/-! ### Correctness of the first-order straight-line program -/

namespace EquationCode

@[simp] theorem ofInt_zero : SignedCode.ofInt 0 = SignedCode.zero := rfl
@[simp] theorem ofInt_one : SignedCode.ofInt 1 = SignedCode.one := rfl
@[simp] theorem ofInt_neg_one : SignedCode.ofInt (-1) = SignedCode.neg SignedCode.one := rfl

@[simp] theorem ofEquation_eqConst {r : ℕ} (o : Fin r) (a : ℤ) :
    ofEquation (DegreeTwoEquation.eqConst o a) = eqConst o.val (SignedCode.ofInt a) := by
  simp [ofEquation, DegreeTwoEquation.eqConst, eqConst, SignedCode.neg_ofInt]

@[simp] theorem ofEquation_eqAdd {r : ℕ} (o i j : Fin r) :
    ofEquation (DegreeTwoEquation.eqAdd o i j) = eqAdd o.val i.val j.val := by
  simp [ofEquation, DegreeTwoEquation.eqAdd, eqAdd]

@[simp] theorem ofEquation_eqMul {r : ℕ} (o i j : Fin r) :
    ofEquation (DegreeTwoEquation.eqMul o i j) = eqMul o.val i.val j.val := by
  simp [ofEquation, DegreeTwoEquation.eqMul, eqMul]

@[simp] theorem ofEquation_eqZero {r : ℕ} (o : Fin r) :
    ofEquation (DegreeTwoEquation.eqZero o) = eqZero o.val := by
  simp [ofEquation, DegreeTwoEquation.eqZero, eqZero]

@[simp] theorem ofEquation_eqCopy {r : ℕ} (o i : Fin r) :
    ofEquation (StraightLineProgram.eqCopy o i) = eqCopy o.val i.val := by
  simp [ofEquation, StraightLineProgram.eqCopy, eqCopy]

@[simp] theorem ofEquation_eqScale {r : ℕ} (o : Fin r) (c : ℤ) (i : Fin r) :
    ofEquation (StraightLineProgram.eqScale o c i) =
      eqScale o.val (SignedCode.ofInt c) i.val := by
  simp [ofEquation, StraightLineProgram.eqScale, eqScale, SignedCode.neg_ofInt]

@[simp] theorem ofEquation_gPell (r : ℕ) :
    ofEquation (gPell r) = pell r := by
  have hthree : (3 : ℤ).toNat = 3 := by decide
  norm_num [ofEquation, gPell, pell, SignedCode.ofInt, SignedCode.one,
    SignedCode.zero, SignedCode.neg, vh, vk, hthree]

@[simp] theorem ofEquation_gSq (r : ℕ) :
    ofEquation (gSq r) = squares r := by
  have hx :
      (List.finRange r).map
          ((fun term : ℤ × Fin (r + 6) × Fin (r + 6) =>
              ((SignedCode.ofInt term.1, term.2.1.val), term.2.2.val)) ∘
            fun i => ((1 : ℤ), Fin.castAdd 6 i, Fin.castAdd 6 i)) =
        (List.range r).map fun i => ((SignedCode.one, i), i) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro i _
    rfl
  have hu :
      (List.finRange 4).map
          ((fun term : ℤ × Fin (r + 6) × Fin (r + 6) =>
              ((SignedCode.ofInt term.1, term.2.1.val), term.2.2.val)) ∘
            fun j => ((1 : ℤ), vu r j, vu r j)) =
        (List.range 4).map fun j => ((SignedCode.one, r + 2 + j), r + 2 + j) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro j _
    simp [vu, SignedCode.ofInt, SignedCode.one]
  simp only [ofEquation, gSq, squares, List.map_append, List.map_map]
  rw [hx, hu]
  norm_num [vh, SignedCode.ofInt, SignedCode.zero, SignedCode.one, SignedCode.neg]

theorem rename_identity (F : EquationCode) : rename id F = F := by
  rcases F with ⟨quad, lin, constant⟩
  simp [rename]

end EquationCode

namespace ProgramCode

@[simp] theorem ofProgram_const {n : ℕ} (a : ℤ) :
    ofProgram (StraightLineProgram.const (n := n) a) =
      const n (SignedCode.ofInt a) := by
  simp [ofProgram, StraightLineProgram.const, const]

@[simp] theorem ofProgram_var {n : ℕ} (i : Fin n) :
    ofProgram (StraightLineProgram.var i) = var n i.val := by
  simp [ofProgram, StraightLineProgram.var, var, Fin.last]

theorem shiftAux_incl₂ {n k₁ k₂ : ℕ} (i : Fin (n + k₂)) :
    EquationCode.shiftAux n k₁ i.val = (incl₂ n k₁ k₂ i).val := by
  by_cases h : i.val < n
  · simp [EquationCode.shiftAux, incl₂, h]
  · simp [EquationCode.shiftAux, incl₂, h]

@[simp] theorem ofEquation_rename_incl₁ {n k₁ k₂ : ℕ}
    (F : DegreeTwoEquation (n + k₁)) :
    EquationCode.ofEquation (F.rename (incl₁ n k₁ k₂)) =
      EquationCode.ofEquation F := by
  rcases F with ⟨quad, lin, constant⟩
  simp only [DegreeTwoEquation.rename, EquationCode.ofEquation, List.map_map]
  apply Prod.ext
  · apply List.map_congr_left
    rintro ⟨coefficient, i, j⟩ _
    rfl
  · apply Prod.ext
    · apply List.map_congr_left
      rintro ⟨coefficient, i⟩ _
      rfl
    · rfl

@[simp] theorem ofEquation_rename_incl₂ {n k₁ k₂ : ℕ}
    (F : DegreeTwoEquation (n + k₂)) :
    EquationCode.ofEquation (F.rename (incl₂ n k₁ k₂)) =
      EquationCode.rename (EquationCode.shiftAux n k₁) (EquationCode.ofEquation F) := by
  rcases F with ⟨quad, lin, constant⟩
  simp only [DegreeTwoEquation.rename, EquationCode.ofEquation, EquationCode.rename,
    List.map_map]
  apply Prod.ext
  · apply List.map_congr_left
    rintro ⟨coefficient, i, j⟩ _
    simp only [Function.comp_apply]
    rw [shiftAux_incl₂ i, shiftAux_incl₂ j]
  · apply Prod.ext
    · apply List.map_congr_left
      rintro ⟨coefficient, i⟩ _
      simp only [Function.comp_apply]
      rw [shiftAux_incl₂ i]
    · rfl

@[simp] theorem ofEquation_rename_castAdd {r extra : ℕ}
    (F : DegreeTwoEquation r) :
    EquationCode.ofEquation (F.rename (Fin.castAdd extra)) =
      EquationCode.ofEquation F := by
  rcases F with ⟨quad, lin, constant⟩
  simp only [DegreeTwoEquation.rename, EquationCode.ofEquation, List.map_map]
  apply Prod.ext
  · apply List.map_congr_left
    rintro ⟨coefficient, i, j⟩ _
    rfl
  · apply Prod.ext
    · apply List.map_congr_left
      rintro ⟨coefficient, i⟩ _
      rfl
    · rfl

@[simp] theorem map_ofEquation_rename_incl₁ {n k₁ k₂ : ℕ}
    (gates : List (DegreeTwoEquation (n + k₁))) :
    gates.map (EquationCode.ofEquation ∘ DegreeTwoEquation.rename (incl₁ n k₁ k₂)) =
      gates.map EquationCode.ofEquation := by
  exact List.map_congr_left fun F _ => ofEquation_rename_incl₁ F

@[simp] theorem map_ofEquation_rename_incl₂ {n k₁ k₂ : ℕ}
    (gates : List (DegreeTwoEquation (n + k₂))) :
    gates.map (EquationCode.ofEquation ∘ DegreeTwoEquation.rename (incl₂ n k₁ k₂)) =
      gates.map
        (EquationCode.rename (EquationCode.shiftAux n k₁) ∘ EquationCode.ofEquation) := by
  exact List.map_congr_left fun F _ => ofEquation_rename_incl₂ F

@[simp] theorem ofProgram_add {n : ℕ} (left right : StraightLineProgram n) :
  ofProgram (StraightLineProgram.add left right) =
      add n (ofProgram left) (ofProgram right) := by
  simp [StraightLineProgram.add, StraightLineProgram.binary, ofProgram, add, binary,
    shiftAux_incl₂, outPos, incl₁]

@[simp] theorem ofProgram_mul {n : ℕ} (left right : StraightLineProgram n) :
  ofProgram (StraightLineProgram.mul left right) =
      mul n (ofProgram left) (ofProgram right) := by
  simp [StraightLineProgram.mul, StraightLineProgram.binary, ofProgram, mul, binary,
    shiftAux_incl₂, outPos, incl₁]

@[simp] theorem ofProgram_scale {n : ℕ} (c : ℤ) (program : StraightLineProgram n) :
    ofProgram (StraightLineProgram.scale c program) =
      scale n (SignedCode.ofInt c) (ofProgram program) := by
  simp [StraightLineProgram.scale, StraightLineProgram.unary, ofProgram, scale,
    outPos, incl₁]

@[simp] theorem ofProgram_mulVar {n : ℕ} (program : StraightLineProgram n) (i : Fin n) :
    ofProgram (StraightLineProgram.mulVar program i) =
      mulVar n (ofProgram program) i.val := by
  simp [StraightLineProgram.mulVar, StraightLineProgram.unaryInput, ofProgram, mulVar,
    outPos, incl₁]

theorem iterateMulVar_ofProgram {n : ℕ} (i : Fin n) (steps : ℕ)
    (program : StraightLineProgram n) :
    iterateMulVar n i.val steps (ofProgram program) =
      ofProgram ((fun next => StraightLineProgram.mulVar next i)^[steps] program) := by
  induction steps generalizing program with
  | zero => rfl
  | succ steps ih =>
      rw [iterateMulVar, Function.iterate_succ_apply', ih, iterateMulVarStep,
        ← ofProgram_mulVar]

@[simp] theorem pow_ofProgram {n : ℕ} (i : Fin n) (power : ℕ) :
    pow n i.val power = ofProgram (StraightLineProgram.pow i power) := by
  induction power using Nat.twoStepInduction with
  | zero => simp [pow, StraightLineProgram.pow]
  | one => simp [pow, StraightLineProgram.pow]
  | more power _ ih =>
      rw [pow, if_neg (Nat.succ_ne_zero power), StraightLineProgram.pow,
        ofProgram_mulVar, ih]

theorem exponentList_getD {n : ℕ} (e : Fin n → ℕ) (i : Fin n) :
    (exponentList e).getD i.val 0 = e i := by
  rw [List.getD_eq_getElem _ _ (by rw [exponentList_length]; exact i.isLt)]
  simp [exponentList]

theorem monomialAux_ofProgram {n : ℕ} (e : Fin n → ℕ)
    (indices : List (Fin n)) :
    monomialAux n (exponentList e) (indices.map Fin.val) =
      (StraightLineProgram.monomialAux e indices).map ofProgram := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.map_cons, monomialAux_cons,
        StraightLineProgram.monomialAux, ih]
      cases htail : StraightLineProgram.monomialAux e indices with
      | none =>
          simp only [Option.map_none]
          rw [exponentList_getD]
          split_ifs with h
          · rfl
          · simp [pow_ofProgram]
      | some program =>
          simp only [Option.map_some]
          rw [exponentList_getD, iterateMulVar_ofProgram]

@[simp] theorem monomial_ofProgram {n : ℕ} (e : Fin n → ℕ) :
    monomial n (exponentList e) = ofProgram (StraightLineProgram.monomial e) := by
  rw [monomial, StraightLineProgram.monomial]
  rw [← List.map_coe_finRange_eq_range]
  rw [monomialAux_ofProgram]
  cases StraightLineProgram.monomialAux e (List.finRange n) <;> simp

theorem ofPolynomial_ofProgram {n : ℕ} (polynomial : IntPolynomialCode n) :
    ofPolynomial n
        (polynomial.map fun term => (exponentList term.1, term.2)) =
      ofProgram (StraightLineProgram.ofCode polynomial) := by
  induction polynomial with
  | nil => simp [ofPolynomial, StraightLineProgram.ofCode]
  | cons term tail ih =>
      rcases term with ⟨exponents, coefficient⟩
      cases tail with
      | nil =>
          simp [ofPolynomial, termProgram, StraightLineProgram.ofCode]
      | cons next rest =>
          simp only [List.map_cons] at ih ⊢
          have htail :
              ofPolynomial n
                  ((exponentList next.1, next.2) ::
                    rest.map fun term => (exponentList term.1, term.2)) =
                ofProgram (StraightLineProgram.ofCode (next :: rest)) := by
            simpa only [List.map_cons] using ih
          rw [ofPolynomial, ofPolynomialAux_cons,
            ofPolynomialAux_eq_some_ofPolynomial, Option.getD_some, termProgram,
            monomial_ofProgram, htail, ← ofProgram_scale]
          simp only
          rw [← ofProgram_add]
          rfl

theorem degreeTwoSystem_ofProgram {n : ℕ} (polynomial : IntPolynomialCode n) :
    degreeTwoSystem n (polynomial.map fun term => (exponentList term.1, term.2)) =
      (n + (StraightLineProgram.ofCode polynomial).k,
        (Trinomial.degreeTwoSystem polynomial).map EquationCode.ofEquation) := by
  rw [degreeTwoSystem, ofPolynomial_ofProgram]
  simp [ProgramCode.ofProgram, Trinomial.degreeTwoSystem]

theorem guardedSystem_ofProgram {n : ℕ} (polynomial : IntPolynomialCode n) :
    guardedSystem n (polynomial.map fun term => (exponentList term.1, term.2)) =
      (numVars polynomial,
        (guarded (Trinomial.degreeTwoSystem polynomial)).map EquationCode.ofEquation) := by
  rw [guardedSystem, degreeTwoSystem_ofProgram]
  simp [guarded, numVars]

end ProgramCode

/-! ### First-order vectors and homogenized matrices -/

namespace RationalCode

/-- Regard a signed integer code as a rational code with denominator one. -/
def ofSigned (a : SignedCode) : RationalCode := (a, 0)

/-- Subtraction of rational codes. -/
def sub (a b : RationalCode) : RationalCode := add a (neg b)

/-- A finite sum of rational codes. -/
def sum (l : List RationalCode) : RationalCode := l.foldr add zero

/-- A natural-number power of a rational code. -/
def pow (a : RationalCode) : ℕ → RationalCode
  | 0 => one
  | n + 1 => mul (pow a n) a

@[simp] theorem value_ofSigned (a : SignedCode) : (ofSigned a).value = a.value := by
  rw [ofSigned, value]
  change mkRat a.value 1 = (a.value : ℚ)
  rw [Rat.mkRat_eq_divInt]
  norm_num [Rat.divInt_one]

@[simp] theorem value_sub (a b : RationalCode) : (sub a b).value = a.value - b.value := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_sum (l : List RationalCode) : (sum l).value = (l.map value).sum := by
  induction l with
  | nil => simp [sum]
  | cons a l ih =>
      change (add a (sum l)).value = a.value + (l.map value).sum
      simp [ih]

@[simp] theorem value_pow (a : RationalCode) (n : ℕ) : (pow a n).value = a.value ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

end RationalCode

/-- A first-order vector over the coded rationals. -/
abbrev RationalVectorCode := List RationalCode

namespace RationalVectorCode

/-- The zero vector of a specified length. -/
def zero (n : ℕ) : RationalVectorCode := (List.range n).map fun _ => RationalCode.zero

/-- Tabulate the first `n` values of a function. -/
def tabulate (n : ℕ) (f : ℕ → RationalCode) : RationalVectorCode :=
  (List.range n).map f

/-- Coordinatewise addition in a specified ambient dimension. -/
def add (n : ℕ) (x y : RationalVectorCode) : RationalVectorCode :=
  tabulate n fun i => RationalCode.add (x.getD i RationalCode.zero)
    (y.getD i RationalCode.zero)

/-- Coordinatewise subtraction in a specified ambient dimension. -/
def sub (n : ℕ) (x y : RationalVectorCode) : RationalVectorCode :=
  tabulate n fun i => RationalCode.sub (x.getD i RationalCode.zero)
    (y.getD i RationalCode.zero)

/-- Scalar multiplication in a specified ambient dimension. -/
def scale (n : ℕ) (a : RationalCode) (x : RationalVectorCode) : RationalVectorCode :=
  tabulate n fun i => RationalCode.mul a (x.getD i RationalCode.zero)

/-- The dot product in a specified ambient dimension. -/
def dot (n : ℕ) (x y : RationalVectorCode) : RationalCode :=
  RationalCode.sum ((List.range n).map fun i =>
    RationalCode.mul (x.getD i RationalCode.zero) (y.getD i RationalCode.zero))

@[simp] theorem getD_tabulate {n i : ℕ} (f : ℕ → RationalCode) (hi : i < n) :
    (tabulate n f).getD i RationalCode.zero = f i := by
  rw [tabulate, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

@[simp] theorem length_tabulate (n : ℕ) (f : ℕ → RationalCode) :
    (tabulate n f).length = n := by
  simp [tabulate]

@[simp] theorem length_zero (n : ℕ) : (zero n).length = n := by
  simp [zero]

@[simp] theorem value_getD_tabulate {n i : ℕ} (f : ℕ → RationalCode) (hi : i < n) :
    ((tabulate n f).getD i RationalCode.zero).value = (f i).value := by
  rw [getD_tabulate f hi]

end RationalVectorCode

namespace HomogenizedCode

/-- The natural-number index of a homogenized coordinate: `none` has index zero and
`some i` has index `i + 1`. -/
def optionIndex {r : ℕ} : Option (Fin r) → ℕ
  | none => 0
  | some i => i.val + 1

theorem optionIndex_lt {r : ℕ} (o : Option (Fin r)) : optionIndex o < r + 1 := by
  cases o with
  | none => simp [optionIndex]
  | some i => simp only [optionIndex]; omega

theorem optionIndex_injective {r : ℕ} :
    Function.Injective (@optionIndex r) := by
  intro o o' h
  cases o with
  | none => cases o' <;> simp [optionIndex] at h ⊢
  | some i =>
      cases o' with
      | none => simp [optionIndex] at h
      | some j =>
          exact congrArg some (Fin.ext (by simpa [optionIndex] using h))

/-- One elementary symmetric-matrix contribution. -/
def symEntry (a : RationalCode) (o₁ o₂ i j : ℕ) : RationalCode :=
  RationalCode.add
    (if i = o₁ ∧ j = o₂ then RationalCode.div a RationalCode.two
      else RationalCode.zero)
    (if i = o₂ ∧ j = o₁ then RationalCode.div a RationalCode.two
      else RationalCode.zero)

/-- One entry of the symmetric matrix obtained by homogenizing an equation code. -/
def matrixEntry (F : EquationCode) (i j : ℕ) : RationalCode :=
  RationalCode.add
    (RationalCode.add
      (RationalCode.sum (F.1.map fun term =>
        symEntry (RationalCode.ofSigned term.1.1) (term.1.2 + 1) (term.2 + 1) i j))
      (RationalCode.sum (F.2.1.map fun term =>
        symEntry (RationalCode.ofSigned term.1) (term.2 + 1) 0 i j)))
    (symEntry (RationalCode.ofSigned F.2.2) 0 0 i j)

theorem symEntry_value {r : ℕ} (a : SignedCode) (o₁ o₂ o o' : Option (Fin r)) :
    (symEntry (RationalCode.ofSigned a) (optionIndex o₁) (optionIndex o₂)
      (optionIndex o) (optionIndex o')).value = symG a.value o₁ o₂ o o' := by
  simp only [symEntry, RationalCode.value_add, RationalCode.value_div,
    RationalCode.value_ofSigned, RationalCode.value_two, apply_ite, RationalCode.value_zero,
    symG]
  simp only [optionIndex_injective.eq_iff]
  split_ifs <;> rfl

theorem matrixEntry_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (o o' : Option (Fin r)) :
    (matrixEntry (EquationCode.ofEquation F) (optionIndex o) (optionIndex o')).value =
      F.homogenize.b o o' := by
  rcases F with ⟨quad, lin, constant⟩
  have hquad :
      (RationalCode.sum (quad.map fun term =>
        symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
          (term.2.1.val + 1) (term.2.2.val + 1) (optionIndex o) (optionIndex o'))).value =
        ((quad.map fun term =>
          symG (term.1 : ℚ) (some term.2.1) (some term.2.2)).sum) o o' := by
    induction quad with
    | nil => simp
    | cons term quad ih =>
        rcases term with ⟨a, i, j⟩
        simp only [List.map_cons, List.sum_cons, Pi.add_apply]
        change
          (RationalCode.add
            (symEntry (RationalCode.ofSigned (SignedCode.ofInt a))
              (optionIndex (some i)) (optionIndex (some j)) (optionIndex o) (optionIndex o'))
            (RationalCode.sum (quad.map fun term =>
              symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
                (term.2.1.val + 1) (term.2.2.val + 1)
                (optionIndex o) (optionIndex o')))).value = _
        rw [RationalCode.value_add, ih,
          symEntry_value (SignedCode.ofInt a) (some i) (some j) o o',
          SignedCode.value_ofInt]
  have hlin :
      (RationalCode.sum (lin.map fun term =>
        symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
          (term.2.val + 1) 0 (optionIndex o) (optionIndex o'))).value =
        ((lin.map fun term => symG (term.1 : ℚ) (some term.2) none).sum) o o' := by
    induction lin with
    | nil => simp
    | cons term lin ih =>
        rcases term with ⟨a, i⟩
        simp only [List.map_cons, List.sum_cons, Pi.add_apply]
        change
          (RationalCode.add
            (symEntry (RationalCode.ofSigned (SignedCode.ofInt a))
              (optionIndex (some i)) (optionIndex (none : Option (Fin r)))
              (optionIndex o) (optionIndex o'))
            (RationalCode.sum (lin.map fun term =>
              symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
                (term.2.val + 1) 0 (optionIndex o) (optionIndex o')))).value = _
        rw [RationalCode.value_add, ih,
          symEntry_value (SignedCode.ofInt a) (some i) none o o',
          SignedCode.value_ofInt]
  have hquadMap :
      ((quad.map fun term =>
          ((SignedCode.ofInt term.1, term.2.1.val), term.2.2.val)).map fun term =>
        symEntry (RationalCode.ofSigned term.1.1) (term.1.2 + 1) (term.2 + 1)
          (optionIndex o) (optionIndex o')) =
        quad.map fun term =>
          symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
            (term.2.1.val + 1) (term.2.2.val + 1) (optionIndex o) (optionIndex o') := by
    rw [List.map_map]
    rfl
  have hlinMap :
      ((lin.map fun term => (SignedCode.ofInt term.1, term.2.val)).map fun term =>
        symEntry (RationalCode.ofSigned term.1) (term.2 + 1) 0
          (optionIndex o) (optionIndex o')) =
        lin.map fun term =>
          symEntry (RationalCode.ofSigned (SignedCode.ofInt term.1))
            (term.2.val + 1) 0 (optionIndex o) (optionIndex o') := by
    rw [List.map_map]
    rfl
  simp only [matrixEntry, EquationCode.ofEquation, RationalCode.value_add]
  rw [hquadMap, hlinMap]
  rw [hquad, hlin]
  simp only [DegreeTwoEquation.homogenize, DegreeTwoEquation.homogenizeFun, Pi.add_apply]
  have hconstant :
      (symEntry (RationalCode.ofSigned (SignedCode.ofInt constant)) 0 0
        (optionIndex o) (optionIndex o')).value = symG (constant : ℚ) none none o o' := by
    simpa only [optionIndex, SignedCode.value_ofInt] using
      symEntry_value (SignedCode.ofInt constant) (none : Option (Fin r)) none o o'
  rw [hconstant]

end HomogenizedCode

/-! ### The base-algebra computation on codes -/

namespace BaseAlgebraCode

/-- A coordinate vector for `A₀`, ordered as `1, B, B², B³, B⁴, C₁, …, C_N`. -/
abbrev Code := RationalVectorCode

/-- The multiplicative identity of the coded base algebra. -/
def one (N : ℕ) : Code :=
  RationalVectorCode.tabulate (5 + N) fun i =>
    if i = 0 then RationalCode.one else RationalCode.zero

/-- The coded image of the point-coordinate variable at position `i`. -/
def gen (N i : ℕ) : Code :=
  RationalVectorCode.tabulate (5 + N) fun j =>
    if i = 0 ∧ j = 1 then RationalCode.one
    else if i = 1 ∧ j = 1 then RationalCode.neg RationalCode.one
    else if 2 ≤ i ∧ j = i + 3 then RationalCode.one
    else RationalCode.zero

/-- Multiplication in the coded base algebra. -/
def mul (N : ℕ) (x y : Code) : Code :=
  RationalVectorCode.tabulate (5 + N) fun j =>
    if j < 5 then
      RationalCode.sum ((List.range (j + 1)).map fun i =>
        RationalCode.mul (x.getD i RationalCode.zero)
          (y.getD (j - i) RationalCode.zero))
    else
      RationalCode.add
        (RationalCode.mul (x.getD 0 RationalCode.zero)
          (y.getD j RationalCode.zero))
        (RationalCode.mul (y.getD 0 RationalCode.zero)
          (x.getD j RationalCode.zero))

/-- Powers in the coded base algebra. -/
def powStep (input : ℕ × (Code × Code)) : Code :=
  mul input.1 input.2.1 input.2.2

/-- Powers in the coded base algebra. -/
def pow (N : ℕ) (x : Code) : ℕ → Code
  | 0 => one N
  | k + 1 => powStep (N, pow N x k, x)

/-- One multiplication step while evaluating a point-coordinate monomial. -/
def imageStep (input : (ℕ × List ℕ) × (Code × ℕ)) : Code :=
  mul input.1.1 input.2.1
    (pow input.1.1 (gen input.1.1 input.2.2)
      (input.1.2.getD input.2.2 0))

/-- The coded image of a dense point-coordinate monomial. -/
def image (N : ℕ) (e : List ℕ) : Code :=
  (List.range (2 + N)).foldl
    (fun acc i => imageStep ((N, e), (acc, i))) (one N)

/-- Decode a base-algebra coordinate vector. -/
noncomputable def value (N : ℕ) (x : Code) : BaseAlgebra N :=
  ⟨(x.getD 0 RationalCode.zero).value,
    (x.getD 1 RationalCode.zero).value,
    (x.getD 2 RationalCode.zero).value,
    (x.getD 3 RationalCode.zero).value,
    (x.getD 4 RationalCode.zero).value,
    fun i => (x.getD (5 + i.val) RationalCode.zero).value⟩

theorem one_getD {N i : ℕ} (hi : i < 5 + N) :
    (one N).getD i RationalCode.zero =
      if i = 0 then RationalCode.one else RationalCode.zero := by
  exact RationalVectorCode.getD_tabulate _ hi

theorem gen_getD {N i j : ℕ} (hj : j < 5 + N) :
    (gen N i).getD j RationalCode.zero =
      if i = 0 ∧ j = 1 then RationalCode.one
      else if i = 1 ∧ j = 1 then RationalCode.neg RationalCode.one
      else if 2 ≤ i ∧ j = i + 3 then RationalCode.one
      else RationalCode.zero := by
  exact RationalVectorCode.getD_tabulate _ hj

theorem mul_getD {N j : ℕ} (x y : Code) (hj : j < 5 + N) :
    (mul N x y).getD j RationalCode.zero =
      if j < 5 then
        RationalCode.sum ((List.range (j + 1)).map fun i =>
          RationalCode.mul (x.getD i RationalCode.zero)
            (y.getD (j - i) RationalCode.zero))
      else
        RationalCode.add
          (RationalCode.mul (x.getD 0 RationalCode.zero)
            (y.getD j RationalCode.zero))
          (RationalCode.mul (y.getD 0 RationalCode.zero)
            (x.getD j RationalCode.zero)) := by
  exact RationalVectorCode.getD_tabulate _ hj

@[simp] theorem value_one (N : ℕ) : value N (one N) = 1 := by
  apply BaseAlgebra.ext
  · change ((one N).getD 0 RationalCode.zero).value = 1
    rw [one_getD (by omega)]; simp
  · change ((one N).getD 1 RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp
  · change ((one N).getD 2 RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp
  · change ((one N).getD 3 RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp
  · change ((one N).getD 4 RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp
  · funext i
    change ((one N).getD (5 + i.val) RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp

@[simp] theorem value_mul (N : ℕ) (x y : Code) :
    value N (mul N x y) = value N x * value N y := by
  apply BaseAlgebra.ext
  · change ((mul N x y).getD 0 RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    norm_num [value, Function.comp_def, List.range_succ]
  · change ((mul N x y).getD 1 RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    norm_num [value, Function.comp_def, List.range_succ]
  · change ((mul N x y).getD 2 RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    norm_num [value, Function.comp_def, List.range_succ]
    ring
  · change ((mul N x y).getD 3 RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    norm_num [value, Function.comp_def, List.range_succ]
    ring
  · change ((mul N x y).getD 4 RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    norm_num [value, Function.comp_def, List.range_succ]
    ring
  · funext i
    change ((mul N x y).getD (5 + i.val) RationalCode.zero).value = _
    rw [mul_getD x y (by omega)]
    simp only [show ¬5 + i.val < 5 by omega, if_false, RationalCode.value_add,
      RationalCode.value_mul]
    rfl

@[simp] theorem value_pow (N : ℕ) (x : Code) (k : ℕ) :
    value N (pow N x k) = value N x ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, powStep, ih, pow_succ]

@[simp] theorem value_gen (N : ℕ) (i : Fin (2 + N)) :
    value N (gen N i.val) = baseGen N i := by
  induction i using Fin.addCases with
  | left i =>
      fin_cases i
      · change value N (gen N 0) = baseGen N (Fin.castAdd N 0)
        rw [baseGen_zero]
        apply BaseAlgebra.ext
        · change ((gen N 0).getD 0 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 0).getD 1 RationalCode.zero).value = 1
          rw [gen_getD (by omega)]; simp
        · change ((gen N 0).getD 2 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 0).getD 3 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 0).getD 4 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · funext j
          change ((gen N 0).getD (5 + j.val) RationalCode.zero).value = 0
          rw [gen_getD (by omega)]
          simp only [show ¬5 + j.val = 1 by omega, and_false, if_false,
            show ¬0 = 1 by omega, false_and, show ¬2 ≤ 0 by omega,
            RationalCode.value_zero]
      · change value N (gen N 1) = baseGen N (Fin.castAdd N 1)
        rw [baseGen_one]
        apply BaseAlgebra.ext
        · change ((gen N 1).getD 0 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 1).getD 1 RationalCode.zero).value = -1
          rw [gen_getD (by omega)]; simp
        · change ((gen N 1).getD 2 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 1).getD 3 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · change ((gen N 1).getD 4 RationalCode.zero).value = 0
          rw [gen_getD (by omega)]; simp
        · funext j
          change ((gen N 1).getD (5 + j.val) RationalCode.zero).value = 0
          rw [gen_getD (by omega)]
          simp only [show ¬1 = 0 by omega, false_and, if_false,
            show ¬5 + j.val = 1 by omega, and_false, show ¬2 ≤ 1 by omega,
            RationalCode.value_zero]
  | right i =>
      change value N (gen N (2 + i.val)) = baseGen N (Fin.natAdd 2 i)
      rw [baseGen_natAdd]
      apply BaseAlgebra.ext
      · change ((gen N (2 + i.val)).getD 0 RationalCode.zero).value = 0
        rw [gen_getD (by omega)]; simp
      · change ((gen N (2 + i.val)).getD 1 RationalCode.zero).value = 0
        rw [gen_getD (by omega)]
        simp only [show ¬2 + i.val = 0 by omega, false_and, if_false,
          show ¬2 + i.val = 1 by omega, show 2 ≤ 2 + i.val by omega, true_and,
          show ¬1 = 2 + i.val + 3 by omega, RationalCode.value_zero]
      · change ((gen N (2 + i.val)).getD 2 RationalCode.zero).value = 0
        rw [gen_getD (by omega)]; simp
      · change ((gen N (2 + i.val)).getD 3 RationalCode.zero).value = 0
        rw [gen_getD (by omega)]; simp
      · change ((gen N (2 + i.val)).getD 4 RationalCode.zero).value = 0
        rw [gen_getD (by omega)]
        simp only [show ¬2 + i.val = 0 by omega, false_and, if_false,
          show ¬2 + i.val = 1 by omega, show 2 ≤ 2 + i.val by omega, true_and,
          show ¬4 = 2 + i.val + 3 by omega, RationalCode.value_zero]
      · funext j
        change ((gen N (2 + i.val)).getD (5 + j.val) RationalCode.zero).value =
          (Pi.single i (1 : ℚ) : Fin N → ℚ) j
        rw [gen_getD (by omega)]
        by_cases h : j = i
        · subst j
          simp only [show ¬2 + i.val = 0 by omega, false_and, if_false,
            show ¬2 + i.val = 1 by omega, show 2 ≤ 2 + i.val by omega, true_and,
            show 5 + i.val = 2 + i.val + 3 by omega, if_pos, RationalCode.value_one,
            Pi.single_eq_same]
        · have hnat : 5 + j.val ≠ 2 + i.val + 3 := by
            intro heq
            apply h
            apply Fin.ext
            omega
          simp only [show ¬2 + i.val = 0 by omega, false_and, if_false,
            show ¬2 + i.val = 1 by omega, show 2 ≤ 2 + i.val by omega, true_and,
            hnat, RationalCode.value_zero, Pi.single_eq_of_ne h]

@[simp] theorem value_image (N : ℕ) (e : Fin (2 + N) → ℕ) :
    value N (image N (exponentList e)) = baseImage N e := by
  rw [image, baseImage, Fin.prod_univ_def]
  rw [← List.map_coe_finRange_eq_range]
  have h : ∀ (l : List (Fin (2 + N))) (acc : Code),
      value N
          ((l.map Fin.val).foldl
            (fun a i => mul N a (pow N (gen N i) ((exponentList e).getD i 0))) acc) =
        value N acc *
          (l.map fun i => baseGen N i ^ e i).prod := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons i l ih =>
        simp only [List.map_cons, List.foldl_cons, ih, value_mul, value_pow,
          List.prod_cons, mul_assoc]
        rw [ProgramCode.exponentList_getD]
        rw [value_gen]
  simp only [imageStep]
  rw [h, value_one, one_mul]

end BaseAlgebraCode

/-! ### The cube-algebra computation on codes -/

namespace MatrixVectorCode

/-- Decode a vector indexed by `none, some 0, …, some (r-1)`. -/
noncomputable def value (r : ℕ) (x : RationalVectorCode) : Option (Fin r) → ℚ :=
  fun o => (x.getD (HomogenizedCode.optionIndex o) RationalCode.zero).value

/-- The homogenized symmetric matrix as a list of coded rows. -/
def matrix (r : ℕ) (F : EquationCode) : List RationalVectorCode :=
  (List.range (r + 1)).map fun i =>
    RationalVectorCode.tabulate (r + 1) fun j => HomogenizedCode.matrixEntry F i j

theorem matrix_getD {r i j : ℕ} (F : EquationCode) (hi : i < r + 1)
    (hj : j < r + 1) :
    ((matrix r F).getD i []).getD j RationalCode.zero =
      HomogenizedCode.matrixEntry F i j := by
  have hrow : (matrix r F).getD i [] =
      RationalVectorCode.tabulate (r + 1) fun j =>
        HomogenizedCode.matrixEntry F i j := by
    rw [matrix, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getElem_range]
  rw [hrow, RationalVectorCode.getD_tabulate _ hj]

/-- Matrix multiplication when the coded matrix rows have already been computed. -/
def polarWithMatrix (r : ℕ) (entries : List RationalVectorCode)
    (x y : RationalVectorCode) : RationalCode :=
  RationalCode.sum ((List.range (r + 1)).map fun i =>
    RationalCode.sum ((List.range (r + 1)).map fun j =>
      RationalCode.mul
        (RationalCode.mul (x.getD i RationalCode.zero)
          ((entries.getD i []).getD j RationalCode.zero))
        (y.getD j RationalCode.zero)))

/-- Matrix multiplication on first-order codes. -/
def polar (r : ℕ) (F : EquationCode) (x y : RationalVectorCode) : RationalCode :=
  polarWithMatrix r (matrix r F) x y

theorem optionIndex_optOf {r : ℕ} (i : Fin (r + 1)) :
    HomogenizedCode.optionIndex (optOf i) = i.val := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem value_polar_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (x y : RationalVectorCode) :
    (polar r (EquationCode.ofEquation F) x y).value =
      F.homogenize.polar (value r x) (value r y) := by
  classical
  simp only [polar, polarWithMatrix,
    RationalCode.value_sum, List.map_map, Function.comp_def,
    RationalCode.value_mul]
  rw [F.homogenize.polar_eq_toBilin', Matrix.toBilin'_apply]
  change _ = ∑ o, ∑ o', value r x o * F.homogenize.b o o' * value r y o'
  rw [← sum_optOf (fun o => ∑ o', value r x o * F.homogenize.b o o' * value r y o')]
  rw [listSum_map_range_eq_finSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_optOf (fun o' =>
    value r x (optOf i) * F.homogenize.b (optOf i) o' * value r y o')]
  rw [listSum_map_range_eq_finSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrix_getD _ i.isLt j.isLt, ← optionIndex_optOf i, ← optionIndex_optOf j,
    HomogenizedCode.matrixEntry_ofEquation]
  rfl

end MatrixVectorCode

namespace CubeAlgebraCode

/-- A coordinate vector for `A_Q`, ordered as `1, v₀, v₁, …, v_N, ζ`. -/
abbrev Code := RationalVectorCode

/-- The multiplicative identity of a coded cube algebra. -/
def one (r : ℕ) : Code :=
  RationalVectorCode.tabulate (r + 3) fun i =>
    if i = 0 then RationalCode.one else RationalCode.zero

/-- Extract the vector coordinates from a coded cube-algebra element. -/
def vectorPart (r : ℕ) (x : Code) : RationalVectorCode :=
  RationalVectorCode.tabulate (r + 1) fun i => x.getD (i + 1) RationalCode.zero

/-- Multiplication in the coded cube algebra attached to an equation code. -/
def mul (r : ℕ) (F : EquationCode) (x y : Code) : Code :=
  RationalVectorCode.tabulate (r + 3) fun j =>
    if j = 0 then
      RationalCode.mul (x.getD 0 RationalCode.zero) (y.getD 0 RationalCode.zero)
    else if j < r + 2 then
      RationalCode.add
        (RationalCode.mul (x.getD 0 RationalCode.zero)
          (y.getD j RationalCode.zero))
        (RationalCode.mul (y.getD 0 RationalCode.zero)
          (x.getD j RationalCode.zero))
    else
      RationalCode.add
        (RationalCode.add
          (RationalCode.mul (x.getD 0 RationalCode.zero)
            (y.getD (r + 2) RationalCode.zero))
          (RationalCode.mul (y.getD 0 RationalCode.zero)
            (x.getD (r + 2) RationalCode.zero)))
        (MatrixVectorCode.polar r F (vectorPart r x) (vectorPart r y))

/-- Powers in a coded cube algebra. -/
def pow (r : ℕ) (F : EquationCode) (x : Code) : ℕ → Code
  | 0 => one r
  | k + 1 => mul r F (pow r F x k) x

/-- The vector in the exponential defining the image of point-coordinate variable `i`. -/
def generatorVector (r i : ℕ) : RationalVectorCode :=
  RationalVectorCode.tabulate (r + 1) fun j =>
    if i = 0 ∧ j = 0 then RationalCode.one
    else if i = 1 ∧ j = 0 then RationalCode.neg RationalCode.one
    else if 2 ≤ i ∧ j + 1 = i then RationalCode.one
    else RationalCode.zero

/-- The coded element `Exp(v) - 1` for a coded vector `v`. -/
def expMinusOne (r : ℕ) (F : EquationCode) (v : RationalVectorCode) : Code :=
  RationalVectorCode.tabulate (r + 3) fun j =>
    if j = 0 then RationalCode.zero
    else if j < r + 2 then v.getD (j - 1) RationalCode.zero
    else RationalCode.div (MatrixVectorCode.polar r F v v) RationalCode.two

/-- The coded image of point-coordinate variable `i`. -/
def gen (r : ℕ) (F : EquationCode) (i : ℕ) : Code :=
  expMinusOne r F (generatorVector r i)

/-- The coded image of a dense point-coordinate monomial. -/
def image (r : ℕ) (F : EquationCode) (e : List ℕ) : Code :=
  (List.range (2 + r)).foldl
    (fun acc i => mul r F acc (pow r F (gen r F i) (e.getD i 0))) (one r)

/-- Decode a cube-algebra coordinate vector. -/
noncomputable def value {r : ℕ} (G : BilinearFormMatrix (Option (Fin r)))
    (x : Code) : CubeAlgebra G :=
  ⟨(x.getD 0 RationalCode.zero).value,
    fun o => (x.getD (HomogenizedCode.optionIndex o + 1) RationalCode.zero).value,
    (x.getD (r + 2) RationalCode.zero).value⟩

theorem one_getD {r i : ℕ} (hi : i < r + 3) :
    (one r).getD i RationalCode.zero =
      if i = 0 then RationalCode.one else RationalCode.zero := by
  exact RationalVectorCode.getD_tabulate _ hi

theorem vectorPart_getD {r i : ℕ} (x : Code) (hi : i < r + 1) :
    (vectorPart r x).getD i RationalCode.zero = x.getD (i + 1) RationalCode.zero := by
  exact RationalVectorCode.getD_tabulate _ hi

theorem mul_getD {r j : ℕ} (F : EquationCode) (x y : Code) (hj : j < r + 3) :
    (mul r F x y).getD j RationalCode.zero =
      if j = 0 then
        RationalCode.mul (x.getD 0 RationalCode.zero) (y.getD 0 RationalCode.zero)
      else if j < r + 2 then
        RationalCode.add
          (RationalCode.mul (x.getD 0 RationalCode.zero)
            (y.getD j RationalCode.zero))
          (RationalCode.mul (y.getD 0 RationalCode.zero)
            (x.getD j RationalCode.zero))
      else
        RationalCode.add
          (RationalCode.add
            (RationalCode.mul (x.getD 0 RationalCode.zero)
              (y.getD (r + 2) RationalCode.zero))
            (RationalCode.mul (y.getD 0 RationalCode.zero)
              (x.getD (r + 2) RationalCode.zero)))
          (MatrixVectorCode.polar r F (vectorPart r x) (vectorPart r y)) := by
  exact RationalVectorCode.getD_tabulate _ hj

@[simp] theorem value_one {r : ℕ} (G : BilinearFormMatrix (Option (Fin r))) :
    value G (one r) = 1 := by
  apply CubeAlgebra.ext
  · change ((one r).getD 0 RationalCode.zero).value = 1
    rw [one_getD (by omega)]; simp
  · funext o
    change ((one r).getD (HomogenizedCode.optionIndex o + 1) RationalCode.zero).value = 0
    rw [one_getD (by have := HomogenizedCode.optionIndex_lt o; omega)]
    simp
  · change ((one r).getD (r + 2) RationalCode.zero).value = 0
    rw [one_getD (by omega)]; simp

theorem matrixVector_value_vectorPart {r : ℕ}
    (G : BilinearFormMatrix (Option (Fin r))) (x : Code) :
    MatrixVectorCode.value r (vectorPart r x) = (value G x).vector := by
  funext o
  rw [MatrixVectorCode.value, vectorPart_getD x (HomogenizedCode.optionIndex_lt o)]
  rfl

@[simp] theorem value_mul_ofEquation {r : ℕ} (F : DegreeTwoEquation r) (x y : Code) :
    value F.homogenize (mul r (EquationCode.ofEquation F) x y) =
      value F.homogenize x * value F.homogenize y := by
  apply CubeAlgebra.ext
  · change ((mul r (EquationCode.ofEquation F) x y).getD 0 RationalCode.zero).value = _
    rw [mul_getD _ _ _ (by omega)]
    simp [value]
  · funext o
    let j := HomogenizedCode.optionIndex o + 1
    have hj0 : j ≠ 0 := by simp [j]
    have hj : j < r + 2 := by
      have := HomogenizedCode.optionIndex_lt o
      omega
    change ((mul r (EquationCode.ofEquation F) x y).getD j RationalCode.zero).value = _
    rw [mul_getD _ _ _ (by omega)]
    simp only [hj0, if_false, hj, if_true, RationalCode.value_add,
      RationalCode.value_mul]
    rfl
  · change ((mul r (EquationCode.ofEquation F) x y).getD (r + 2)
      RationalCode.zero).value = _
    rw [mul_getD _ _ _ (by omega)]
    simp only [show r + 2 ≠ 0 by omega, if_false, show ¬ r + 2 < r + 2 by omega,
      RationalCode.value_add, RationalCode.value_mul]
    rw [MatrixVectorCode.value_polar_ofEquation,
      matrixVector_value_vectorPart F.homogenize,
      matrixVector_value_vectorPart F.homogenize]
    rfl

@[simp] theorem value_pow_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (x : Code) (k : ℕ) :
    value F.homogenize (pow r (EquationCode.ofEquation F) x k) =
      value F.homogenize x ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ]

theorem generatorVector_getD {r i j : ℕ} (hj : j < r + 1) :
    (generatorVector r i).getD j RationalCode.zero =
      if i = 0 ∧ j = 0 then RationalCode.one
      else if i = 1 ∧ j = 0 then RationalCode.neg RationalCode.one
      else if 2 ≤ i ∧ j + 1 = i then RationalCode.one
      else RationalCode.zero := by
  exact RationalVectorCode.getD_tabulate _ hj

theorem expMinusOne_getD {r j : ℕ} (F : EquationCode) (v : RationalVectorCode)
    (hj : j < r + 3) :
    (expMinusOne r F v).getD j RationalCode.zero =
      if j = 0 then RationalCode.zero
      else if j < r + 2 then v.getD (j - 1) RationalCode.zero
      else RationalCode.div (MatrixVectorCode.polar r F v v) RationalCode.two := by
  exact RationalVectorCode.getD_tabulate _ hj

@[simp] theorem value_expMinusOne_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (v : RationalVectorCode) :
    value F.homogenize (expMinusOne r (EquationCode.ofEquation F) v) =
      CubeAlgebra.exp F.homogenize (MatrixVectorCode.value r v) - 1 := by
  apply CubeAlgebra.ext
  · change ((expMinusOne r (EquationCode.ofEquation F) v).getD 0
      RationalCode.zero).value = _
    rw [expMinusOne_getD _ _ (by omega)]
    simp only [sub_eq_add_neg, CubeAlgebra.add_scalar, CubeAlgebra.exp_scalar,
      CubeAlgebra.neg_scalar, CubeAlgebra.one_scalar]
    norm_num
  · funext o
    let j := HomogenizedCode.optionIndex o + 1
    have hj0 : j ≠ 0 := by simp [j]
    have hj : j < r + 2 := by
      have := HomogenizedCode.optionIndex_lt o
      omega
    change ((expMinusOne r (EquationCode.ofEquation F) v).getD j
      RationalCode.zero).value = _
    rw [expMinusOne_getD _ _ (by omega)]
    simp only [hj0, if_false, hj, if_true]
    rw [show j - 1 = HomogenizedCode.optionIndex o by simp [j]]
    simp only [sub_eq_add_neg, CubeAlgebra.add_vector, CubeAlgebra.exp_vector,
      CubeAlgebra.neg_vector, CubeAlgebra.one_vector, Pi.add_apply,
      Pi.zero_apply, neg_zero, add_zero, MatrixVectorCode.value]
  · change ((expMinusOne r (EquationCode.ofEquation F) v).getD (r + 2)
      RationalCode.zero).value = _
    rw [expMinusOne_getD _ _ (by omega)]
    simp only [show r + 2 ≠ 0 by omega, if_false, show ¬r + 2 < r + 2 by omega,
      RationalCode.value_div, RationalCode.value_two]
    rw [MatrixVectorCode.value_polar_ofEquation]
    simp only [sub_eq_add_neg, CubeAlgebra.add_socle, CubeAlgebra.exp_socle,
      CubeAlgebra.neg_socle, CubeAlgebra.one_socle, neg_zero, add_zero,
      BilinearFormMatrix.quad, LinearMap.BilinMap.toQuadraticMap_apply]

theorem generatorVector_zero_value (r : ℕ) :
    MatrixVectorCode.value r (generatorVector r 0) = homVec 0 1 := by
  funext o
  rw [MatrixVectorCode.value]
  rw [generatorVector_getD (HomogenizedCode.optionIndex_lt o)]
  cases o with
  | none => simp [HomogenizedCode.optionIndex]
  | some i => simp [HomogenizedCode.optionIndex]

theorem generatorVector_one_value (r : ℕ) :
    MatrixVectorCode.value r (generatorVector r 1) = homVec 0 (-1) := by
  funext o
  rw [MatrixVectorCode.value]
  rw [generatorVector_getD (HomogenizedCode.optionIndex_lt o)]
  cases o with
  | none => simp [HomogenizedCode.optionIndex]
  | some i => simp [HomogenizedCode.optionIndex]

theorem generatorVector_natAdd_value {r : ℕ} (i : Fin r) :
    MatrixVectorCode.value r (generatorVector r (2 + i.val)) =
      homVec (Pi.single i 1) 0 := by
  funext o
  rw [MatrixVectorCode.value]
  rw [generatorVector_getD (HomogenizedCode.optionIndex_lt o)]
  cases o with
  | none =>
      simp only [HomogenizedCode.optionIndex, show ¬2 + i.val = 0 by omega,
        false_and, if_false, show ¬2 + i.val = 1 by omega,
        show 2 ≤ 2 + i.val by omega, true_and, show ¬1 = 2 + i.val by omega,
        RationalCode.value_zero, homVec_none]
  | some j =>
      by_cases h : j = i
      · subst j
        simp only [HomogenizedCode.optionIndex, show ¬2 + i.val = 0 by omega,
          false_and, if_false, show ¬2 + i.val = 1 by omega,
          show 2 ≤ 2 + i.val by omega, true_and,
          show i.val + 1 + 1 = 2 + i.val by omega, if_true, RationalCode.value_one,
          homVec_some, Pi.single_eq_same]
      · have hnat : j.val + 1 + 1 ≠ 2 + i.val := by
          intro heq
          apply h
          apply Fin.ext
          omega
        simp only [HomogenizedCode.optionIndex, show ¬2 + i.val = 0 by omega,
          false_and, if_false, show ¬2 + i.val = 1 by omega,
          show 2 ≤ 2 + i.val by omega, true_and, hnat, RationalCode.value_zero,
          homVec_some, Pi.single_eq_of_ne h]

@[simp] theorem value_gen_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (i : Fin (2 + r)) :
    value F.homogenize (gen r (EquationCode.ofEquation F) i.val) =
      cubeGen F.homogenize i := by
  induction i using Fin.addCases with
  | left i =>
      fin_cases i
      · change value F.homogenize (gen r (EquationCode.ofEquation F) 0) =
          cubeGen F.homogenize (Fin.castAdd r 0)
        rw [gen, value_expMinusOne_ofEquation, generatorVector_zero_value,
          cubeGen_zero]
      · change value F.homogenize (gen r (EquationCode.ofEquation F) 1) =
          cubeGen F.homogenize (Fin.castAdd r 1)
        rw [gen, value_expMinusOne_ofEquation, generatorVector_one_value,
          cubeGen_one]
  | right i =>
      change value F.homogenize
          (gen r (EquationCode.ofEquation F) (2 + i.val)) =
        cubeGen F.homogenize (Fin.natAdd 2 i)
      rw [gen, value_expMinusOne_ofEquation, generatorVector_natAdd_value,
        cubeGen_natAdd]

@[simp] theorem value_image_ofEquation {r : ℕ} (F : DegreeTwoEquation r)
    (e : Fin (2 + r) → ℕ) :
    value F.homogenize
        (image r (EquationCode.ofEquation F) (exponentList e)) =
      cubeImage F.homogenize e := by
  rw [image, cubeImage, Fin.prod_univ_def]
  rw [← List.map_coe_finRange_eq_range]
  have h : ∀ (l : List (Fin (2 + r))) (acc : Code),
      value F.homogenize
          ((l.map Fin.val).foldl
            (fun a i => mul r (EquationCode.ofEquation F) a
              (pow r (EquationCode.ofEquation F) (gen r (EquationCode.ofEquation F) i)
                ((exponentList e).getD i 0))) acc) =
        value F.homogenize acc *
          (l.map fun i => cubeGen F.homogenize i ^ e i).prod := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons i l ih =>
        simp only [List.map_cons, List.foldl_cons, ih, value_mul_ofEquation,
          value_pow_ofEquation, List.prod_cons, mul_assoc]
        rw [ProgramCode.exponentList_getD, value_gen_ofEquation]
  rw [h, value_one, one_mul]

end CubeAlgebraCode

/-! ### First-order exponent lists -/

namespace ExponentCode

/-- The lists of length `k` whose entries sum to `n`, in the same lexicographic order as
`List.Nat.antidiagonalTuple`. -/
def tuples : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | k + 1, n =>
      (List.Nat.antidiagonal n).flatMap fun ni =>
        (tuples k ni.2).map fun tail => ni.1 :: tail

/-- Dense exponent lists of total degree at most four. -/
def low (r : ℕ) : List (List ℕ) :=
  (List.range 5).flatMap (tuples (2 + r))

/-- Dense exponent lists of total degree five. -/
def degreeFive (r : ℕ) : List (List ℕ) :=
  tuples (2 + r) 5

theorem exponentList_cons {k : ℕ} (a : ℕ) (tail : Fin k → ℕ) :
    exponentList (Fin.cons a tail) = a :: exponentList tail := by
  rw [exponentList, exponentList]
  exact List.ofFn_succ

theorem tuples_eq_map_exponentList (k n : ℕ) :
    tuples k n = (List.Nat.antidiagonalTuple k n).map exponentList := by
  induction k generalizing n with
  | zero => cases n <;> rfl
  | succ k ih =>
      rw [tuples, List.Nat.antidiagonalTuple]
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro ni _
      rw [ih, List.map_map, List.map_map]
      apply List.map_congr_left
      intro tail _
      simp only [Function.comp_apply, exponentList_cons]

theorem low_eq_map_exponentList (r : ℕ) :
    low r = (lowMonomials r).map exponentList := by
  rw [low, lowMonomials, exponentsLE]
  norm_num
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro n _
  exact tuples_eq_map_exponentList (2 + r) n

theorem degreeFive_eq_map_exponentList (r : ℕ) :
    degreeFive r = (exponentsEQ (2 + r) 5).map exponentList :=
  tuples_eq_map_exponentList (2 + r) 5

@[simp] theorem low_length (r : ℕ) : (low r).length = (lowMonomials r).length := by
  rw [low_eq_map_exponentList, List.length_map]

end ExponentCode

/-! ### Rows of the residue linear system -/

namespace RowsCode

/-- One coded row, indexed by the degree-at-most-four monomial list. -/
abbrev Row := RationalVectorCode

/-- One base-algebra coordinate row. -/
def baseRow (r coordinate : ℕ) : Row :=
  (ExponentCode.low r).map fun e =>
    (BaseAlgebraCode.image r e).getD coordinate RationalCode.zero

/-- The base-algebra block, in the coordinate order of `baseCoordFns`. -/
def baseRows (r : ℕ) : List Row :=
  (List.range 5).map (baseRow r) ++
    (List.range r).map fun i => baseRow r (5 + i)

/-- One cube-algebra coordinate row. -/
def cubeRow (r : ℕ) (F : EquationCode) (coordinate : ℕ) : Row :=
  (ExponentCode.low r).map fun e =>
    (CubeAlgebraCode.image r F e).getD coordinate RationalCode.zero

/-- The coordinate rows for one cube algebra, in the order of `cubeCoordFns`. -/
def cubeRows (r : ℕ) (F : EquationCode) : List Row :=
  [cubeRow r F 0, cubeRow r F 1] ++
    (List.range r).map (fun i => cubeRow r F (i + 2)) ++
    [cubeRow r F (r + 2)]

/-- All rows of the residue linear system. -/
def rows (r : ℕ) (equations : List EquationCode) : List Row :=
  baseRows r ++ equations.flatMap (cubeRows r)

/-- Interpret a coded row as a rational vector with the semantic monomial-list length. -/
noncomputable def valueRow (r : ℕ) (row : Row) :
    Fin (lowMonomials r).length → ℚ :=
  fun j => (row.getD j.val RationalCode.zero).value

/-- Interpret a list of coded rows. -/
noncomputable def valueRows (r : ℕ) (codedRows : List Row) :
    List (Fin (lowMonomials r).length → ℚ) :=
  codedRows.map (valueRow r)

theorem low_getD (r : ℕ) (j : Fin (lowMonomials r).length) :
    (ExponentCode.low r).getD j.val [] = exponentList (lowMonomial r j) := by
  rw [ExponentCode.low_eq_map_exponentList]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map]
    exact j.isLt), List.getElem_map]
  rfl

theorem low_getElem (r : ℕ) (j : Fin (lowMonomials r).length) :
    (ExponentCode.low r)[j.val]'(by rw [ExponentCode.low_length]; exact j.isLt) =
      exponentList (lowMonomial r j) := by
  have h := low_getD r j
  rw [List.getD_eq_getElem _ _ (by
    rw [ExponentCode.low_length]
    exact j.isLt)] at h
  exact h

theorem value_baseRow_b (r : ℕ) (k : Fin 5) :
    valueRow r (baseRow r k.val) =
      fun j => bCoord r k (baseImage r (lowMonomial r j)) := by
  funext j
  rw [valueRow, baseRow]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map, ExponentCode.low_length]
    exact j.isLt), List.getElem_map, low_getElem r j]
  have h := congrArg (bCoord r k)
    (BaseAlgebraCode.value_image r (lowMonomial r j))
  fin_cases k <;> exact h

theorem value_baseRow_c (r : ℕ) (i : Fin r) :
    valueRow r (baseRow r (5 + i.val)) =
      fun j => cCoord r i (baseImage r (lowMonomial r j)) := by
  funext j
  rw [valueRow, baseRow]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map, ExponentCode.low_length]
    exact j.isLt), List.getElem_map, low_getElem r j]
  exact congrArg (cCoord r i) (BaseAlgebraCode.value_image r (lowMonomial r j))

theorem value_baseRows (r : ℕ) :
    valueRows r (baseRows r) =
      (baseCoordFns r).map fun κ => fun j => κ (baseImage r (lowMonomial r j)) := by
  simp only [valueRows, baseRows, List.map_append, List.map_map, baseCoordFns]
  congr 1
  · rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro k _
    exact value_baseRow_b r k
  · rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro i _
    exact value_baseRow_c r i

theorem value_cubeRow_scalar {r : ℕ} (F : DegreeTwoEquation r) :
    valueRow r (cubeRow r (EquationCode.ofEquation F) 0) =
      fun j => scalarCoord F.homogenize (cubeImage F.homogenize (lowMonomial r j)) := by
  funext j
  rw [valueRow, cubeRow]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map, ExponentCode.low_length]
    exact j.isLt), List.getElem_map, low_getElem r j]
  exact congrArg (scalarCoord F.homogenize)
    (CubeAlgebraCode.value_image_ofEquation F (lowMonomial r j))

theorem value_cubeRow_vector {r : ℕ} (F : DegreeTwoEquation r)
    (o : Option (Fin r)) :
    valueRow r
        (cubeRow r (EquationCode.ofEquation F) (HomogenizedCode.optionIndex o + 1)) =
      fun j => vectorCoord F.homogenize o
        (cubeImage F.homogenize (lowMonomial r j)) := by
  funext j
  rw [valueRow, cubeRow]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map, ExponentCode.low_length]
    exact j.isLt), List.getElem_map, low_getElem r j]
  exact congrArg (vectorCoord F.homogenize o)
    (CubeAlgebraCode.value_image_ofEquation F (lowMonomial r j))

theorem value_cubeRow_socle {r : ℕ} (F : DegreeTwoEquation r) :
    valueRow r (cubeRow r (EquationCode.ofEquation F) (r + 2)) =
      fun j => socleCoord F.homogenize (cubeImage F.homogenize (lowMonomial r j)) := by
  funext j
  rw [valueRow, cubeRow]
  rw [List.getD_eq_getElem _ _ (by
    rw [List.length_map, ExponentCode.low_length]
    exact j.isLt), List.getElem_map, low_getElem r j]
  exact congrArg (socleCoord F.homogenize)
    (CubeAlgebraCode.value_image_ofEquation F (lowMonomial r j))

theorem value_cubeRows {r : ℕ} (F : DegreeTwoEquation r) :
    valueRows r (cubeRows r (EquationCode.ofEquation F)) =
      (cubeCoordFns F.homogenize).map fun κ =>
        fun j => κ (cubeImage F.homogenize (lowMonomial r j)) := by
  simp only [valueRows, cubeRows, List.map_append, List.map_cons, List.map_nil,
    List.map_map, cubeCoordFns]
  have hnone := value_cubeRow_vector F (none : Option (Fin r))
  change valueRow r (cubeRow r (EquationCode.ofEquation F) 1) = _ at hnone
  rw [value_cubeRow_scalar, hnone, value_cubeRow_socle]
  simp only [List.cons_append, List.nil_append]
  congr 2
  congr 1
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  apply List.map_congr_left
  intro i _
  simpa only [HomogenizedCode.optionIndex, Nat.add_assoc] using
    value_cubeRow_vector F (some i)

theorem value_rows {r : ℕ} (equations : List (DegreeTwoEquation r)) :
    valueRows r (rows r (equations.map EquationCode.ofEquation)) =
      Trinomial.rows (homogenizedSystem equations) := by
  change valueRows r (rows r (equations.map EquationCode.ofEquation)) =
    Trinomial.rows (fun i => (equations.get i).homogenize)
  rw [rows]
  rw [valueRows, List.map_append]
  change valueRows r (baseRows r) ++
      (((equations.map EquationCode.ofEquation).flatMap (cubeRows r)).map
        (valueRow r)) = _
  rw [value_baseRows]
  rw [List.flatMap_map, List.map_flatMap]
  have hcubes :
      (equations.flatMap fun F =>
        (cubeRows r (EquationCode.ofEquation F)).map (valueRow r)) =
        equations.flatMap fun F =>
          (cubeCoordFns F.homogenize).map fun κ =>
            fun j => κ (cubeImage F.homogenize (lowMonomial r j)) := by
    apply List.flatMap_congr
    intro F _
    simpa only [valueRows] using value_cubeRows F
  rw [hcubes]
  simp only [Trinomial.rows, materialize_eq]
  congr 1
  · apply List.map_congr_left
    intro κ _
    funext j
    simp [lowMonomial]
  · conv_lhs => rw [← List.map_get_finRange equations, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    apply List.map_congr_left
    intro κ _
    funext j
    simp [lowMonomial]

end RowsCode

/-! ### Gaussian elimination on coded rational vectors -/

namespace KernelCode

/-- Evaluate a coded row on a coded vector. -/
def rowEval (n : ℕ) (row vector : RationalVectorCode) : RationalCode :=
  RationalVectorCode.dot n row vector

/-- The coded standard basis of `ℚⁿ`. -/
def standardBasis (n : ℕ) : List RationalVectorCode :=
  (List.range n).map fun i =>
    RationalVectorCode.tabulate n fun j =>
      if i = j then RationalCode.one else RationalCode.zero

/-- The substitution `w - c v` on coded vectors. -/
def subSmul (n : ℕ) (w v : RationalVectorCode) (c : RationalCode) :
    RationalVectorCode :=
  RationalVectorCode.tabulate n fun j =>
    RationalCode.sub (w.getD j RationalCode.zero)
      (RationalCode.mul c (v.getD j RationalCode.zero))

/-- One coded Gaussian-elimination step. -/
def eliminate (n : ℕ) (row : RationalVectorCode) :
    List RationalVectorCode → List RationalVectorCode
  | [] => []
  | v :: vectors =>
      if RationalCode.Equivalent (rowEval n row v) RationalCode.zero then
        v :: eliminate n row vectors
      else
        vectors.map fun w => subSmul n w v
          (RationalCode.div (rowEval n row w) (rowEval n row v))

/-- A coded spanning set for the common kernel of a row list. -/
def kernelBasis (n : ℕ) : List RationalVectorCode → List RationalVectorCode
  | [] => standardBasis n
  | row :: rows => eliminate n row (kernelBasis n rows)

/-- Decode a coded rational vector. -/
noncomputable def valueVector (n : ℕ) (v : RationalVectorCode) : Fin n → ℚ :=
  fun j => (v.getD j.val RationalCode.zero).value

/-- Decode a list of coded rational vectors. -/
noncomputable def valueVectors (n : ℕ) (vectors : List RationalVectorCode) :
    List (Fin n → ℚ) :=
  vectors.map (valueVector n)

@[simp] theorem valueVectors_nil (n : ℕ) :
    valueVectors n [] = [] := rfl

@[simp] theorem valueVectors_cons (n : ℕ) (v : RationalVectorCode)
    (vectors : List RationalVectorCode) :
    valueVectors n (v :: vectors) = valueVector n v :: valueVectors n vectors := rfl

@[simp] theorem value_rowEval (n : ℕ) (row vector : RationalVectorCode) :
    (rowEval n row vector).value =
      Trinomial.rowEval (valueVector n row) (valueVector n vector) := by
  rw [rowEval, RationalVectorCode.dot, RationalCode.value_sum]
  simp only [List.map_map, Function.comp_def, RationalCode.value_mul,
    Trinomial.rowEval, Fin.sum_univ_def, valueVector]
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

@[simp] theorem value_subSmul (n : ℕ) (w v : RationalVectorCode)
    (c : RationalCode) :
    valueVector n (subSmul n w v c) =
      valueVector n w - c.value • valueVector n v := by
  funext j
  rw [valueVector, subSmul, RationalVectorCode.getD_tabulate _ j.isLt]
  simp [valueVector, sub_eq_add_neg]

theorem standardBasis_getD {n i : ℕ} (hi : i < n) :
    (standardBasis n).getD i [] =
      RationalVectorCode.tabulate n fun j =>
        if i = j then RationalCode.one else RationalCode.zero := by
  rw [standardBasis, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

@[simp] theorem value_standardBasis (n : ℕ) :
    valueVectors n (standardBasis n) =
      (List.finRange n).map fun j => Pi.single j 1 := by
  rw [valueVectors, standardBasis, ← List.map_coe_finRange_eq_range,
    List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  funext j
  change ((RationalVectorCode.tabulate n fun j =>
    if i.val = j then RationalCode.one else RationalCode.zero).getD j.val
      RationalCode.zero).value = _
  rw [RationalVectorCode.getD_tabulate _ j.isLt]
  simp only [Pi.single_apply]
  by_cases h : i = j
  · subst j; simp
  · have hval : i.val ≠ j.val := fun heq => h (Fin.ext heq)
    have hrev : j ≠ i := Ne.symm h
    simp [hval, hrev]

theorem value_eliminate (n : ℕ) (row : RationalVectorCode)
    (vectors : List RationalVectorCode) :
    valueVectors n (eliminate n row vectors) =
      Trinomial.eliminate (valueVector n row) (valueVectors n vectors) := by
  induction vectors with
  | nil => rfl
  | cons v vectors ih =>
      rw [eliminate, Trinomial.eliminate.eq_def]
      have hiff : RationalCode.Equivalent (rowEval n row v) RationalCode.zero ↔
          Trinomial.rowEval (valueVector n row) (valueVector n v) = 0 := by
        rw [RationalCode.equivalent_iff_value_eq, value_rowEval,
          RationalCode.value_zero]
      by_cases hcode : RationalCode.Equivalent (rowEval n row v) RationalCode.zero
      · have hsemantic := hiff.mp hcode
        rw [if_pos hcode, valueVectors_cons]
        change valueVector n v :: valueVectors n (eliminate n row vectors) =
          if Trinomial.rowEval (valueVector n row) (valueVector n v) = 0 then
            valueVector n v :: Trinomial.eliminate (valueVector n row)
              (valueVectors n vectors)
          else _
        rw [if_pos hsemantic, ih]
      · have hsemantic : Trinomial.rowEval (valueVector n row) (valueVector n v) ≠ 0 :=
          fun h => hcode (hiff.mpr h)
        rw [if_neg hcode]
        change valueVectors n
            (vectors.map fun w => subSmul n w v
              (RationalCode.div (rowEval n row w) (rowEval n row v))) =
          if Trinomial.rowEval (valueVector n row) (valueVector n v) = 0 then _
          else (valueVectors n vectors).map fun w =>
            w - (Trinomial.rowEval (valueVector n row) w /
              Trinomial.rowEval (valueVector n row) (valueVector n v)) • valueVector n v
        rw [if_neg hsemantic]
        simp only [valueVectors, List.map_map]
        apply List.map_congr_left
        intro w _
        simp only [Function.comp_apply, value_subSmul, RationalCode.value_div,
          value_rowEval]

@[simp] theorem value_kernelBasis (n : ℕ) (codedRows : List RationalVectorCode) :
    valueVectors n (kernelBasis n codedRows) =
      Trinomial.kernelBasis (valueVectors n codedRows) := by
  induction codedRows with
  | nil =>
      rw [kernelBasis, value_standardBasis]
      change (List.finRange n).map (fun j => Pi.single j 1) =
        Trinomial.kernelBasis ([] : List (Fin n → ℚ))
      rw [Trinomial.kernelBasis.eq_def]
  | cons row codedRows ih =>
      rw [kernelBasis, value_eliminate, ih]
      change Trinomial.eliminate (valueVector n row)
          (Trinomial.kernelBasis (valueVectors n codedRows)) =
        Trinomial.kernelBasis (valueVector n row :: valueVectors n codedRows)
      conv_rhs => rw [Trinomial.kernelBasis.eq_def]

end KernelCode

/-! ### Generator polynomials in point coordinates -/

namespace PointGeneratorCode

/-- Remove zero coefficients from a coded kernel vector and attach the corresponding
degree-at-most-four exponent lists. -/
def kernelPolynomial (r : ℕ) (v : RationalVectorCode) : RawPolynomial :=
  ((List.range (ExponentCode.low r).length).map fun j =>
    (v.getD j RationalCode.zero, (ExponentCode.low r).getD j [])).filter fun term =>
      ¬RationalCode.Equivalent term.1 RationalCode.zero

/-- The generator list in the point coordinates `s,t,c`. -/
def generators (r : ℕ) (equations : List EquationCode) : List RawPolynomial :=
  (ExponentCode.degreeFive r).map (fun e => [(RationalCode.one, e)]) ++
    (KernelCode.kernelBasis (ExponentCode.low r).length (RowsCode.rows r equations)).map
      (kernelPolynomial r)

/-- Interpret a coded sparse polynomial as a `PointPoly`. -/
noncomputable def valuePolynomial (r : ℕ) (p : RawPolynomial) : PointPoly r :=
  p.map fun term => (term.1.value, exponentOfList (2 + r) term.2)

/-- Interpret a coded point-coordinate generator list. -/
noncomputable def valueGenerators (r : ℕ) (coded : List RawPolynomial) :
    List (PointPoly r) :=
  coded.map (valuePolynomial r)

theorem valuePolynomial_single (r : ℕ) (e : Fin (2 + r) → ℕ) :
    valuePolynomial r [(RationalCode.one, exponentList e)] = [(1, e)] := by
  simp [valuePolynomial]

theorem value_kernelPolynomial (r : ℕ) (v : RationalVectorCode) :
    valuePolynomial r (kernelPolynomial r v) =
      kernelPoly (KernelCode.valueVector (lowMonomials r).length v) := by
  classical
  rw [kernelPolynomial, valuePolynomial, kernelPoly, ExponentCode.low_length]
  rw [← List.map_coe_finRange_eq_range]
  have hpredicate :
      (fun term : RationalCode × List ℕ =>
        decide (¬RationalCode.Equivalent term.1 RationalCode.zero)) =
        (fun term : ℚ × (Fin (2 + r) → ℕ) => decide (term.1 ≠ 0)) ∘
          (fun term => (term.1.value, exponentOfList (2 + r) term.2)) := by
    funext term
    simp [RationalCode.equivalent_iff_value_eq]
  rw [hpredicate, ← List.filter_map]
  apply congrArg (List.filter fun term : ℚ × (Fin (2 + r) → ℕ) => term.1 ≠ 0)
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  change
    ((v.getD j.val RationalCode.zero).value,
        exponentOfList (2 + r) ((ExponentCode.low r).getD j.val [])) =
      (KernelCode.valueVector (lowMonomials r).length v j, lowMonomial r j)
  rw [RowsCode.low_getD]
  simp [KernelCode.valueVector]

theorem value_generators {r : ℕ} (equations : List (DegreeTwoEquation r)) :
    valueGenerators r
        (generators r (equations.map EquationCode.ofEquation)) =
      Trinomial.generators (homogenizedSystem equations) := by
  rw [valueGenerators, generators, Trinomial.generators, List.map_append,
    List.map_map]
  congr 1
  · rw [ExponentCode.degreeFive_eq_map_exponentList, List.map_map]
    apply List.map_congr_left
    intro e _
    exact valuePolynomial_single r e
  · rw [ExponentCode.low_length]
    let codedKernel :=
      KernelCode.kernelBasis (lowMonomials r).length
        (RowsCode.rows r (equations.map EquationCode.ofEquation))
    calc
      (codedKernel.map (kernelPolynomial r)).map (valuePolynomial r) =
          (KernelCode.valueVectors (lowMonomials r).length codedKernel).map kernelPoly := by
        rw [KernelCode.valueVectors, List.map_map, List.map_map]
        apply List.map_congr_left
        intro v _
        exact value_kernelPolynomial r v
      _ = (Trinomial.kernelBasis (Trinomial.rows (homogenizedSystem equations))).map
          (kernelPolyWith (lowMonomials r).toArray (by simp)) := by
        rw [KernelCode.value_kernelBasis]
        have hrows :
            KernelCode.valueVectors (lowMonomials r).length
                (RowsCode.rows r (equations.map EquationCode.ofEquation)) =
              Trinomial.rows (homogenizedSystem equations) := by
          exact RowsCode.value_rows equations
        rw [hrows]
        apply List.map_congr_left
        intro v _
        exact (kernelPolyWith_toArray v).symm

end PointGeneratorCode

/-! ### Expansion in the standard polynomial coordinates -/

namespace StandardPolynomialCode

/-- The all-zero exponent list of the specified arity. -/
def zeroExponent (n : ℕ) : List ℕ :=
  List.replicate n 0

/-- The exponent list of the standard variable at natural-number position `i`. -/
def unitExponent (n i : ℕ) : List ℕ :=
  (List.range n).map fun j => if j = i then 1 else 0

/-- A coded constant polynomial. -/
def constant (n : ℕ) (a : RationalCode) : RawPolynomial :=
  [(a, zeroExponent n)]

/-- A coded standard variable. -/
def standardVariable (n i : ℕ) : RawPolynomial :=
  [(RationalCode.one, unitExponent n i)]

/-- Scalar multiplication of a coded polynomial. -/
def scale (n : ℕ) (a : RationalCode) (p : RawPolynomial) : RawPolynomial :=
  RawPolynomial.mul n (constant n a) p

/-- Subtraction of coded polynomials. -/
def sub (p q : RawPolynomial) : RawPolynomial :=
  RawPolynomial.add p (RawPolynomial.neg q)

/-- A natural power of a coded polynomial. -/
def pow (n : ℕ) (p : RawPolynomial) : ℕ → RawPolynomial
  | 0 => constant n RationalCode.one
  | k + 1 => RawPolynomial.mul n p (pow n p k)

/-- A finite product of coded polynomials. -/
def product (n : ℕ) : List RawPolynomial → RawPolynomial
  | [] => constant n RationalCode.one
  | p :: polynomials => RawPolynomial.mul n p (product n polynomials)

/-- The `i`-th point coordinate written in the standard coordinates.  Positions `0`
and `1` are `2S - 1` and `2T - 1`; every later position is `D_i - 1`. -/
def pointGenerator (r i : ℕ) : RawPolynomial :=
  let n := 2 + r
  sub (scale n (if i < 2 then RationalCode.two else RationalCode.one)
      (standardVariable n i))
    (constant n RationalCode.one)

/-- Expand one point-coordinate monomial in the standard coordinates. -/
def pointMonomial (r : ℕ) (e : List ℕ) : RawPolynomial :=
  let n := 2 + r
  product n ((List.range n).map fun i => pow n (pointGenerator r i) (e.getD i 0))

/-- Expand a sparse polynomial in `s,t,c` into the standard coordinates `S,T,D`. -/
def expand (r : ℕ) (p : RawPolynomial) : RawPolynomial :=
  p.flatMap fun term => scale (2 + r) term.1 (pointMonomial r term.2)

/-- The coordinate ordering used by coded presentations: `S`, `T`, followed by the
variables `D_i`. -/
def standardVar (r : ℕ) : Fin (2 + r) → Var r :=
  Fin.append ![Var.S, Var.T] Var.D

@[simp] theorem zeroExponent_length (n : ℕ) : (zeroExponent n).length = n := by
  simp [zeroExponent]

@[simp] theorem unitExponent_length (n i : ℕ) : (unitExponent n i).length = n := by
  simp [unitExponent]

@[simp] theorem exponentOfList_zeroExponent (n : ℕ) :
    exponentOfList n (zeroExponent n) = 0 := by
  funext i
  simp [exponentOfList, zeroExponent]

theorem exponentOfList_unitExponent (n i : ℕ) (hi : i < n) :
    exponentOfList n (unitExponent n i) = Pi.single ⟨i, hi⟩ 1 := by
  funext j
  simp only [exponentOfList, unitExponent]
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_map,
    List.getElem_range]
  by_cases h : j = ⟨i, hi⟩
  · subst j
    simp
  · have hval : j.val ≠ i := fun hval => h (Fin.ext hval)
    simp [hval, h]

@[simp] theorem toPoly_constant (n : ℕ) (a : RationalCode) :
    RawPolynomial.toPoly n (constant n a) = MvPolynomial.C a.value := by
  simp only [constant, RawPolynomial.toPoly_cons, RawPolynomial.toPoly_nil,
    exponentOfList_zeroExponent, add_zero]
  have hzero : Finsupp.equivFunOnFinite.symm (0 : Fin n → ℕ) =
      (0 : Fin n →₀ ℕ) := by
    ext i
    simp
  rw [hzero]
  rfl

@[simp] theorem toPoly_variable (n i : ℕ) (hi : i < n) :
    RawPolynomial.toPoly n (standardVariable n i) = MvPolynomial.X ⟨i, hi⟩ := by
  rw [standardVariable, RawPolynomial.toPoly_cons, RawPolynomial.toPoly_nil,
    RationalCode.value_one, exponentOfList_unitExponent n i hi]
  rw [add_zero]
  congr 1
  ext j
  simp

@[simp] theorem toPoly_scale (n : ℕ) (a : RationalCode) (p : RawPolynomial) :
    RawPolynomial.toPoly n (scale n a p) =
      MvPolynomial.C a.value * RawPolynomial.toPoly n p := by
  simp [scale]

@[simp] theorem toPoly_sub (n : ℕ) (p q : RawPolynomial) :
    RawPolynomial.toPoly n (sub p q) =
      RawPolynomial.toPoly n p - RawPolynomial.toPoly n q := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem toPoly_pow (n : ℕ) (p : RawPolynomial) (k : ℕ) :
    RawPolynomial.toPoly n (pow n p k) = RawPolynomial.toPoly n p ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ']

@[simp] theorem toPoly_product (n : ℕ) (polynomials : List RawPolynomial) :
    RawPolynomial.toPoly n (product n polynomials) =
      (polynomials.map (RawPolynomial.toPoly n)).prod := by
  induction polynomials with
  | nil => simp [product]
  | cons p polynomials ih => simp [product, ih]

theorem toPoly_pointGenerator (r : ℕ) (i : Fin (2 + r)) :
    RawPolynomial.toPoly (2 + r) (pointGenerator r i.val) =
      MvPolynomial.C (if i.val < 2 then (2 : ℚ) else 1) * MvPolynomial.X i - 1 := by
  by_cases h : i.val < 2 <;> simp [pointGenerator, i.isLt, h]

@[simp] theorem standardVar_castAdd_zero (r : ℕ) :
    standardVar r (Fin.castAdd r 0) = Var.S := by
  simp [standardVar, Fin.append_left]

@[simp] theorem standardVar_castAdd_one (r : ℕ) :
    standardVar r (Fin.castAdd r 1) = Var.T := by
  simp [standardVar, Fin.append_left]

@[simp] theorem standardVar_natAdd (r : ℕ) (i : Fin r) :
    standardVar r (Fin.natAdd 2 i) = Var.D i := by
  simp [standardVar, Fin.append_right]

theorem rename_toPoly_pointGenerator (r : ℕ) (i : Fin (2 + r)) :
    MvPolynomial.rename (standardVar r)
        (RawPolynomial.toPoly (2 + r) (pointGenerator r i.val)) =
      Trinomial.pointGen r i := by
  rw [toPoly_pointGenerator]
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j <;> simp [MvPolynomial.rename_X] <;>
      exact map_ofNat MvPolynomial.C 2
  · intro j
    simp [MvPolynomial.rename_X]

theorem rename_toPoly_pointMonomial (r : ℕ) (e : List ℕ) :
    MvPolynomial.rename (standardVar r)
        (RawPolynomial.toPoly (2 + r) (pointMonomial r e)) =
      Trinomial.pointMonomial r (exponentOfList (2 + r) e) := by
  rw [pointMonomial, toPoly_product, map_list_prod, List.map_map,
    Trinomial.pointMonomial, Fin.prod_univ_def]
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, map_pow, toPoly_pow]
  rw [rename_toPoly_pointGenerator]
  rfl

theorem rename_toPoly_expand (r : ℕ) (p : RawPolynomial) :
    MvPolynomial.rename (standardVar r)
        (RawPolynomial.toPoly (2 + r) (expand r p)) =
      (PointGeneratorCode.valuePolynomial r p).toPoly := by
  induction p with
  | nil => simp [expand, PointGeneratorCode.valuePolynomial, PointPoly.toPoly]
  | cons term p ih =>
      rw [show expand r (term :: p) =
          scale (2 + r) term.1 (pointMonomial r term.2) ++ expand r p by rfl]
      rw [RawPolynomial.toPoly_append, map_add, toPoly_scale, map_mul,
        MvPolynomial.rename_C,
        rename_toPoly_pointMonomial, ih]
      simp only [PointGeneratorCode.valuePolynomial, PointPoly.toPoly, List.map_cons,
        List.sum_cons]
      rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]

theorem valid_constant (n : ℕ) (a : RationalCode) :
    RawPolynomial.Valid n (constant n a) := by
  intro term hterm
  simp only [constant, List.mem_singleton] at hterm
  subst term
  exact zeroExponent_length n

theorem valid_scale (n : ℕ) (a : RationalCode) (p : RawPolynomial) :
    RawPolynomial.Valid n (scale n a p) :=
  RawPolynomial.valid_mul n _ _

theorem valid_sub {n : ℕ} {p q : RawPolynomial}
    (hp : RawPolynomial.Valid n p) (hq : RawPolynomial.Valid n q) :
    RawPolynomial.Valid n (sub p q) :=
  RawPolynomial.valid_add hp (RawPolynomial.valid_neg hq)

theorem valid_pow (n : ℕ) (p : RawPolynomial) (k : ℕ) :
    RawPolynomial.Valid n (pow n p k) := by
  cases k with
  | zero => exact valid_constant n RationalCode.one
  | succ k => exact RawPolynomial.valid_mul n _ _

theorem valid_product (n : ℕ) (polynomials : List RawPolynomial) :
    RawPolynomial.Valid n (product n polynomials) := by
  cases polynomials with
  | nil => exact valid_constant n RationalCode.one
  | cons p polynomials => exact RawPolynomial.valid_mul n _ _

theorem valid_pointMonomial (r : ℕ) (e : List ℕ) :
    RawPolynomial.Valid (2 + r) (pointMonomial r e) :=
  valid_product _ _

theorem valid_expand (r : ℕ) (p : RawPolynomial) :
    RawPolynomial.Valid (2 + r) (expand r p) := by
  intro term hterm
  rw [expand, List.mem_flatMap] at hterm
  obtain ⟨source, _, hterm⟩ := hterm
  exact valid_scale (2 + r) source.1 (pointMonomial r source.2) term hterm

end StandardPolynomialCode

/-! ### The first-order compiler -/

/-- The raw compiler from sparse integer-polynomial syntax to a finite rational ideal
presentation. -/
def compilerRaw (q : PolynomialInputRaw) : IdealPresentationRaw :=
  let system := ProgramCode.guardedSystem q.1 q.2
  (2 + system.1,
    (PointGeneratorCode.generators system.1 system.2).map
      (StandardPolynomialCode.expand system.1))

theorem compiledGenerators_valid (r : ℕ) (equations : List EquationCode) :
    IdealPresentationRaw.Valid
      (2 + r,
        (PointGeneratorCode.generators r equations).map
          (StandardPolynomialCode.expand r)) := by
  intro term hterm
  rw [List.mem_flatten] at hterm
  obtain ⟨polynomial, hpolynomial, hterm⟩ := hterm
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hpolynomial
  exact StandardPolynomialCode.valid_expand r source term hterm

theorem compilerRaw_valid (q : PolynomialInputRaw) : compilerRaw q |>.Valid := by
  rw [compilerRaw]
  exact compiledGenerators_valid _ _

/-- The compiler on valid first-order input codes. -/
def compilerCode (q : PolynomialInputCode) : IdealPresentationCode :=
  ⟨compilerRaw q.1, compilerRaw_valid q.1⟩

/-- The compiler on the dependent input and output types used by the decision
problems. -/
def compiler (p : PolynomialInput) : IdealPresentation :=
  idealPresentationOfCode (compilerCode (polynomialInputToCode p))

theorem compilerRaw_ofPolynomial {n : ℕ} (p : IntPolynomialCode n) :
    compilerRaw (polynomialInputToCode ⟨n, p⟩).1 =
      (2 + numVars p,
        (PointGeneratorCode.generators (numVars p)
          ((guarded (degreeTwoSystem p)).map EquationCode.ofEquation)).map
            (StandardPolynomialCode.expand (numVars p))) := by
  change compilerRaw
      (n, p.map fun term => (exponentList term.1, term.2)) = _
  rw [compilerRaw]
  rw [ProgramCode.guardedSystem_ofProgram]

@[simp] theorem compiler_arity {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).1 = 2 + numVars p := by
  change (compilerCode (polynomialInputToCode ⟨n, p⟩)).1.1 = _
  change (compilerRaw (polynomialInputToCode ⟨n, p⟩).1).1 = _
  rw [compilerRaw_ofPolynomial]

theorem compiler_rawGenerators {n : ℕ} (p : IntPolynomialCode n) :
    (compiler ⟨n, p⟩).rawGenerators =
      (PointGeneratorCode.generators (numVars p)
        ((guarded (degreeTwoSystem p)).map EquationCode.ofEquation)).map
          (StandardPolynomialCode.expand (numVars p)) := by
  rw [IdealPresentation.rawGenerators, compiler]
  rw [idealPresentationToCode_ofCode]
  change (compilerRaw (polynomialInputToCode ⟨n, p⟩).1).2 = _
  rw [compilerRaw_ofPolynomial]

theorem rename_toPoly_compilerGenerators {n : ℕ} (p : IntPolynomialCode n) :
    ((compiler ⟨n, p⟩).rawGenerators.map fun polynomial =>
      MvPolynomial.rename (StandardPolynomialCode.standardVar (numVars p))
        (RawPolynomial.toPoly (2 + numVars p) polynomial)) =
      (generatorsOf p).map PointPoly.toPoly := by
  rw [compiler_rawGenerators, List.map_map]
  calc
    ((PointGeneratorCode.generators (numVars p)
        ((guarded (degreeTwoSystem p)).map EquationCode.ofEquation)).map
          (fun polynomial =>
            MvPolynomial.rename (StandardPolynomialCode.standardVar (numVars p))
              (RawPolynomial.toPoly (2 + numVars p)
                (StandardPolynomialCode.expand (numVars p) polynomial)))) =
        (PointGeneratorCode.valueGenerators (numVars p)
          (PointGeneratorCode.generators (numVars p)
            ((guarded (degreeTwoSystem p)).map EquationCode.ofEquation))).map
              PointPoly.toPoly := by
      rw [PointGeneratorCode.valueGenerators, List.map_map]
      apply List.map_congr_left
      intro polynomial _
      exact StandardPolynomialCode.rename_toPoly_expand (numVars p) polynomial
    _ = (generatorsOf p).map PointPoly.toPoly := by
      rw [PointGeneratorCode.value_generators]
      rfl

/-! ### Primitive-recursive verification of the compiler -/

namespace RationalCode

theorem ofSigned_primrec : Primrec ofSigned :=
  Primrec.pair Primrec.id (Primrec.const 0)

theorem sub_primrec : Primrec₂ sub :=
  add_primrec.comp₂ Primrec₂.left (neg_primrec.comp₂ Primrec₂.right)

theorem sum_primrec : Primrec sum := by
  have hstep : Primrec₂ fun (_ : List RationalCode)
      (termResult : RationalCode × RationalCode) => add termResult.1 termResult.2 :=
    add_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact Primrec.list_foldr Primrec.id (Primrec.const zero) hstep

theorem pow_primrec : Primrec fun input : RationalCode × ℕ => pow input.1 input.2 := by
  have hstep : Primrec₂ fun (input : RationalCode × ℕ)
      (stepResult : ℕ × RationalCode) => mul stepResult.2 input.1 :=
    mul_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂ Primrec₂.left)
  exact (Primrec.nat_rec' Primrec.snd (Primrec.const one) hstep).of_eq fun input => by
    induction input.2 with
    | zero => rfl
    | succ k ih => simp [pow, ih]

end RationalCode

namespace RationalVectorCode

theorem tabulate_primrec {α : Type*} [Primcodable α] {n : α → ℕ}
    {f : α → ℕ → RationalCode} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec fun input => tabulate (n input) (f input) :=
  Primrec.list_map (Primrec.list_range.comp hn) hf

theorem zero_primrec : Primrec zero :=
  tabulate_primrec Primrec.id (Primrec.const RationalCode.zero).to₂

theorem add_primrec : Primrec fun input : ℕ × (RationalVectorCode × RationalVectorCode) =>
    add input.1 input.2.1 input.2.2 := by
  let X := ℕ × (RationalVectorCode × RationalVectorCode)
  have hx : Primrec₂ fun (input : X) (i : ℕ) => input.2.1.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hy : Primrec₂ fun (input : X) (i : ℕ) => input.2.2.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  exact tabulate_primrec Primrec.fst (RationalCode.add_primrec.comp₂ hx hy)

theorem sub_primrec : Primrec fun input : ℕ × (RationalVectorCode × RationalVectorCode) =>
    sub input.1 input.2.1 input.2.2 := by
  let X := ℕ × (RationalVectorCode × RationalVectorCode)
  have hx : Primrec₂ fun (input : X) (i : ℕ) => input.2.1.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hy : Primrec₂ fun (input : X) (i : ℕ) => input.2.2.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  exact tabulate_primrec Primrec.fst (RationalCode.sub_primrec.comp₂ hx hy)

theorem scale_primrec : Primrec fun input : ℕ × (RationalCode × RationalVectorCode) =>
    scale input.1 input.2.1 input.2.2 := by
  let X := ℕ × (RationalCode × RationalVectorCode)
  have hx : Primrec₂ fun (input : X) (i : ℕ) => input.2.2.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  exact tabulate_primrec Primrec.fst <|
    RationalCode.mul_primrec.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) hx

theorem dot_primrec : Primrec fun input : ℕ × (RationalVectorCode × RationalVectorCode) =>
    dot input.1 input.2.1 input.2.2 := by
  let X := ℕ × (RationalVectorCode × RationalVectorCode)
  have hx : Primrec₂ fun (input : X) (i : ℕ) => input.2.1.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hy : Primrec₂ fun (input : X) (i : ℕ) => input.2.2.getD i RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp₂
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have hproducts : Primrec fun input : X =>
      (List.range input.1).map fun i =>
        RationalCode.mul (input.2.1.getD i RationalCode.zero)
          (input.2.2.getD i RationalCode.zero) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (RationalCode.mul_primrec.comp₂ hx hy)
  exact RationalCode.sum_primrec.comp hproducts

end RationalVectorCode

namespace EquationCode

theorem rename_primrec {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Primrec₂ f) :
    Primrec fun input : α × EquationCode => rename (f input.1) input.2 := by
  let X := α × EquationCode
  have hquadTerm : Primrec₂ fun (input : X) (term : (SignedCode × ℕ) × ℕ) =>
      ((term.1.1, f input.1 term.1.2), f input.1 term.2) := by
    exact Primrec₂.pair.comp₂
      (Primrec₂.pair.comp₂
        ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.right)
        (hf.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
          ((Primrec.snd.comp Primrec.fst).comp₂ Primrec₂.right)))
      (hf.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.snd.comp₂ Primrec₂.right))
  have hlinTerm : Primrec₂ fun (input : X) (term : SignedCode × ℕ) =>
      (term.1, f input.1 term.2) := by
    exact Primrec₂.pair.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (hf.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.snd.comp₂ Primrec₂.right))
  have hquad : Primrec fun input : X =>
      input.2.1.map fun term =>
        ((term.1.1, f input.1 term.1.2), f input.1 term.2) :=
    Primrec.list_map (Primrec.fst.comp Primrec.snd) hquadTerm
  have hlin : Primrec fun input : X =>
      input.2.2.1.map fun term => (term.1, f input.1 term.2) :=
    Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hlinTerm
  exact Primrec.pair hquad <| Primrec.pair hlin
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem eqConst_primrec : Primrec fun input : ℕ × SignedCode =>
    eqConst input.1 input.2 := by
  have hterm : Primrec fun input : ℕ × SignedCode => (SignedCode.one, input.1) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.fst
  have hlin : Primrec fun input : ℕ × SignedCode => [(SignedCode.one, input.1)] :=
    Primrec.list_cons.comp hterm (Primrec.const [])
  exact Primrec.pair (Primrec.const []) <|
    Primrec.pair hlin (SignedCode.neg_primrec.comp Primrec.snd)

theorem eqAdd_primrec : Primrec fun input : ℕ × (ℕ × ℕ) =>
    eqAdd input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ℕ × ℕ)
  have hfirst : Primrec fun input : X => (SignedCode.one, input.1) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.fst
  have hsecond : Primrec fun input : X =>
      (SignedCode.neg SignedCode.one, input.2.1) :=
    Primrec.pair (Primrec.const (SignedCode.neg SignedCode.one))
      (Primrec.fst.comp Primrec.snd)
  have hthird : Primrec fun input : X =>
      (SignedCode.neg SignedCode.one, input.2.2) :=
    Primrec.pair (Primrec.const (SignedCode.neg SignedCode.one))
      (Primrec.snd.comp Primrec.snd)
  have hlin : Primrec fun input : X =>
      [(SignedCode.one, input.1),
        (SignedCode.neg SignedCode.one, input.2.1),
        (SignedCode.neg SignedCode.one, input.2.2)] :=
    Primrec.list_cons.comp hfirst <| Primrec.list_cons.comp hsecond <|
      Primrec.list_cons.comp hthird (Primrec.const [])
  exact Primrec.pair (Primrec.const []) <|
    Primrec.pair hlin (Primrec.const SignedCode.zero)

theorem eqMul_primrec : Primrec fun input : ℕ × (ℕ × ℕ) =>
    eqMul input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ℕ × ℕ)
  have hquadTerm : Primrec fun input : X =>
      ((SignedCode.neg SignedCode.one, input.2.1), input.2.2) :=
    Primrec.pair
      (Primrec.pair (Primrec.const (SignedCode.neg SignedCode.one))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hquad : Primrec fun input : X =>
      [((SignedCode.neg SignedCode.one, input.2.1), input.2.2)] :=
    Primrec.list_cons.comp hquadTerm (Primrec.const [])
  have hlinTerm : Primrec fun input : X => (SignedCode.one, input.1) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.fst
  have hlin : Primrec fun input : X => [(SignedCode.one, input.1)] :=
    Primrec.list_cons.comp hlinTerm (Primrec.const [])
  exact Primrec.pair hquad <| Primrec.pair hlin (Primrec.const SignedCode.zero)

theorem eqCopy_primrec : Primrec fun input : ℕ × ℕ =>
    eqCopy input.1 input.2 := by
  have hfirst : Primrec fun input : ℕ × ℕ => (SignedCode.one, input.1) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.fst
  have hsecond : Primrec fun input : ℕ × ℕ =>
      (SignedCode.neg SignedCode.one, input.2) :=
    Primrec.pair (Primrec.const (SignedCode.neg SignedCode.one)) Primrec.snd
  have hlin : Primrec fun input : ℕ × ℕ =>
      [(SignedCode.one, input.1), (SignedCode.neg SignedCode.one, input.2)] :=
    Primrec.list_cons.comp hfirst <|
      Primrec.list_cons.comp hsecond (Primrec.const [])
  exact Primrec.pair (Primrec.const []) <|
    Primrec.pair hlin (Primrec.const SignedCode.zero)

theorem eqScale_primrec : Primrec fun input : ℕ × (SignedCode × ℕ) =>
    eqScale input.1 input.2.1 input.2.2 := by
  let X := ℕ × (SignedCode × ℕ)
  have hfirst : Primrec fun input : X => (SignedCode.one, input.1) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.fst
  have hsecond : Primrec fun input : X =>
      (SignedCode.neg input.2.1, input.2.2) :=
    Primrec.pair
      (SignedCode.neg_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hlin : Primrec fun input : X =>
      [(SignedCode.one, input.1), (SignedCode.neg input.2.1, input.2.2)] :=
    Primrec.list_cons.comp hfirst <|
      Primrec.list_cons.comp hsecond (Primrec.const [])
  exact Primrec.pair (Primrec.const []) <|
    Primrec.pair hlin (Primrec.const SignedCode.zero)

theorem eqZero_primrec : Primrec eqZero := by
  have hterm : Primrec fun o : ℕ => (SignedCode.one, o) :=
    Primrec.pair (Primrec.const SignedCode.one) Primrec.id
  exact Primrec.pair (Primrec.const []) <| Primrec.pair
    (Primrec.list_cons.comp hterm (Primrec.const []))
    (Primrec.const SignedCode.zero)

theorem shiftAux_primrec : Primrec fun input : ℕ × (ℕ × ℕ) =>
    shiftAux input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ℕ × ℕ)
  have hlt : PrimrecPred fun input : X => input.2.2 < input.1 :=
    Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact Primrec.ite hlt (Primrec.snd.comp Primrec.snd) <|
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)

theorem pell_primrec : Primrec pell := by
  have hfirst : Primrec fun r : ℕ => ((SignedCode.one, r), r) :=
    Primrec.pair (Primrec.pair (Primrec.const SignedCode.one) Primrec.id) Primrec.id
  have hnext : Primrec fun r : ℕ => r + 1 := Primrec.succ
  have hsecond : Primrec fun r : ℕ =>
      (((0, 3), r + 1), r + 1) :=
    Primrec.pair (Primrec.pair (Primrec.const ((0, 3) : SignedCode)) hnext) hnext
  have hquad : Primrec fun r : ℕ =>
      [((SignedCode.one, r), r), (((0, 3), r + 1), r + 1)] :=
    Primrec.list_cons.comp hfirst <|
      Primrec.list_cons.comp hsecond (Primrec.const [])
  exact Primrec.pair hquad <| Primrec.pair (Primrec.const []) (Primrec.const ((0, 1) : SignedCode))

theorem squares_primrec : Primrec squares := by
  have holdTerm : Primrec₂ fun (_ : ℕ) (i : ℕ) => ((SignedCode.one, i), i) :=
    (Primrec.pair (Primrec.pair (Primrec.const SignedCode.one) Primrec.snd)
      Primrec.snd).to₂
  have hold : Primrec fun r : ℕ =>
      (List.range r).map fun i => ((SignedCode.one, i), i) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.id) holdTerm
  have hnewIndex : Primrec₂ fun (r j : ℕ) => r + 2 + j :=
    Primrec.nat_add.comp₂
      (Primrec.nat_add.comp₂ Primrec₂.left (Primrec.const 2).to₂)
      Primrec₂.right
  have hnewTerm : Primrec₂ fun (r j : ℕ) =>
      ((SignedCode.one, r + 2 + j), r + 2 + j) :=
    Primrec₂.pair.comp₂
      (Primrec₂.pair.comp₂ (Primrec.const SignedCode.one).to₂ hnewIndex)
      hnewIndex
  have hnew : Primrec fun r : ℕ =>
      (List.range 4).map fun j => ((SignedCode.one, r + 2 + j), r + 2 + j) :=
    Primrec.list_map (Primrec.const (List.range 4)) hnewTerm
  have hquad : Primrec fun r : ℕ =>
      ((List.range r).map fun i => ((SignedCode.one, i), i)) ++
        ((List.range 4).map fun j => ((SignedCode.one, r + 2 + j), r + 2 + j)) :=
    Primrec.list_append.comp hold hnew
  have hlinTerm : Primrec fun r : ℕ => (SignedCode.neg SignedCode.one, r) :=
    Primrec.pair (Primrec.const (SignedCode.neg SignedCode.one)) Primrec.id
  exact Primrec.pair hquad <| Primrec.pair
    (Primrec.list_cons.comp hlinTerm (Primrec.const []))
    (Primrec.const SignedCode.zero)

end EquationCode

namespace ProgramCode

theorem const_primrec : Primrec fun input : ℕ × SignedCode =>
    const input.1 input.2 := by
  have hgate : Primrec fun input : ℕ × SignedCode =>
      EquationCode.eqConst input.1 input.2 := EquationCode.eqConst_primrec
  exact Primrec.pair (Primrec.const 1) <| Primrec.pair
    (Primrec.list_cons.comp hgate (Primrec.const [])) Primrec.fst

theorem var_primrec : Primrec fun input : ℕ × ℕ => var input.1 input.2 := by
  have hgate : Primrec fun input : ℕ × ℕ =>
      EquationCode.eqCopy input.1 input.2 := EquationCode.eqCopy_primrec
  exact Primrec.pair (Primrec.const 1) <| Primrec.pair
    (Primrec.list_cons.comp hgate (Primrec.const [])) Primrec.fst

set_option maxHeartbeats 800000 in
theorem binary_primrec (gate : ℕ → ℕ → ℕ → EquationCode)
    (hgate : Primrec fun input : ℕ × (ℕ × ℕ) =>
      gate input.1 input.2.1 input.2.2) :
    Primrec fun input : ℕ × (ProgramCode × ProgramCode) =>
      binary gate input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ProgramCode × ProgramCode)
  have hleftK : Primrec fun input : X => input.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hrightK : Primrec fun input : X => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleftGates : Primrec fun input : X => input.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hrightGates : Primrec fun input : X => input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hleftOut : Primrec fun input : X => input.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hrightOut : Primrec fun input : X => input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hshift : Primrec₂ fun (input : X) (i : ℕ) =>
      EquationCode.shiftAux input.1 input.2.1.1 i := by
    have hlt : PrimrecPred fun input : X × ℕ => input.2 < input.1.1 :=
      Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst)
    have hidentity : Primrec fun input : X × ℕ => input.2 := Primrec.snd
    have htranslated : Primrec fun input : X × ℕ => input.2 + input.1.2.1.1 :=
      Primrec.nat_add.comp Primrec.snd <|
        Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.ite hlt hidentity htranslated).to₂
  have hrenamedRight : Primrec fun input : X =>
      input.2.2.2.1.map
        (EquationCode.rename (EquationCode.shiftAux input.1 input.2.1.1)) :=
    Primrec.list_map hrightGates (EquationCode.rename_primrec hshift).to₂
  have hout : Primrec fun input : X => input.1 + input.2.1.1 + input.2.2.1 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst hleftK) hrightK
  have hshiftedRightOut : Primrec fun input : X =>
      EquationCode.shiftAux input.1 input.2.1.1 input.2.2.2.2 := by
    have hlt : PrimrecPred fun input : X => input.2.2.2.2 < input.1 :=
      Primrec.nat_lt.comp hrightOut Primrec.fst
    exact Primrec.ite hlt hrightOut (Primrec.nat_add.comp hrightOut hleftK)
  have hlastGate : Primrec fun input : X =>
      gate (input.1 + input.2.1.1 + input.2.2.1) input.2.1.2.2
        (EquationCode.shiftAux input.1 input.2.1.1 input.2.2.2.2) :=
    hgate.comp <| Primrec.pair hout <| Primrec.pair hleftOut hshiftedRightOut
  have hprefix : Primrec fun input : X =>
      input.2.1.2.1 ++
        input.2.2.2.1.map
          (EquationCode.rename (EquationCode.shiftAux input.1 input.2.1.1)) :=
    Primrec.list_append.comp hleftGates hrenamedRight
  have hgates : Primrec fun input : X =>
      input.2.1.2.1 ++
        input.2.2.2.1.map
          (EquationCode.rename (EquationCode.shiftAux input.1 input.2.1.1)) ++
        [gate (input.1 + input.2.1.1 + input.2.2.1) input.2.1.2.2
          (EquationCode.shiftAux input.1 input.2.1.1 input.2.2.2.2)] :=
    Primrec.list_append.comp hprefix <|
      Primrec.list_cons.comp hlastGate (Primrec.const [])
  have hk : Primrec fun input : X => input.2.1.1 + input.2.2.1 + 1 :=
    Primrec.succ.comp (Primrec.nat_add.comp hleftK hrightK)
  exact (Primrec.pair hk (Primrec.pair hgates hout)).of_eq fun input => by
    simp [binary]

theorem add_primrec : Primrec fun input : ℕ × (ProgramCode × ProgramCode) =>
    add input.1 input.2.1 input.2.2 := by
  simpa only [add] using binary_primrec EquationCode.eqAdd EquationCode.eqAdd_primrec

theorem mul_primrec : Primrec fun input : ℕ × (ProgramCode × ProgramCode) =>
    mul input.1 input.2.1 input.2.2 := by
  simpa only [mul] using binary_primrec EquationCode.eqMul EquationCode.eqMul_primrec

theorem scale_primrec : Primrec fun input : ℕ × (SignedCode × ProgramCode) =>
    scale input.1 input.2.1 input.2.2 := by
  let X := ℕ × (SignedCode × ProgramCode)
  have hk : Primrec fun input : X => input.2.2.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hout : Primrec fun input : X => input.1 + input.2.2.1 :=
    Primrec.nat_add.comp Primrec.fst
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hgate : Primrec fun input : X =>
      EquationCode.eqScale (input.1 + input.2.2.1) input.2.1 input.2.2.2.2 :=
    EquationCode.eqScale_primrec.comp <| Primrec.pair hout <| Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hgates : Primrec fun input : X =>
      input.2.2.2.1 ++
        [EquationCode.eqScale (input.1 + input.2.2.1) input.2.1 input.2.2.2.2] :=
    Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_cons.comp hgate (Primrec.const []))
  exact (Primrec.pair hk (Primrec.pair hgates hout)).of_eq fun input => by
    simp [scale]

theorem mulVar_primrec : Primrec fun input : ℕ × (ProgramCode × ℕ) =>
    mulVar input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ProgramCode × ℕ)
  have hk : Primrec fun input : X => input.2.1.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hout : Primrec fun input : X => input.1 + input.2.1.1 :=
    Primrec.nat_add.comp Primrec.fst
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hgate : Primrec fun input : X =>
      EquationCode.eqMul (input.1 + input.2.1.1) input.2.1.2.2 input.2.2 :=
    EquationCode.eqMul_primrec.comp <| Primrec.pair hout <| Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have hgates : Primrec fun input : X =>
      input.2.1.2.1 ++
        [EquationCode.eqMul (input.1 + input.2.1.1) input.2.1.2.2 input.2.2] :=
    Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.list_cons.comp hgate (Primrec.const []))
  exact (Primrec.pair hk (Primrec.pair hgates hout)).of_eq fun input => by
    simp [mulVar]

theorem iterateMulVarStep_primrec : Primrec iterateMulVarStep := by
  have hn : Primrec fun input : ℕ × (ℕ × ProgramCode) => input.1 := Primrec.fst
  have hi : Primrec fun input : ℕ × (ℕ × ProgramCode) => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hprogram : Primrec fun input : ℕ × (ℕ × ProgramCode) => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  exact (mulVar_primrec.comp (Primrec.pair hn (Primrec.pair hprogram hi))).of_eq
    fun _ => rfl

theorem iterateMulVar_primrec : Primrec fun input : ℕ × (ℕ × (ℕ × ProgramCode)) =>
    iterateMulVar input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  let X := ℕ × (ℕ × (ℕ × ProgramCode))
  have hstep : Primrec₂ fun (input : X) (stepResult : ℕ × ProgramCode) =>
      iterateMulVarStep (input.1, input.2.1, stepResult.2) := by
    have hinput : Primrec₂ fun (input : X) (stepResult : ℕ × ProgramCode) =>
        (input.1, input.2.1, stepResult.2) :=
      Primrec₂.pair.comp₂ (Primrec.fst.comp₂ Primrec₂.left) <|
        Primrec₂.pair.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          (Primrec.snd.comp₂ Primrec₂.right)
    exact iterateMulVarStep_primrec.comp₂ hinput
  exact (Primrec.nat_rec'
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hstep).of_eq fun input => by
      induction input.2.2.1 with
      | zero => rfl
      | succ k ih => simp [iterateMulVar, ih]

set_option maxHeartbeats 800000 in
theorem pow_primrec : Primrec fun input : ℕ × (ℕ × ℕ) =>
    pow input.1 input.2.1 input.2.2 := by
  let X := ℕ × (ℕ × ℕ)
  have hbase : Primrec fun input : X => const input.1 SignedCode.one :=
    const_primrec.comp (Primrec.pair Primrec.fst (Primrec.const SignedCode.one))
  have hzero : PrimrecPred fun stepResult : X × (ℕ × ProgramCode) =>
      stepResult.2.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hvar : Primrec fun stepResult : X × (ℕ × ProgramCode) =>
      var stepResult.1.1 stepResult.1.2.1 :=
    var_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hmulVar : Primrec fun stepResult : X × (ℕ × ProgramCode) =>
      mulVar stepResult.1.1 stepResult.2.2 stepResult.1.2.1 :=
    mulVar_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
      Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hstep : Primrec₂ fun (input : X) (stepResult : ℕ × ProgramCode) =>
      if stepResult.1 = 0 then var input.1 input.2.1
      else mulVar input.1 stepResult.2 input.2.1 :=
    (Primrec.ite hzero hvar hmulVar).to₂
  exact (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd) hbase hstep).of_eq fun input => by
    induction input.2.2 with
    | zero => rfl
    | succ k ih => simp [pow, ih]

set_option maxHeartbeats 800000 in
theorem monomialAux_primrec : Primrec fun input : ℕ × (List ℕ × List ℕ) =>
    monomialAux input.1 input.2.1 input.2.2 := by
  let X := ℕ × (List ℕ × List ℕ)
  let Z := X × (ℕ × Option ProgramCode)
  have hget : Primrec fun input : Z => input.1.2.1.getD input.2.1 0 :=
    Primrec.list_getD 0 |>.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have hzero : PrimrecPred fun input : Z => input.1.2.1.getD input.2.1 0 = 0 :=
    Primrec.eq.comp hget (Primrec.const 0)
  have hpow : Primrec fun input : Z =>
      pow input.1.1 input.2.1 (input.1.2.1.getD input.2.1 0) :=
    pow_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
      Primrec.pair (Primrec.fst.comp Primrec.snd) hget
  have hnone : Primrec fun input : Z =>
      if input.1.2.1.getD input.2.1 0 = 0 then none
      else some (pow input.1.1 input.2.1 (input.1.2.1.getD input.2.1 0)) :=
    Primrec.ite hzero (Primrec.const none) (Primrec.option_some.comp hpow)
  have hsome : Primrec₂ fun (input : Z) (program : ProgramCode) =>
      some (iterateMulVar input.1.1 input.2.1
        (input.1.2.1.getD input.2.1 0) program) := by
    have hiterateInput : Primrec₂ fun (input : Z) (program : ProgramCode) =>
        (input.1.1,
          (input.2.1, (input.1.2.1.getD input.2.1 0, program))) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left) <|
        Primrec₂.pair.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) <|
          Primrec₂.pair.comp₂ (hget.comp₂ Primrec₂.left) Primrec₂.right
    exact Primrec.option_some.comp₂ (iterateMulVar_primrec.comp₂ hiterateInput)
  have hstep : Primrec₂ fun (input : X) (termResult : ℕ × Option ProgramCode) =>
      match termResult.2 with
      | none =>
          if input.2.1.getD termResult.1 0 = 0 then none
          else some (pow input.1 termResult.1 (input.2.1.getD termResult.1 0))
      | some program =>
          some (iterateMulVar input.1 termResult.1
            (input.2.1.getD termResult.1 0) program) := by
    exact (Primrec.option_casesOn
      (Primrec.snd.comp Primrec.snd) hnone hsome).to₂.of_eq fun _ termResult => by
        cases termResult.2 <;> rfl
  exact (Primrec.list_foldr
    (Primrec.snd.comp Primrec.snd) (Primrec.const none) hstep).of_eq fun input => by
      rfl

theorem monomial_primrec : Primrec fun input : ℕ × List ℕ =>
    monomial input.1 input.2 := by
  have haux : Primrec fun input : ℕ × List ℕ =>
      monomialAux input.1 input.2 (List.range input.1) :=
    monomialAux_primrec.comp <| Primrec.pair Primrec.fst <|
      Primrec.pair Primrec.snd (Primrec.list_range.comp Primrec.fst)
  have hdefault : Primrec fun input : ℕ × List ℕ =>
      const input.1 SignedCode.one :=
    const_primrec.comp <| Primrec.pair Primrec.fst (Primrec.const SignedCode.one)
  exact (Primrec.option_getD.comp haux hdefault).of_eq fun _ => rfl

theorem termProgram_primrec : Primrec fun input : ℕ × (List ℕ × ℤ) =>
    termProgram input.1 input.2 := by
  have hcoefficient : Primrec fun input : ℕ × (List ℕ × ℤ) =>
      SignedCode.ofInt input.2.2 :=
    SignedCode.ofInt_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hmonomial : Primrec fun input : ℕ × (List ℕ × ℤ) =>
      monomial input.1 input.2.1 :=
    monomial_primrec.comp <| Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  exact scale_primrec.comp <| Primrec.pair Primrec.fst <|
    Primrec.pair hcoefficient hmonomial

set_option maxHeartbeats 800000 in
theorem ofPolynomialAux_primrec : Primrec fun input : ℕ × List (List ℕ × ℤ) =>
    ofPolynomialAux input.1 input.2 := by
  let X := ℕ × List (List ℕ × ℤ)
  let Z := X × ((List ℕ × ℤ) × Option ProgramCode)
  have hterm : Primrec fun input : Z => termProgram input.1.1 input.2.1 :=
    termProgram_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hnone : Primrec fun input : Z => some (termProgram input.1.1 input.2.1) :=
    Primrec.option_some.comp hterm
  have hsome : Primrec₂ fun (input : Z) (program : ProgramCode) =>
      some (add input.1.1 (termProgram input.1.1 input.2.1) program) := by
    have haddInput : Primrec₂ fun (input : Z) (program : ProgramCode) =>
        (input.1.1, (termProgram input.1.1 input.2.1, program)) :=
      Primrec₂.pair.comp₂
        ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left) <|
        Primrec₂.pair.comp₂ (hterm.comp₂ Primrec₂.left) Primrec₂.right
    exact Primrec.option_some.comp₂ (add_primrec.comp₂ haddInput)
  have hstep : Primrec₂ fun (input : X)
      (termResult : (List ℕ × ℤ) × Option ProgramCode) =>
      some (match termResult.2 with
        | none => termProgram input.1 termResult.1
        | some program => add input.1 (termProgram input.1 termResult.1) program) := by
    exact (Primrec.option_casesOn
      (Primrec.snd.comp Primrec.snd) hnone hsome).to₂.of_eq fun _ termResult => by
        cases termResult.2 <;> rfl
  exact (Primrec.list_foldr Primrec.snd (Primrec.const none) hstep).of_eq
    fun input => rfl

theorem ofPolynomial_primrec : Primrec fun input : ℕ × List (List ℕ × ℤ) =>
    ofPolynomial input.1 input.2 := by
  have hdefault : Primrec fun input : ℕ × List (List ℕ × ℤ) =>
      const input.1 SignedCode.zero :=
    const_primrec.comp <| Primrec.pair Primrec.fst (Primrec.const SignedCode.zero)
  exact (Primrec.option_getD.comp ofPolynomialAux_primrec hdefault).of_eq fun _ => rfl

theorem degreeTwoSystem_primrec : Primrec fun input : ℕ × List (List ℕ × ℤ) =>
    degreeTwoSystem input.1 input.2 := by
  let X := ℕ × List (List ℕ × ℤ)
  have hprogram : Primrec fun input : X => ofPolynomial input.1 input.2 :=
    ofPolynomial_primrec
  have harity : Primrec fun input : X => input.1 + (ofPolynomial input.1 input.2).1 :=
    Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp hprogram)
  have hzero : Primrec fun input : X =>
      EquationCode.eqZero (ofPolynomial input.1 input.2).2.2 :=
    EquationCode.eqZero_primrec.comp (Primrec.snd.comp (Primrec.snd.comp hprogram))
  have hgates : Primrec fun input : X =>
      (ofPolynomial input.1 input.2).2.1 ++
        [EquationCode.eqZero (ofPolynomial input.1 input.2).2.2] :=
    Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp hprogram)) <|
      Primrec.list_cons.comp hzero (Primrec.const [])
  exact (Primrec.pair harity hgates).of_eq fun input => by simp [degreeTwoSystem]

theorem guardedSystem_primrec : Primrec fun input : ℕ × List (List ℕ × ℤ) =>
    guardedSystem input.1 input.2 := by
  let X := ℕ × List (List ℕ × ℤ)
  have hsystem : Primrec fun input : X => degreeTwoSystem input.1 input.2 :=
    degreeTwoSystem_primrec
  have hr : Primrec fun input : X => (degreeTwoSystem input.1 input.2).1 :=
    Primrec.fst.comp hsystem
  have harity : Primrec fun input : X => (degreeTwoSystem input.1 input.2).1 + 6 :=
    Primrec.nat_add.comp hr (Primrec.const 6)
  have hpell : Primrec fun input : X =>
      EquationCode.pell (degreeTwoSystem input.1 input.2).1 :=
    EquationCode.pell_primrec.comp hr
  have hsquares : Primrec fun input : X =>
      EquationCode.squares (degreeTwoSystem input.1 input.2).1 :=
    EquationCode.squares_primrec.comp hr
  have hextra : Primrec fun input : X =>
      [EquationCode.pell (degreeTwoSystem input.1 input.2).1,
        EquationCode.squares (degreeTwoSystem input.1 input.2).1] :=
    Primrec.list_cons.comp hpell <|
      Primrec.list_cons.comp hsquares (Primrec.const [])
  have hgates : Primrec fun input : X =>
      (degreeTwoSystem input.1 input.2).2 ++
        [EquationCode.pell (degreeTwoSystem input.1 input.2).1,
          EquationCode.squares (degreeTwoSystem input.1 input.2).1] :=
    Primrec.list_append.comp (Primrec.snd.comp hsystem) hextra
  exact (Primrec.pair harity hgates).of_eq fun input => by simp [guardedSystem]

end ProgramCode

namespace HomogenizedCode

theorem symEntry_primrec : Primrec fun input :
    RationalCode × (ℕ × (ℕ × (ℕ × ℕ))) =>
    symEntry input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2 := by
  let X := RationalCode × (ℕ × (ℕ × (ℕ × ℕ)))
  have hhalf : Primrec fun input : X => RationalCode.div input.1 RationalCode.two :=
    RationalCode.div_primrec.comp Primrec.fst (Primrec.const RationalCode.two)
  have hfirstCondition : PrimrecPred fun input : X =>
      input.2.2.2.1 = input.2.1 ∧ input.2.2.2.2 = input.2.2.1 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp Primrec.snd)).and <|
      Primrec.eq.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsecondCondition : PrimrecPred fun input : X =>
      input.2.2.2.1 = input.2.2.1 ∧ input.2.2.2.2 = input.2.1 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).and <|
      Primrec.eq.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.snd)
  have hfirst : Primrec fun input : X =>
      if input.2.2.2.1 = input.2.1 ∧ input.2.2.2.2 = input.2.2.1 then
        RationalCode.div input.1 RationalCode.two else RationalCode.zero :=
    Primrec.ite hfirstCondition hhalf (Primrec.const RationalCode.zero)
  have hsecond : Primrec fun input : X =>
      if input.2.2.2.1 = input.2.2.1 ∧ input.2.2.2.2 = input.2.1 then
        RationalCode.div input.1 RationalCode.two else RationalCode.zero :=
    Primrec.ite hsecondCondition hhalf (Primrec.const RationalCode.zero)
  exact (RationalCode.add_primrec.comp hfirst hsecond).of_eq fun input => by
    simp [symEntry]

set_option maxHeartbeats 800000 in
theorem matrixEntry_comp_primrec {α : Type*} [Primcodable α]
    {F : α → EquationCode} {i j : α → ℕ}
    (hF : Primrec F) (hi : Primrec i) (hj : Primrec j) :
    Primrec fun input => matrixEntry (F input) (i input) (j input) := by
  have hquadTerm : Primrec₂ fun (input : α) (term : (SignedCode × ℕ) × ℕ) =>
      symEntry (RationalCode.ofSigned term.1.1) (term.1.2 + 1) (term.2 + 1)
        (i input) (j input) := by
    have hinput : Primrec₂ fun (input : α) (term : (SignedCode × ℕ) × ℕ) =>
        (RationalCode.ofSigned term.1.1,
          (term.1.2 + 1, (term.2 + 1, (i input, j input)))) :=
      Primrec₂.pair.comp₂
        (RationalCode.ofSigned_primrec.comp₂
          ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.right)) <|
        Primrec₂.pair.comp₂
          (Primrec.succ.comp₂ ((Primrec.snd.comp Primrec.fst).comp₂ Primrec₂.right)) <|
        Primrec₂.pair.comp₂ (Primrec.succ.comp₂ (Primrec.snd.comp₂ Primrec₂.right)) <|
        Primrec₂.pair.comp₂
          (hi.comp₂ Primrec₂.left) (hj.comp₂ Primrec₂.left)
    exact symEntry_primrec.comp₂ hinput
  have hlinTerm : Primrec₂ fun (input : α) (term : SignedCode × ℕ) =>
      symEntry (RationalCode.ofSigned term.1) (term.2 + 1) 0
        (i input) (j input) := by
    have hinput : Primrec₂ fun (input : α) (term : SignedCode × ℕ) =>
        (RationalCode.ofSigned term.1,
          (term.2 + 1, (0, (i input, j input)))) :=
      Primrec₂.pair.comp₂
        (RationalCode.ofSigned_primrec.comp₂
          (Primrec.fst.comp₂ Primrec₂.right)) <|
        Primrec₂.pair.comp₂
          (Primrec.succ.comp₂ (Primrec.snd.comp₂ Primrec₂.right)) <|
        Primrec₂.pair.comp₂ (Primrec.const 0).to₂ <|
        Primrec₂.pair.comp₂ (hi.comp₂ Primrec₂.left) (hj.comp₂ Primrec₂.left)
    exact symEntry_primrec.comp₂ hinput
  have hquadList : Primrec fun input : α => (F input).1.map fun term =>
      symEntry (RationalCode.ofSigned term.1.1) (term.1.2 + 1) (term.2 + 1)
        (i input) (j input) :=
    Primrec.list_map (Primrec.fst.comp hF) hquadTerm
  have hlinList : Primrec fun input : α => (F input).2.1.map fun term =>
      symEntry (RationalCode.ofSigned term.1) (term.2 + 1) 0
        (i input) (j input) :=
    Primrec.list_map
      (Primrec.fst.comp (Primrec.snd.comp hF)) hlinTerm
  have hquad : Primrec fun input : α => RationalCode.sum
      ((F input).1.map fun term =>
        symEntry (RationalCode.ofSigned term.1.1) (term.1.2 + 1) (term.2 + 1)
          (i input) (j input)) :=
    RationalCode.sum_primrec.comp hquadList
  have hlin : Primrec fun input : α => RationalCode.sum
      ((F input).2.1.map fun term =>
        symEntry (RationalCode.ofSigned term.1) (term.2 + 1) 0
          (i input) (j input)) :=
    RationalCode.sum_primrec.comp hlinList
  have hconstant : Primrec fun input : α =>
      symEntry (RationalCode.ofSigned (F input).2.2) 0 0 (i input) (j input) :=
    symEntry_primrec.comp <| Primrec.pair
      (RationalCode.ofSigned_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp hF))) <|
      Primrec.pair (Primrec.const 0) <| Primrec.pair (Primrec.const 0) <|
        Primrec.pair hi hj
  exact (RationalCode.add_primrec.comp
    (RationalCode.add_primrec.comp hquad hlin) hconstant).of_eq fun input => by
      simp [matrixEntry]

end HomogenizedCode

namespace BaseAlgebraCode

theorem one_primrec : Primrec one := by
  have hlength : Primrec fun N : ℕ => 5 + N :=
    Primrec.nat_add.comp (Primrec.const 5) Primrec.id
  have hcoordinate : Primrec₂ fun (_ : ℕ) (i : ℕ) =>
      if i = 0 then RationalCode.one else RationalCode.zero := by
    have hzero : PrimrecPred fun input : ℕ × ℕ => input.2 = 0 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
    exact (Primrec.ite hzero (Primrec.const RationalCode.one)
      (Primrec.const RationalCode.zero)).to₂
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

theorem gen_primrec : Primrec fun input : ℕ × ℕ => gen input.1 input.2 := by
  let X := ℕ × ℕ
  let Z := X × ℕ
  have hcaseZero : PrimrecPred fun input : Z =>
      input.1.2 = 0 ∧ input.2 = 1 :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hcaseOne : PrimrecPred fun input : Z =>
      input.1.2 = 1 ∧ input.2 = 1 :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hcaseD : PrimrecPred fun input : Z =>
      2 ≤ input.1.2 ∧ input.2 = input.1.2 + 3 :=
    (Primrec.nat_le.comp (Primrec.const 2)
      (Primrec.snd.comp Primrec.fst)).and <|
      Primrec.eq.comp Primrec.snd <|
        Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 3)
  have hcoordinate : Primrec fun input : Z =>
      if input.1.2 = 0 ∧ input.2 = 1 then RationalCode.one
      else if input.1.2 = 1 ∧ input.2 = 1 then RationalCode.neg RationalCode.one
      else if 2 ≤ input.1.2 ∧ input.2 = input.1.2 + 3 then RationalCode.one
      else RationalCode.zero :=
    Primrec.ite hcaseZero (Primrec.const RationalCode.one) <|
      Primrec.ite hcaseOne (Primrec.const (RationalCode.neg RationalCode.one)) <|
        Primrec.ite hcaseD (Primrec.const RationalCode.one)
          (Primrec.const RationalCode.zero)
  have hlength : Primrec fun input : X => 5 + input.1 :=
    Primrec.nat_add.comp (Primrec.const 5) Primrec.fst
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate.to₂

set_option maxHeartbeats 800000 in
theorem mul_primrec : Primrec fun input : ℕ × (Code × Code) =>
    mul input.1 input.2.1 input.2.2 := by
  let X := ℕ × (Code × Code)
  let Z := X × ℕ
  have hsmallTerm : Primrec₂ fun (input : Z) (i : ℕ) =>
      RationalCode.mul (input.1.2.1.getD i RationalCode.zero)
        (input.1.2.2.getD (input.2 - i) RationalCode.zero) := by
    have hx : Primrec₂ fun (input : Z) (i : ℕ) =>
        input.1.2.1.getD i RationalCode.zero :=
      Primrec.list_getD RationalCode.zero |>.comp₂
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).comp₂ Primrec₂.left)
        Primrec₂.right
    have hy : Primrec₂ fun (input : Z) (i : ℕ) =>
        input.1.2.2.getD (input.2 - i) RationalCode.zero :=
      Primrec.list_getD RationalCode.zero |>.comp₂
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).comp₂ Primrec₂.left)
        (Primrec.nat_sub.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    exact RationalCode.mul_primrec.comp₂ hx hy
  have hsmallList : Primrec fun input : Z =>
      (List.range (input.2 + 1)).map fun i =>
        RationalCode.mul (input.1.2.1.getD i RationalCode.zero)
          (input.1.2.2.getD (input.2 - i) RationalCode.zero) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) hsmallTerm
  have hsmall : Primrec fun input : Z => RationalCode.sum
      ((List.range (input.2 + 1)).map fun i =>
        RationalCode.mul (input.1.2.1.getD i RationalCode.zero)
          (input.1.2.2.getD (input.2 - i) RationalCode.zero)) :=
    RationalCode.sum_primrec.comp hsmallList
  have hxzero : Primrec fun input : Z =>
      input.1.2.1.getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)
  have hyzero : Primrec fun input : Z =>
      input.1.2.2.getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)
  have hxj : Primrec fun input : Z =>
      input.1.2.1.getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hyj : Primrec fun input : Z =>
      input.1.2.2.getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hlarge : Primrec fun input : Z =>
      RationalCode.add
        (RationalCode.mul (input.1.2.1.getD 0 RationalCode.zero)
          (input.1.2.2.getD input.2 RationalCode.zero))
        (RationalCode.mul (input.1.2.2.getD 0 RationalCode.zero)
          (input.1.2.1.getD input.2 RationalCode.zero)) :=
    RationalCode.add_primrec.comp
      (RationalCode.mul_primrec.comp hxzero hyj)
      (RationalCode.mul_primrec.comp hyzero hxj)
  have hcondition : PrimrecPred fun input : Z => input.2 < 5 :=
    Primrec.nat_lt.comp Primrec.snd (Primrec.const 5)
  have hcoordinate : Primrec₂ fun (input : X) (j : ℕ) =>
      if j < 5 then
        RationalCode.sum ((List.range (j + 1)).map fun i =>
          RationalCode.mul (input.2.1.getD i RationalCode.zero)
            (input.2.2.getD (j - i) RationalCode.zero))
      else
        RationalCode.add
          (RationalCode.mul (input.2.1.getD 0 RationalCode.zero)
            (input.2.2.getD j RationalCode.zero))
          (RationalCode.mul (input.2.2.getD 0 RationalCode.zero)
            (input.2.1.getD j RationalCode.zero)) :=
    (Primrec.ite hcondition hsmall hlarge).to₂
  have hlength : Primrec fun input : X => 5 + input.1 :=
    Primrec.nat_add.comp (Primrec.const 5) Primrec.fst
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

theorem powStep_primrec : Primrec powStep := by
  exact mul_primrec.of_eq fun _ => rfl

set_option maxHeartbeats 800000 in
theorem pow_primrec : Primrec fun input : ℕ × (Code × ℕ) =>
    pow input.1 input.2.1 input.2.2 := by
  let X := ℕ × (Code × ℕ)
  have hbase : Primrec fun input : X => one input.1 := one_primrec.comp Primrec.fst
  have hstep : Primrec₂ fun (input : X) (stepResult : ℕ × Code) =>
      powStep (input.1, stepResult.2, input.2.1) := by
    have hinput : Primrec₂ fun (input : X) (stepResult : ℕ × Code) =>
        (input.1, (stepResult.2, input.2.1)) :=
      Primrec₂.pair.comp₂ (Primrec.fst.comp₂ Primrec₂.left) <|
        Primrec₂.pair.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
    exact powStep_primrec.comp₂ hinput
  exact (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd) hbase hstep).of_eq fun input => by
    induction input.2.2 with
    | zero => rfl
    | succ k ih => simp [pow, ih]

set_option maxHeartbeats 800000 in
theorem imageStep_primrec : Primrec imageStep := by
  let X := (ℕ × List ℕ) × (Code × ℕ)
  have hexponent : Primrec fun input : X => input.1.2.getD input.2.2 0 :=
    Primrec.list_getD 0 |>.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hgen : Primrec fun input : X => gen input.1.1 input.2.2 :=
    gen_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hpower : Primrec fun input : X =>
      pow input.1.1 (gen input.1.1 input.2.2)
        (input.1.2.getD input.2.2 0) :=
    pow_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
      Primrec.pair hgen hexponent
  exact (mul_primrec.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
    Primrec.pair (Primrec.fst.comp Primrec.snd) hpower).of_eq fun _ => rfl

theorem image_primrec : Primrec fun input : ℕ × List ℕ => image input.1 input.2 := by
  let X := ℕ × List ℕ
  have hstep : Primrec₂ fun (input : X) (accIndex : Code × ℕ) =>
      imageStep (input, accIndex) := imageStep_primrec.to₂
  have hlength : Primrec fun input : X => 2 + input.1 :=
    Primrec.nat_add.comp (Primrec.const 2) Primrec.fst
  exact (Primrec.list_foldl (Primrec.list_range.comp hlength)
    (one_primrec.comp Primrec.fst) hstep).of_eq fun input => by rfl

end BaseAlgebraCode

namespace MatrixVectorCode

set_option maxHeartbeats 800000 in
theorem matrix_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} (hr : Primrec r) (hF : Primrec F) :
    Primrec fun input => matrix (r input) (F input) := by
  let Y := α × ℕ
  have hentry : Primrec₂ fun (input : Y) (j : ℕ) =>
      HomogenizedCode.matrixEntry (F input.1) input.2 j := by
    have hentry' : Primrec fun input : Y × ℕ =>
        HomogenizedCode.matrixEntry (F input.1.1) input.1.2 input.2 :=
      HomogenizedCode.matrixEntry_comp_primrec
        (hF.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact hentry'.to₂
  have hrow : Primrec₂ fun (input : α) (i : ℕ) =>
      RationalVectorCode.tabulate (r input + 1) fun j =>
        HomogenizedCode.matrixEntry (F input) i j := by
    have hrow' : Primrec fun input : Y =>
        RationalVectorCode.tabulate (r input.1 + 1) fun j =>
          HomogenizedCode.matrixEntry (F input.1) input.2 j :=
      RationalVectorCode.tabulate_primrec
        (Primrec.succ.comp (hr.comp Primrec.fst)) hentry
    exact hrow'.to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp hr)) hrow).of_eq
      fun input => by simp [matrix]

set_option maxHeartbeats 800000 in
theorem polarWithMatrix_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {entries : α → List RationalVectorCode}
    {x y : α → RationalVectorCode} (hr : Primrec r) (hentries : Primrec entries)
    (hx : Primrec x) (hy : Primrec y) :
    Primrec fun input => polarWithMatrix (r input) (entries input) (x input) (y input) := by
  let Y := α × ℕ
  let Z := Y × ℕ
  have hxCoordinate : Primrec fun input : Z =>
      (x input.1.1).getD input.1.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hx.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have hrow : Primrec fun input : Z =>
      (entries input.1.1).getD input.1.2 [] :=
    Primrec.list_getD [] |>.comp
      (hentries.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have hentry : Primrec fun input : Z =>
      ((entries input.1.1).getD input.1.2 []).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp hrow Primrec.snd
  have hyCoordinate : Primrec fun input : Z =>
      (y input.1.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hy.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hterm : Primrec₂ fun (input : Y) (j : ℕ) =>
      RationalCode.mul
        (RationalCode.mul ((x input.1).getD input.2 RationalCode.zero)
          (((entries input.1).getD input.2 []).getD j RationalCode.zero))
        ((y input.1).getD j RationalCode.zero) :=
    (RationalCode.mul_primrec.comp
      (RationalCode.mul_primrec.comp hxCoordinate hentry) hyCoordinate).to₂
  have hinnerList : Primrec fun input : Y =>
      (List.range (r input.1 + 1)).map fun j =>
        RationalCode.mul
          (RationalCode.mul ((x input.1).getD input.2 RationalCode.zero)
            (((entries input.1).getD input.2 []).getD j RationalCode.zero))
          ((y input.1).getD j RationalCode.zero) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp (hr.comp Primrec.fst))) hterm
  have hinner : Primrec₂ fun (input : α) (i : ℕ) =>
      RationalCode.sum ((List.range (r input + 1)).map fun j =>
        RationalCode.mul
          (RationalCode.mul ((x input).getD i RationalCode.zero)
            (((entries input).getD i []).getD j RationalCode.zero))
          ((y input).getD j RationalCode.zero)) :=
    (RationalCode.sum_primrec.comp hinnerList).to₂
  have houterList : Primrec fun input : α =>
      (List.range (r input + 1)).map fun i =>
        RationalCode.sum ((List.range (r input + 1)).map fun j =>
          RationalCode.mul
            (RationalCode.mul ((x input).getD i RationalCode.zero)
              (((entries input).getD i []).getD j RationalCode.zero))
            ((y input).getD j RationalCode.zero)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hr)) hinner
  exact (RationalCode.sum_primrec.comp houterList).of_eq fun input => by
    simp [polarWithMatrix]

set_option maxHeartbeats 800000 in
theorem polar_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode}
    {x y : α → RationalVectorCode} (hr : Primrec r) (hF : Primrec F)
    (hx : Primrec x) (hy : Primrec y) :
    Primrec fun input => polar (r input) (F input) (x input) (y input) := by
  exact (polarWithMatrix_comp_primrec hr (matrix_comp_primrec hr hF) hx hy).of_eq
    fun _ => rfl

set_option maxHeartbeats 800000 in
theorem polar_primrec : Primrec fun input :
    ℕ × (EquationCode × (RationalVectorCode × RationalVectorCode)) =>
    polar input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  exact polar_comp_primrec Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

end MatrixVectorCode

namespace CubeAlgebraCode

theorem one_comp_primrec {α : Type*} [Primcodable α] {r : α → ℕ}
    (hr : Primrec r) : Primrec fun input => one (r input) := by
  have hlength : Primrec fun input : α => r input + 3 :=
    Primrec.nat_add.comp hr (Primrec.const 3)
  have hcoordinate : Primrec₂ fun (_ : α) (j : ℕ) =>
      if j = 0 then RationalCode.one else RationalCode.zero := by
    have hzero : PrimrecPred fun input : α × ℕ => input.2 = 0 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
    exact (Primrec.ite hzero (Primrec.const RationalCode.one)
      (Primrec.const RationalCode.zero)).to₂
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

theorem vectorPart_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {x : α → Code} (hr : Primrec r) (hx : Primrec x) :
    Primrec fun input => vectorPart (r input) (x input) := by
  have hlength : Primrec fun input : α => r input + 1 :=
    Primrec.succ.comp hr
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      (x input).getD (j + 1) RationalCode.zero := by
    exact Primrec.list_getD RationalCode.zero |>.comp₂
      (hx.comp₂ Primrec₂.left) (Primrec.succ.comp₂ Primrec₂.right)
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

set_option maxHeartbeats 800000 in
theorem mul_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} {x y : α → Code}
    (hr : Primrec r) (hF : Primrec F) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun input => mul (r input) (F input) (x input) (y input) := by
  let Y := α × ℕ
  have hxzero : Primrec fun input : Y =>
      (x input.1).getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hx.comp Primrec.fst) (Primrec.const 0)
  have hyzero : Primrec fun input : Y =>
      (y input.1).getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hy.comp Primrec.fst) (Primrec.const 0)
  have hxj : Primrec fun input : Y =>
      (x input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hx.comp Primrec.fst) Primrec.snd
  have hyj : Primrec fun input : Y =>
      (y input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hy.comp Primrec.fst) Primrec.snd
  have hsocleIndex : Primrec fun input : Y => r input.1 + 2 :=
    Primrec.nat_add.comp (hr.comp Primrec.fst) (Primrec.const 2)
  have hxsocle : Primrec fun input : Y =>
      (x input.1).getD (r input.1 + 2) RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hx.comp Primrec.fst) hsocleIndex
  have hysocle : Primrec fun input : Y =>
      (y input.1).getD (r input.1 + 2) RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hy.comp Primrec.fst) hsocleIndex
  have hscalar : Primrec fun input : Y =>
      RationalCode.mul ((x input.1).getD 0 RationalCode.zero)
        ((y input.1).getD 0 RationalCode.zero) :=
    RationalCode.mul_primrec.comp hxzero hyzero
  have hvector : Primrec fun input : Y =>
      RationalCode.add
        (RationalCode.mul ((x input.1).getD 0 RationalCode.zero)
          ((y input.1).getD input.2 RationalCode.zero))
        (RationalCode.mul ((y input.1).getD 0 RationalCode.zero)
          ((x input.1).getD input.2 RationalCode.zero)) :=
    RationalCode.add_primrec.comp
      (RationalCode.mul_primrec.comp hxzero hyj)
      (RationalCode.mul_primrec.comp hyzero hxj)
  have hpolar : Primrec fun input : Y =>
      MatrixVectorCode.polar (r input.1) (F input.1)
        (vectorPart (r input.1) (x input.1))
        (vectorPart (r input.1) (y input.1)) :=
    MatrixVectorCode.polar_comp_primrec
      (hr.comp Primrec.fst) (hF.comp Primrec.fst)
      (vectorPart_comp_primrec (hr.comp Primrec.fst) (hx.comp Primrec.fst))
      (vectorPart_comp_primrec (hr.comp Primrec.fst) (hy.comp Primrec.fst))
  have hsocle : Primrec fun input : Y =>
      RationalCode.add
        (RationalCode.add
          (RationalCode.mul ((x input.1).getD 0 RationalCode.zero)
            ((y input.1).getD (r input.1 + 2) RationalCode.zero))
          (RationalCode.mul ((y input.1).getD 0 RationalCode.zero)
            ((x input.1).getD (r input.1 + 2) RationalCode.zero)))
        (MatrixVectorCode.polar (r input.1) (F input.1)
          (vectorPart (r input.1) (x input.1))
          (vectorPart (r input.1) (y input.1))) :=
    RationalCode.add_primrec.comp
      (RationalCode.add_primrec.comp
        (RationalCode.mul_primrec.comp hxzero hysocle)
        (RationalCode.mul_primrec.comp hyzero hxsocle)) hpolar
  have hzero : PrimrecPred fun input : Y => input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hvectorIndex : PrimrecPred fun input : Y => input.2 < r input.1 + 2 :=
    Primrec.nat_lt.comp Primrec.snd hsocleIndex
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if j = 0 then
        RationalCode.mul ((x input).getD 0 RationalCode.zero)
          ((y input).getD 0 RationalCode.zero)
      else if j < r input + 2 then
        RationalCode.add
          (RationalCode.mul ((x input).getD 0 RationalCode.zero)
            ((y input).getD j RationalCode.zero))
          (RationalCode.mul ((y input).getD 0 RationalCode.zero)
            ((x input).getD j RationalCode.zero))
      else
        RationalCode.add
          (RationalCode.add
            (RationalCode.mul ((x input).getD 0 RationalCode.zero)
              ((y input).getD (r input + 2) RationalCode.zero))
            (RationalCode.mul ((y input).getD 0 RationalCode.zero)
              ((x input).getD (r input + 2) RationalCode.zero)))
          (MatrixVectorCode.polar (r input) (F input)
            (vectorPart (r input) (x input)) (vectorPart (r input) (y input))) :=
    (Primrec.ite hzero hscalar (Primrec.ite hvectorIndex hvector hsocle)).to₂
  have hlength : Primrec fun input : α => r input + 3 :=
    Primrec.nat_add.comp hr (Primrec.const 3)
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

set_option maxHeartbeats 800000 in
theorem pow_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} {x : α → Code} {k : α → ℕ}
    (hr : Primrec r) (hF : Primrec F) (hx : Primrec x) (hk : Primrec k) :
    Primrec fun input => pow (r input) (F input) (x input) (k input) := by
  have hbase : Primrec fun input : α => one (r input) := one_comp_primrec hr
  have hstep : Primrec₂ fun (input : α) (stepResult : ℕ × Code) =>
      mul (r input) (F input) stepResult.2 (x input) := by
    have hstep' : Primrec fun input : α × (ℕ × Code) =>
        mul (r input.1) (F input.1) input.2.2 (x input.1) :=
      mul_comp_primrec (hr.comp Primrec.fst) (hF.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd) (hx.comp Primrec.fst)
    exact hstep'.to₂
  exact (Primrec.nat_rec' hk hbase hstep).of_eq fun input => by
    induction k input with
    | zero => rfl
    | succ k ih => simp [pow, ih]

theorem generatorVector_comp_primrec {α : Type*} [Primcodable α]
    {r i : α → ℕ} (hr : Primrec r) (hi : Primrec i) :
    Primrec fun input => generatorVector (r input) (i input) := by
  let Y := α × ℕ
  have hcaseZero : PrimrecPred fun input : Y =>
      i input.1 = 0 ∧ input.2 = 0 :=
    (Primrec.eq.comp (hi.comp Primrec.fst) (Primrec.const 0)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcaseOne : PrimrecPred fun input : Y =>
      i input.1 = 1 ∧ input.2 = 0 :=
    (Primrec.eq.comp (hi.comp Primrec.fst) (Primrec.const 1)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcaseLater : PrimrecPred fun input : Y =>
      2 ≤ i input.1 ∧ input.2 + 1 = i input.1 :=
    (Primrec.nat_le.comp (Primrec.const 2) (hi.comp Primrec.fst)).and <|
      Primrec.eq.comp (Primrec.succ.comp Primrec.snd) (hi.comp Primrec.fst)
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if i input = 0 ∧ j = 0 then RationalCode.one
      else if i input = 1 ∧ j = 0 then RationalCode.neg RationalCode.one
      else if 2 ≤ i input ∧ j + 1 = i input then RationalCode.one
      else RationalCode.zero :=
    (Primrec.ite hcaseZero (Primrec.const RationalCode.one) <|
      Primrec.ite hcaseOne (Primrec.const (RationalCode.neg RationalCode.one)) <|
        Primrec.ite hcaseLater (Primrec.const RationalCode.one)
          (Primrec.const RationalCode.zero)).to₂
  exact RationalVectorCode.tabulate_primrec (Primrec.succ.comp hr) hcoordinate

set_option maxHeartbeats 800000 in
theorem expMinusOne_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} {v : α → RationalVectorCode}
    (hr : Primrec r) (hF : Primrec F) (hv : Primrec v) :
    Primrec fun input => expMinusOne (r input) (F input) (v input) := by
  let Y := α × ℕ
  have hzero : PrimrecPred fun input : Y => input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hbound : Primrec fun input : Y => r input.1 + 2 :=
    Primrec.nat_add.comp (hr.comp Primrec.fst) (Primrec.const 2)
  have hvectorIndex : PrimrecPred fun input : Y => input.2 < r input.1 + 2 :=
    Primrec.nat_lt.comp Primrec.snd hbound
  have hvector : Primrec fun input : Y =>
      (v input.1).getD (input.2 - 1) RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hv.comp Primrec.fst) <|
      Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hsocle : Primrec fun input : Y =>
      RationalCode.div
        (MatrixVectorCode.polar (r input.1) (F input.1) (v input.1) (v input.1))
        RationalCode.two :=
    RationalCode.div_primrec.comp
      (MatrixVectorCode.polar_comp_primrec
        (hr.comp Primrec.fst) (hF.comp Primrec.fst)
        (hv.comp Primrec.fst) (hv.comp Primrec.fst))
      (Primrec.const RationalCode.two)
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if j = 0 then RationalCode.zero
      else if j < r input + 2 then (v input).getD (j - 1) RationalCode.zero
      else RationalCode.div
        (MatrixVectorCode.polar (r input) (F input) (v input) (v input))
        RationalCode.two :=
    (Primrec.ite hzero (Primrec.const RationalCode.zero)
      (Primrec.ite hvectorIndex hvector hsocle)).to₂
  exact RationalVectorCode.tabulate_primrec
    (Primrec.nat_add.comp hr (Primrec.const 3)) hcoordinate

theorem gen_comp_primrec {α : Type*} [Primcodable α]
    {r i : α → ℕ} {F : α → EquationCode}
    (hr : Primrec r) (hF : Primrec F) (hi : Primrec i) :
    Primrec fun input => gen (r input) (F input) (i input) := by
  exact (expMinusOne_comp_primrec hr hF (generatorVector_comp_primrec hr hi)).of_eq
    fun _ => rfl

set_option maxHeartbeats 800000 in
theorem image_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} {e : α → List ℕ}
    (hr : Primrec r) (hF : Primrec F) (he : Primrec e) :
    Primrec fun input => image (r input) (F input) (e input) := by
  let Y := α × (Code × ℕ)
  have hexponent : Primrec fun input : Y =>
      (e input.1).getD input.2.2 0 :=
    Primrec.list_getD 0 |>.comp (he.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hgen : Primrec fun input : Y =>
      gen (r input.1) (F input.1) input.2.2 :=
    gen_comp_primrec (hr.comp Primrec.fst) (hF.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hpower : Primrec fun input : Y =>
      pow (r input.1) (F input.1)
        (gen (r input.1) (F input.1) input.2.2)
        ((e input.1).getD input.2.2 0) :=
    pow_comp_primrec (hr.comp Primrec.fst) (hF.comp Primrec.fst) hgen hexponent
  have hstep : Primrec₂ fun (input : α) (accIndex : Code × ℕ) =>
      mul (r input) (F input) accIndex.1
        (pow (r input) (F input) (gen (r input) (F input) accIndex.2)
          ((e input).getD accIndex.2 0)) := by
    have hstep' : Primrec fun input : Y =>
        mul (r input.1) (F input.1) input.2.1
          (pow (r input.1) (F input.1)
            (gen (r input.1) (F input.1) input.2.2)
            ((e input.1).getD input.2.2 0)) :=
      mul_comp_primrec (hr.comp Primrec.fst) (hF.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) hpower
    exact hstep'.to₂
  have hindices : Primrec fun input : α => List.range (2 + r input) :=
    Primrec.list_range.comp <| Primrec.nat_add.comp (Primrec.const 2) hr
  exact (Primrec.list_foldl hindices (one_comp_primrec hr) hstep).of_eq
    fun input => by rfl

end CubeAlgebraCode

namespace ExponentCode

/-- A bounded table containing `tuples k d` for every `d ≤ n`.  Carrying the whole
table makes the recursion on `k` first order. -/
def tupleTableBase (n : ℕ) : List (List (List ℕ)) :=
  (List.range (n + 1)).map fun d => if d = 0 then [[]] else []

/-- Extend a bounded table from tuples of length `k` to tuples of length `k + 1`. -/
def tupleTableStep (n : ℕ) (table : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  (List.range (n + 1)).map fun d =>
    (List.Nat.antidiagonal d).flatMap fun ni =>
      (table.getD ni.2 []).map fun tail => ni.1 :: tail

/-- The bounded table used to compute the exponent lists by primitive recursion. -/
def tupleTable (n : ℕ) : ℕ → List (List (List ℕ))
  | 0 => tupleTableBase n
  | k + 1 => tupleTableStep n (tupleTable n k)

theorem antidiagonal_primrec : Primrec List.Nat.antidiagonal := by
  have hterm : Primrec₂ fun (n i : ℕ) => (i, n - i) :=
    Primrec₂.pair.comp₂ Primrec₂.right
      (Primrec.nat_sub.comp₂ Primrec₂.left Primrec₂.right)
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.succ) hterm).of_eq
    fun n => by simp [List.Nat.antidiagonal]

theorem tupleTableBase_primrec : Primrec tupleTableBase := by
  have hzero : PrimrecPred fun input : ℕ × ℕ => input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hentry : Primrec₂ fun (_ : ℕ) (d : ℕ) =>
      if d = 0 then ([[]] : List (List ℕ)) else [] :=
    (Primrec.ite hzero (Primrec.const ([[]] : List (List ℕ)))
      (Primrec.const [])).to₂
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.succ) hentry).of_eq
    fun n => by simp [tupleTableBase]

set_option maxHeartbeats 800000 in
theorem tupleTableStep_primrec : Primrec fun input :
    ℕ × List (List (List ℕ)) => tupleTableStep input.1 input.2 := by
  let X := ℕ × List (List (List ℕ))
  let Y := X × ℕ
  let Z := Y × (ℕ × ℕ)
  have htails : Primrec fun input : Z =>
      input.1.1.2.getD input.2.2 [] :=
    Primrec.list_getD [] |>.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)
  have hcons : Primrec₂ fun (input : Z) (tail : List ℕ) =>
      input.2.1 :: tail :=
    Primrec.list_cons.comp₂
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left) Primrec₂.right
  have htailMap : Primrec₂ fun (input : Y) (ni : ℕ × ℕ) =>
      (input.1.2.getD ni.2 []).map fun tail => ni.1 :: tail := by
    have htailMap' : Primrec fun input : Z =>
        (input.1.1.2.getD input.2.2 []).map fun tail => input.2.1 :: tail :=
      Primrec.list_map htails hcons
    exact htailMap'.to₂
  have hentry : Primrec₂ fun (input : X) (d : ℕ) =>
      (List.Nat.antidiagonal d).flatMap fun ni =>
        (input.2.getD ni.2 []).map fun tail => ni.1 :: tail := by
    have hentry' : Primrec fun input : Y =>
        (List.Nat.antidiagonal input.2).flatMap fun ni =>
          (input.1.2.getD ni.2 []).map fun tail => ni.1 :: tail :=
      Primrec.list_flatMap (antidiagonal_primrec.comp Primrec.snd) htailMap
    exact hentry'.to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) hentry).of_eq
      fun input => by simp [tupleTableStep]

set_option maxHeartbeats 800000 in
theorem tupleTable_primrec : Primrec fun input : ℕ × ℕ =>
    tupleTable input.1 input.2 := by
  have hbase : Primrec fun input : ℕ × ℕ => tupleTableBase input.1 :=
    tupleTableBase_primrec.comp Primrec.fst
  have hstep : Primrec₂ fun (input : ℕ × ℕ)
      (stepResult : ℕ × List (List (List ℕ))) =>
      tupleTableStep input.1 stepResult.2 := by
    have hstep' : Primrec fun input : (ℕ × ℕ) × (ℕ × List (List (List ℕ))) =>
        tupleTableStep input.1.1 input.2.2 :=
      tupleTableStep_primrec.comp <|
        Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd)
    exact hstep'.to₂
  exact (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq fun input => by
    induction input.2 with
    | zero => rfl
    | succ k ih => simp [tupleTable, ih]

theorem tupleTable_length (n k : ℕ) : (tupleTable n k).length = n + 1 := by
  induction k with
  | zero => simp [tupleTable, tupleTableBase]
  | succ k _ => simp [tupleTable, tupleTableStep]

theorem tupleTable_getD {n k d : ℕ} (hd : d < n + 1) :
    (tupleTable n k).getD d [] = tuples k d := by
  induction k generalizing d with
  | zero =>
      rw [tupleTable, tupleTableBase]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getElem_range]
      cases d <;> rfl
  | succ k ih =>
      rw [tupleTable, tupleTableStep]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getElem_range, tuples]
      apply List.flatMap_congr
      intro ni hni
      rw [ih]
      have hsum := List.Nat.mem_antidiagonal.mp hni
      omega

set_option maxHeartbeats 800000 in
theorem tuples_primrec : Primrec fun input : ℕ × ℕ =>
    tuples input.1 input.2 := by
  have htable : Primrec fun input : ℕ × ℕ => tupleTable input.2 input.1 :=
    tupleTable_primrec.comp (Primrec.pair Primrec.snd Primrec.fst)
  exact (Primrec.list_getD ([] : List (List ℕ)) |>.comp htable Primrec.snd).of_eq
    fun input => tupleTable_getD (by omega)

theorem low_primrec : Primrec low := by
  have htuples : Primrec₂ fun (r d : ℕ) => tuples (2 + r) d := by
    exact (tuples_primrec.comp <|
      Primrec.pair
        (Primrec.nat_add.comp (Primrec.const 2) Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_flatMap (Primrec.const (List.range 5)) htuples).of_eq
    fun r => by simp [low]

theorem degreeFive_primrec : Primrec degreeFive := by
  exact tuples_primrec.comp <|
    Primrec.pair (Primrec.nat_add.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 5)

end ExponentCode

namespace BaseAlgebraCode

theorem one_comp_primrec {α : Type*} [Primcodable α] {N : α → ℕ}
    (hN : Primrec N) : Primrec fun input => one (N input) := by
  have hlength : Primrec fun input : α => 5 + N input :=
    Primrec.nat_add.comp (Primrec.const 5) hN
  have hcoordinate : Primrec₂ fun (_ : α) (i : ℕ) =>
      if i = 0 then RationalCode.one else RationalCode.zero := by
    have hzero : PrimrecPred fun input : α × ℕ => input.2 = 0 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
    exact (Primrec.ite hzero (Primrec.const RationalCode.one)
      (Primrec.const RationalCode.zero)).to₂
  exact RationalVectorCode.tabulate_primrec hlength hcoordinate

theorem gen_comp_primrec {α : Type*} [Primcodable α]
    {N i : α → ℕ} (hN : Primrec N) (hi : Primrec i) :
    Primrec fun input => gen (N input) (i input) := by
  let Y := α × ℕ
  have hcaseZero : PrimrecPred fun input : Y =>
      i input.1 = 0 ∧ input.2 = 1 :=
    (Primrec.eq.comp (hi.comp Primrec.fst) (Primrec.const 0)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hcaseOne : PrimrecPred fun input : Y =>
      i input.1 = 1 ∧ input.2 = 1 :=
    (Primrec.eq.comp (hi.comp Primrec.fst) (Primrec.const 1)).and <|
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hcaseD : PrimrecPred fun input : Y =>
      2 ≤ i input.1 ∧ input.2 = i input.1 + 3 :=
    (Primrec.nat_le.comp (Primrec.const 2) (hi.comp Primrec.fst)).and <|
      Primrec.eq.comp Primrec.snd <|
        Primrec.nat_add.comp (hi.comp Primrec.fst) (Primrec.const 3)
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if i input = 0 ∧ j = 1 then RationalCode.one
      else if i input = 1 ∧ j = 1 then RationalCode.neg RationalCode.one
      else if 2 ≤ i input ∧ j = i input + 3 then RationalCode.one
      else RationalCode.zero :=
    (Primrec.ite hcaseZero (Primrec.const RationalCode.one) <|
      Primrec.ite hcaseOne (Primrec.const (RationalCode.neg RationalCode.one)) <|
        Primrec.ite hcaseD (Primrec.const RationalCode.one)
          (Primrec.const RationalCode.zero)).to₂
  exact RationalVectorCode.tabulate_primrec
    (Primrec.nat_add.comp (Primrec.const 5) hN) hcoordinate

set_option maxHeartbeats 800000 in
theorem mul_comp_primrec {α : Type*} [Primcodable α]
    {N : α → ℕ} {x y : α → Code}
    (hN : Primrec N) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun input => mul (N input) (x input) (y input) := by
  let Y := α × ℕ
  let Z := Y × ℕ
  have hxi : Primrec fun input : Z =>
      (x input.1.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hx.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hyji : Primrec fun input : Z =>
      (y input.1.1).getD (input.1.2 - input.2) RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hy.comp (Primrec.fst.comp Primrec.fst)) <|
        Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hsmallTerm : Primrec₂ fun (input : Y) (i : ℕ) =>
      RationalCode.mul ((x input.1).getD i RationalCode.zero)
        ((y input.1).getD (input.2 - i) RationalCode.zero) :=
    (RationalCode.mul_primrec.comp hxi hyji).to₂
  have hsmallList : Primrec fun input : Y =>
      (List.range (input.2 + 1)).map fun i =>
        RationalCode.mul ((x input.1).getD i RationalCode.zero)
          ((y input.1).getD (input.2 - i) RationalCode.zero) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      hsmallTerm
  have hsmall : Primrec fun input : Y => RationalCode.sum
      ((List.range (input.2 + 1)).map fun i =>
        RationalCode.mul ((x input.1).getD i RationalCode.zero)
          ((y input.1).getD (input.2 - i) RationalCode.zero)) :=
    RationalCode.sum_primrec.comp hsmallList
  have hxzero : Primrec fun input : Y =>
      (x input.1).getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hx.comp Primrec.fst) (Primrec.const 0)
  have hyzero : Primrec fun input : Y =>
      (y input.1).getD 0 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hy.comp Primrec.fst) (Primrec.const 0)
  have hxj : Primrec fun input : Y =>
      (x input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hx.comp Primrec.fst) Primrec.snd
  have hyj : Primrec fun input : Y =>
      (y input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hy.comp Primrec.fst) Primrec.snd
  have hlarge : Primrec fun input : Y =>
      RationalCode.add
        (RationalCode.mul ((x input.1).getD 0 RationalCode.zero)
          ((y input.1).getD input.2 RationalCode.zero))
        (RationalCode.mul ((y input.1).getD 0 RationalCode.zero)
          ((x input.1).getD input.2 RationalCode.zero)) :=
    RationalCode.add_primrec.comp
      (RationalCode.mul_primrec.comp hxzero hyj)
      (RationalCode.mul_primrec.comp hyzero hxj)
  have hcondition : PrimrecPred fun input : Y => input.2 < 5 :=
    Primrec.nat_lt.comp Primrec.snd (Primrec.const 5)
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if j < 5 then
        RationalCode.sum ((List.range (j + 1)).map fun i =>
          RationalCode.mul ((x input).getD i RationalCode.zero)
            ((y input).getD (j - i) RationalCode.zero))
      else
        RationalCode.add
          (RationalCode.mul ((x input).getD 0 RationalCode.zero)
            ((y input).getD j RationalCode.zero))
          (RationalCode.mul ((y input).getD 0 RationalCode.zero)
            ((x input).getD j RationalCode.zero)) :=
    (Primrec.ite hcondition hsmall hlarge).to₂
  exact RationalVectorCode.tabulate_primrec
    (Primrec.nat_add.comp (Primrec.const 5) hN) hcoordinate

set_option maxHeartbeats 800000 in
theorem pow_comp_primrec {α : Type*} [Primcodable α]
    {N k : α → ℕ} {x : α → Code}
    (hN : Primrec N) (hx : Primrec x) (hk : Primrec k) :
    Primrec fun input => pow (N input) (x input) (k input) := by
  have hbase : Primrec fun input : α => one (N input) := one_comp_primrec hN
  have hstep : Primrec₂ fun (input : α) (stepResult : ℕ × Code) =>
      mul (N input) stepResult.2 (x input) := by
    have hstep' : Primrec fun input : α × (ℕ × Code) =>
        mul (N input.1) input.2.2 (x input.1) :=
      mul_comp_primrec (hN.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd) (hx.comp Primrec.fst)
    exact hstep'.to₂
  exact (Primrec.nat_rec' hk hbase hstep).of_eq fun input => by
    induction k input with
    | zero => rfl
    | succ k ih => simp [pow, powStep, ih]

set_option maxHeartbeats 800000 in
theorem image_comp_primrec {α : Type*} [Primcodable α]
    {N : α → ℕ} {e : α → List ℕ} (hN : Primrec N) (he : Primrec e) :
    Primrec fun input => image (N input) (e input) := by
  let Y := α × (Code × ℕ)
  have hexponent : Primrec fun input : Y =>
      (e input.1).getD input.2.2 0 :=
    Primrec.list_getD 0 |>.comp (he.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hgen : Primrec fun input : Y => gen (N input.1) input.2.2 :=
    gen_comp_primrec (hN.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hpower : Primrec fun input : Y =>
      pow (N input.1) (gen (N input.1) input.2.2)
        ((e input.1).getD input.2.2 0) :=
    pow_comp_primrec (hN.comp Primrec.fst) hgen hexponent
  have hstep : Primrec₂ fun (input : α) (accIndex : Code × ℕ) =>
      mul (N input) accIndex.1
        (pow (N input) (gen (N input) accIndex.2)
          ((e input).getD accIndex.2 0)) := by
    have hstep' : Primrec fun input : Y =>
        mul (N input.1) input.2.1
          (pow (N input.1) (gen (N input.1) input.2.2)
            ((e input.1).getD input.2.2 0)) :=
      mul_comp_primrec (hN.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) hpower
    exact hstep'.to₂
  have hindices : Primrec fun input : α => List.range (2 + N input) :=
    Primrec.list_range.comp <|
      Primrec.nat_add.comp (Primrec.const 2) hN
  exact (Primrec.list_foldl hindices (one_comp_primrec hN) hstep).of_eq
    fun input => by rfl

end BaseAlgebraCode

namespace RowsCode

set_option maxHeartbeats 800000 in
theorem baseRow_comp_primrec {α : Type*} [Primcodable α]
    {r coordinate : α → ℕ} (hr : Primrec r) (hcoordinate : Primrec coordinate) :
    Primrec fun input => baseRow (r input) (coordinate input) := by
  let Y := α × List ℕ
  have himage : Primrec fun input : Y =>
      BaseAlgebraCode.image (r input.1) input.2 :=
    BaseAlgebraCode.image_comp_primrec (hr.comp Primrec.fst) Primrec.snd
  have hentry : Primrec₂ fun (input : α) (e : List ℕ) =>
      (BaseAlgebraCode.image (r input) e).getD
        (coordinate input) RationalCode.zero := by
    have hentry' : Primrec fun input : Y =>
        (BaseAlgebraCode.image (r input.1) input.2).getD
          (coordinate input.1) RationalCode.zero :=
      Primrec.list_getD RationalCode.zero |>.comp himage
        (hcoordinate.comp Primrec.fst)
    exact hentry'.to₂
  exact (Primrec.list_map (ExponentCode.low_primrec.comp hr) hentry).of_eq
    fun input => by simp [baseRow]

set_option maxHeartbeats 800000 in
theorem baseRows_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} (hr : Primrec r) :
    Primrec fun input => baseRows (r input) := by
  have hfirstRow : Primrec₂ fun (input : α) (coordinate : ℕ) =>
      baseRow (r input) coordinate := by
    have hfirstRow' : Primrec fun input : α × ℕ =>
        baseRow (r input.1) input.2 :=
      baseRow_comp_primrec (hr.comp Primrec.fst) Primrec.snd
    exact hfirstRow'.to₂
  have hfirst : Primrec fun input : α =>
      (List.range 5).map (baseRow (r input)) :=
    Primrec.list_map (Primrec.const (List.range 5)) hfirstRow
  have hsecondRow : Primrec₂ fun (input : α) (i : ℕ) =>
      baseRow (r input) (5 + i) := by
    have hsecondRow' : Primrec fun input : α × ℕ =>
        baseRow (r input.1) (5 + input.2) :=
      baseRow_comp_primrec (hr.comp Primrec.fst) <|
        Primrec.nat_add.comp (Primrec.const 5) Primrec.snd
    exact hsecondRow'.to₂
  have hsecond : Primrec fun input : α =>
      (List.range (r input)).map fun i => baseRow (r input) (5 + i) :=
    Primrec.list_map (Primrec.list_range.comp hr) hsecondRow
  exact (Primrec.list_append.comp hfirst hsecond).of_eq fun input => by
    simp [baseRows]

set_option maxHeartbeats 800000 in
theorem cubeRow_comp_primrec {α : Type*} [Primcodable α]
    {r coordinate : α → ℕ} {F : α → EquationCode}
    (hr : Primrec r) (hF : Primrec F) (hcoordinate : Primrec coordinate) :
    Primrec fun input => cubeRow (r input) (F input) (coordinate input) := by
  let Y := α × List ℕ
  have himage : Primrec fun input : Y =>
      CubeAlgebraCode.image (r input.1) (F input.1) input.2 :=
    CubeAlgebraCode.image_comp_primrec (hr.comp Primrec.fst)
      (hF.comp Primrec.fst) Primrec.snd
  have hentry : Primrec₂ fun (input : α) (e : List ℕ) =>
      (CubeAlgebraCode.image (r input) (F input) e).getD
        (coordinate input) RationalCode.zero := by
    have hentry' : Primrec fun input : Y =>
        (CubeAlgebraCode.image (r input.1) (F input.1) input.2).getD
          (coordinate input.1) RationalCode.zero :=
      Primrec.list_getD RationalCode.zero |>.comp himage
        (hcoordinate.comp Primrec.fst)
    exact hentry'.to₂
  exact (Primrec.list_map (ExponentCode.low_primrec.comp hr) hentry).of_eq
    fun input => by simp [cubeRow]

set_option maxHeartbeats 800000 in
theorem cubeRows_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {F : α → EquationCode} (hr : Primrec r) (hF : Primrec F) :
    Primrec fun input => cubeRows (r input) (F input) := by
  have hzero : Primrec fun input : α => cubeRow (r input) (F input) 0 :=
    cubeRow_comp_primrec hr hF (Primrec.const 0)
  have hone : Primrec fun input : α => cubeRow (r input) (F input) 1 :=
    cubeRow_comp_primrec hr hF (Primrec.const 1)
  have hfirst : Primrec fun input : α =>
      [cubeRow (r input) (F input) 0, cubeRow (r input) (F input) 1] :=
    Primrec.list_cons.comp hzero <|
      Primrec.list_cons.comp hone (Primrec.const [])
  have hmiddleRow : Primrec₂ fun (input : α) (i : ℕ) =>
      cubeRow (r input) (F input) (i + 2) := by
    have hmiddleRow' : Primrec fun input : α × ℕ =>
        cubeRow (r input.1) (F input.1) (input.2 + 2) :=
      cubeRow_comp_primrec (hr.comp Primrec.fst) (hF.comp Primrec.fst) <|
        Primrec.nat_add.comp Primrec.snd (Primrec.const 2)
    exact hmiddleRow'.to₂
  have hmiddle : Primrec fun input : α =>
      (List.range (r input)).map fun i => cubeRow (r input) (F input) (i + 2) :=
    Primrec.list_map (Primrec.list_range.comp hr) hmiddleRow
  have hsocle : Primrec fun input : α =>
      cubeRow (r input) (F input) (r input + 2) :=
    cubeRow_comp_primrec hr hF <|
      Primrec.nat_add.comp hr (Primrec.const 2)
  have hlast : Primrec fun input : α =>
      [cubeRow (r input) (F input) (r input + 2)] :=
    Primrec.list_cons.comp hsocle (Primrec.const [])
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp hfirst hmiddle) hlast).of_eq fun input => by
      simp [cubeRows]

set_option maxHeartbeats 800000 in
theorem rows_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {equations : α → List EquationCode}
    (hr : Primrec r) (hequations : Primrec equations) :
    Primrec fun input => rows (r input) (equations input) := by
  have hcubes : Primrec₂ fun (input : α) (F : EquationCode) =>
      cubeRows (r input) F := by
    have hcubes' : Primrec fun input : α × EquationCode =>
        cubeRows (r input.1) input.2 :=
      cubeRows_comp_primrec (hr.comp Primrec.fst) Primrec.snd
    exact hcubes'.to₂
  have hcubeRows : Primrec fun input : α =>
      (equations input).flatMap (cubeRows (r input)) :=
    Primrec.list_flatMap hequations hcubes
  exact (Primrec.list_append.comp (baseRows_comp_primrec hr) hcubeRows).of_eq
    fun input => by simp [rows]

end RowsCode

namespace KernelCode

set_option maxHeartbeats 800000 in
theorem rowEval_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {row vector : α → RationalVectorCode}
    (hn : Primrec n) (hrow : Primrec row) (hvector : Primrec vector) :
    Primrec fun input => rowEval (n input) (row input) (vector input) := by
  let Y := α × ℕ
  have hrowEntry : Primrec fun input : Y =>
      (row input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hrow.comp Primrec.fst) Primrec.snd
  have hvectorEntry : Primrec fun input : Y =>
      (vector input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp
      (hvector.comp Primrec.fst) Primrec.snd
  have hterm : Primrec₂ fun (input : α) (i : ℕ) =>
      RationalCode.mul ((row input).getD i RationalCode.zero)
        ((vector input).getD i RationalCode.zero) :=
    (RationalCode.mul_primrec.comp hrowEntry hvectorEntry).to₂
  have hterms : Primrec fun input : α =>
      (List.range (n input)).map fun i =>
        RationalCode.mul ((row input).getD i RationalCode.zero)
          ((vector input).getD i RationalCode.zero) :=
    Primrec.list_map (Primrec.list_range.comp hn) hterm
  exact (RationalCode.sum_primrec.comp hterms).of_eq fun input => by
    simp [rowEval, RationalVectorCode.dot]

set_option maxHeartbeats 800000 in
theorem standardBasis_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} (hn : Primrec n) :
    Primrec fun input => standardBasis (n input) := by
  let Y := α × ℕ
  have hcoordinate : Primrec₂ fun (input : Y) (j : ℕ) =>
      if input.2 = j then RationalCode.one else RationalCode.zero := by
    have heq : PrimrecPred fun input : Y × ℕ => input.1.2 = input.2 :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (Primrec.ite heq (Primrec.const RationalCode.one)
      (Primrec.const RationalCode.zero)).to₂
  have hvector : Primrec₂ fun (input : α) (i : ℕ) =>
      RationalVectorCode.tabulate (n input) fun j =>
        if i = j then RationalCode.one else RationalCode.zero := by
    have hvector' : Primrec fun input : Y =>
        RationalVectorCode.tabulate (n input.1) fun j =>
          if input.2 = j then RationalCode.one else RationalCode.zero :=
      RationalVectorCode.tabulate_primrec (hn.comp Primrec.fst) hcoordinate
    exact hvector'.to₂
  exact (Primrec.list_map (Primrec.list_range.comp hn) hvector).of_eq
    fun input => by simp [standardBasis]

set_option maxHeartbeats 800000 in
theorem subSmul_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {w v : α → RationalVectorCode} {c : α → RationalCode}
    (hn : Primrec n) (hw : Primrec w) (hv : Primrec v) (hc : Primrec c) :
    Primrec fun input => subSmul (n input) (w input) (v input) (c input) := by
  let Y := α × ℕ
  have hwj : Primrec fun input : Y =>
      (w input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hw.comp Primrec.fst) Primrec.snd
  have hvj : Primrec fun input : Y =>
      (v input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hv.comp Primrec.fst) Primrec.snd
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      RationalCode.sub ((w input).getD j RationalCode.zero)
        (RationalCode.mul (c input) ((v input).getD j RationalCode.zero)) :=
    (RationalCode.sub_primrec.comp hwj
      (RationalCode.mul_primrec.comp (hc.comp Primrec.fst) hvj)).to₂
  exact RationalVectorCode.tabulate_primrec hn hcoordinate

set_option maxHeartbeats 800000 in
theorem eliminate_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {row : α → RationalVectorCode}
    {vectors : α → List RationalVectorCode}
    (hn : Primrec n) (hrow : Primrec row) (hvectors : Primrec vectors) :
    Primrec fun input => eliminate (n input) (row input) (vectors input) := by
  let Z := α × (RationalVectorCode ×
    (List RationalVectorCode × List RationalVectorCode))
  have hpivot : Primrec fun input : Z =>
      rowEval (n input.1) (row input.1) input.2.1 :=
    rowEval_comp_primrec (hn.comp Primrec.fst) (hrow.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hcondition : PrimrecPred fun input : Z =>
      RationalCode.Equivalent
        (rowEval (n input.1) (row input.1) input.2.1) RationalCode.zero :=
    RationalCode.equivalent_primrec.comp hpivot (Primrec.const RationalCode.zero)
  have hkeep : Primrec fun input : Z =>
      input.2.1 :: input.2.2.2 :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) <|
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let W := Z × RationalVectorCode
  have hrowEvalW : Primrec fun input : W =>
      rowEval (n input.1.1) (row input.1.1) input.2 :=
    rowEval_comp_primrec (hn.comp (Primrec.fst.comp Primrec.fst))
      (hrow.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hcoefficient : Primrec fun input : W =>
      RationalCode.div
        (rowEval (n input.1.1) (row input.1.1) input.2)
        (rowEval (n input.1.1) (row input.1.1) input.1.2.1) :=
    RationalCode.div_primrec.comp hrowEvalW (hpivot.comp Primrec.fst)
  have htransform : Primrec₂ fun (input : Z) (w : RationalVectorCode) =>
      subSmul (n input.1) w input.2.1
        (RationalCode.div (rowEval (n input.1) (row input.1) w)
          (rowEval (n input.1) (row input.1) input.2.1)) := by
    have htransform' : Primrec fun input : W =>
        subSmul (n input.1.1) input.2 input.1.2.1
          (RationalCode.div (rowEval (n input.1.1) (row input.1.1) input.2)
            (rowEval (n input.1.1) (row input.1.1) input.1.2.1)) :=
      subSmul_comp_primrec (hn.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        hcoefficient
    exact htransform'.to₂
  have hdrop : Primrec fun input : Z =>
      input.2.2.1.map fun w =>
        subSmul (n input.1) w input.2.1
          (RationalCode.div (rowEval (n input.1) (row input.1) w)
            (rowEval (n input.1) (row input.1) input.2.1)) :=
    Primrec.list_map
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      htransform
  have hstep : Primrec₂ fun (input : α)
      (data : RationalVectorCode ×
        (List RationalVectorCode × List RationalVectorCode)) =>
      if RationalCode.Equivalent (rowEval (n input) (row input) data.1)
          RationalCode.zero then
        data.1 :: data.2.2
      else
        data.2.1.map fun w => subSmul (n input) w data.1
          (RationalCode.div (rowEval (n input) (row input) w)
            (rowEval (n input) (row input) data.1)) :=
    (Primrec.ite hcondition hkeep hdrop).to₂
  exact (Primrec.list_rec hvectors (Primrec.const []) hstep).of_eq fun input => by
    induction vectors input with
    | nil => rfl
    | cons v tail ih =>
        rw [eliminate]
        dsimp only [List.recOn] at ih ⊢
        by_cases hp : RationalCode.Equivalent (rowEval (n input) (row input) v)
            RationalCode.zero
        · rw [if_pos hp, if_pos hp, ih]
        · rw [if_neg hp, if_neg hp]

set_option maxHeartbeats 800000 in
theorem kernelBasis_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {codedRows : α → List RationalVectorCode}
    (hn : Primrec n) (hrows : Primrec codedRows) :
    Primrec fun input => kernelBasis (n input) (codedRows input) := by
  let Z := α × (RationalVectorCode ×
    (List RationalVectorCode × List RationalVectorCode))
  have hstep' : Primrec fun input : Z =>
      eliminate (n input.1) input.2.1 input.2.2.2 :=
    eliminate_comp_primrec (hn.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ fun (input : α)
      (data : RationalVectorCode ×
        (List RationalVectorCode × List RationalVectorCode)) =>
      eliminate (n input) data.1 data.2.2 := hstep'.to₂
  exact (Primrec.list_rec hrows (standardBasis_comp_primrec hn) hstep).of_eq
    fun input => by
      induction codedRows input with
      | nil => rfl
      | cons row tail ih =>
          rw [kernelBasis]
          exact congrArg (eliminate (n input) row) ih

end KernelCode

namespace PointGeneratorCode

set_option maxHeartbeats 800000 in
theorem kernelPolynomial_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {v : α → RationalVectorCode}
    (hr : Primrec r) (hv : Primrec v) :
    Primrec fun input => kernelPolynomial (r input) (v input) := by
  let Y := α × ℕ
  have hlow : Primrec fun input : α => ExponentCode.low (r input) :=
    ExponentCode.low_primrec.comp hr
  have hcoefficient : Primrec fun input : Y =>
      (v input.1).getD input.2 RationalCode.zero :=
    Primrec.list_getD RationalCode.zero |>.comp (hv.comp Primrec.fst) Primrec.snd
  have hexponent : Primrec fun input : Y =>
      (ExponentCode.low (r input.1)).getD input.2 [] :=
    Primrec.list_getD [] |>.comp (hlow.comp Primrec.fst) Primrec.snd
  have hterm : Primrec₂ fun (input : α) (j : ℕ) =>
      ((v input).getD j RationalCode.zero,
        (ExponentCode.low (r input)).getD j []) :=
    (Primrec.pair hcoefficient hexponent).to₂
  have hterms : Primrec fun input : α =>
      (List.range (ExponentCode.low (r input)).length).map fun j =>
        ((v input).getD j RationalCode.zero,
          (ExponentCode.low (r input)).getD j []) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp hlow)) hterm
  have hnonzero : PrimrecPred fun term : RationalCode × List ℕ =>
      ¬RationalCode.Equivalent term.1 RationalCode.zero :=
    (RationalCode.equivalent_primrec.comp Primrec.fst
      (Primrec.const RationalCode.zero)).not
  exact (Primrec.listFilter hnonzero).comp hterms |>.of_eq fun input => by
    simp [kernelPolynomial]

set_option maxHeartbeats 800000 in
theorem generators_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {equations : α → List EquationCode}
    (hr : Primrec r) (hequations : Primrec equations) :
    Primrec fun input => generators (r input) (equations input) := by
  have hdegreeTerm : Primrec₂ fun (_ : α) (e : List ℕ) =>
      ([(RationalCode.one, e)] : RawPolynomial) := by
    exact (Primrec.list_cons.comp
      (Primrec.pair (Primrec.const RationalCode.one) Primrec.snd)
      (Primrec.const [])).to₂
  have hdegree : Primrec fun input : α =>
      (ExponentCode.degreeFive (r input)).map fun e =>
        [(RationalCode.one, e)] :=
    Primrec.list_map (ExponentCode.degreeFive_primrec.comp hr) hdegreeTerm
  have hlow : Primrec fun input : α => ExponentCode.low (r input) :=
    ExponentCode.low_primrec.comp hr
  have hdimension : Primrec fun input : α =>
      (ExponentCode.low (r input)).length :=
    Primrec.list_length.comp hlow
  have hrows : Primrec fun input : α =>
      RowsCode.rows (r input) (equations input) :=
    RowsCode.rows_comp_primrec hr hequations
  have hkernel : Primrec fun input : α =>
      KernelCode.kernelBasis (ExponentCode.low (r input)).length
        (RowsCode.rows (r input) (equations input)) :=
    KernelCode.kernelBasis_comp_primrec hdimension hrows
  have hkernelPolynomial : Primrec₂ fun (input : α) (v : RationalVectorCode) =>
      kernelPolynomial (r input) v := by
    have hkernelPolynomial' : Primrec fun input : α × RationalVectorCode =>
        kernelPolynomial (r input.1) input.2 :=
      kernelPolynomial_comp_primrec (hr.comp Primrec.fst) Primrec.snd
    exact hkernelPolynomial'.to₂
  have hkernelGenerators : Primrec fun input : α =>
      (KernelCode.kernelBasis (ExponentCode.low (r input)).length
        (RowsCode.rows (r input) (equations input))).map (kernelPolynomial (r input)) :=
    Primrec.list_map hkernel hkernelPolynomial
  exact (Primrec.list_append.comp hdegree hkernelGenerators).of_eq fun input => by
    simp [generators]

end PointGeneratorCode

namespace RawPolynomial

theorem add_comp_primrec {α : Type*} [Primcodable α]
    {p q : α → RawPolynomial} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun input => add (p input) (q input) :=
  Primrec.list_append.comp hp hq

theorem neg_comp_primrec {α : Type*} [Primcodable α]
    {p : α → RawPolynomial} (hp : Primrec p) :
    Primrec fun input => neg (p input) := by
  have hterm : Primrec₂ fun (_ : α) (term : RationalCode × List ℕ) =>
      (RationalCode.neg term.1, term.2) :=
    (Primrec.pair
      (RationalCode.neg_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_map hp hterm).of_eq fun input => by simp [neg]

set_option maxHeartbeats 800000 in
theorem mul_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {p q : α → RawPolynomial}
    (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) :
    Primrec fun input => mul (n input) (p input) (q input) := by
  let Y := α × RawTerm
  have hterm : Primrec₂ fun (input : Y) (b : RawTerm) =>
      (RationalCode.mul input.2.1 b.1,
        exponentAdd (n input.1) input.2.2 b.2) := by
    have hterm' : Primrec fun input : Y × RawTerm =>
        multiplyTerm
          (n input.1.1, (input.1.2, input.2)) :=
      multiplyTerm_primrec.comp <| Primrec.pair
        (hn.comp (Primrec.fst.comp Primrec.fst)) <|
        Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact hterm'.to₂
  have hinner : Primrec₂ fun (input : α) (a : RawTerm) =>
      (q input).map fun b =>
        (RationalCode.mul a.1 b.1, exponentAdd (n input) a.2 b.2) := by
    have hinner' : Primrec fun input : Y =>
        (q input.1).map fun b =>
          (RationalCode.mul input.2.1 b.1,
            exponentAdd (n input.1) input.2.2 b.2) :=
      Primrec.list_map (hq.comp Primrec.fst) hterm
    exact hinner'.to₂
  exact (Primrec.list_flatMap hp hinner).of_eq fun input => by simp [mul]

end RawPolynomial

namespace StandardPolynomialCode

theorem zeroExponent_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} (hn : Primrec n) :
    Primrec fun input => zeroExponent (n input) := by
  have hzero : Primrec₂ fun (_ : α) (_ : ℕ) => (0 : ℕ) :=
    (Primrec.const 0).to₂
  exact (Primrec.list_map (Primrec.list_range.comp hn) hzero).of_eq
    fun input => by simp [zeroExponent]

theorem unitExponent_comp_primrec {α : Type*} [Primcodable α]
    {n i : α → ℕ} (hn : Primrec n) (hi : Primrec i) :
    Primrec fun input => unitExponent (n input) (i input) := by
  have heq : PrimrecPred fun input : α × ℕ => input.2 = i input.1 :=
    Primrec.eq.comp Primrec.snd (hi.comp Primrec.fst)
  have hcoordinate : Primrec₂ fun (input : α) (j : ℕ) =>
      if j = i input then 1 else 0 :=
    (Primrec.ite heq (Primrec.const 1) (Primrec.const 0)).to₂
  exact (Primrec.list_map (Primrec.list_range.comp hn) hcoordinate).of_eq
    fun input => by simp [unitExponent]

theorem constant_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {a : α → RationalCode} (hn : Primrec n) (ha : Primrec a) :
    Primrec fun input => constant (n input) (a input) := by
  exact (Primrec.list_cons.comp
    (Primrec.pair ha (zeroExponent_comp_primrec hn))
    (Primrec.const [])).of_eq fun input => by simp [constant]

theorem standardVariable_comp_primrec {α : Type*} [Primcodable α]
    {n i : α → ℕ} (hn : Primrec n) (hi : Primrec i) :
    Primrec fun input => standardVariable (n input) (i input) := by
  exact (Primrec.list_cons.comp
    (Primrec.pair (Primrec.const RationalCode.one)
      (unitExponent_comp_primrec hn hi))
    (Primrec.const [])).of_eq fun input => by simp [standardVariable]

set_option maxHeartbeats 800000 in
theorem scale_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {a : α → RationalCode} {p : α → RawPolynomial}
    (hn : Primrec n) (ha : Primrec a) (hp : Primrec p) :
    Primrec fun input => scale (n input) (a input) (p input) := by
  exact (RawPolynomial.mul_comp_primrec hn (constant_comp_primrec hn ha) hp).of_eq
    fun _ => rfl

theorem sub_comp_primrec {α : Type*} [Primcodable α]
    {p q : α → RawPolynomial} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun input => sub (p input) (q input) := by
  exact (RawPolynomial.add_comp_primrec hp
    (RawPolynomial.neg_comp_primrec hq)).of_eq fun _ => rfl

set_option maxHeartbeats 800000 in
theorem pow_comp_primrec {α : Type*} [Primcodable α]
    {n k : α → ℕ} {p : α → RawPolynomial}
    (hn : Primrec n) (hp : Primrec p) (hk : Primrec k) :
    Primrec fun input => pow (n input) (p input) (k input) := by
  have hbase : Primrec fun input : α => constant (n input) RationalCode.one :=
    constant_comp_primrec hn (Primrec.const RationalCode.one)
  have hstep : Primrec₂ fun (input : α) (stepResult : ℕ × RawPolynomial) =>
      RawPolynomial.mul (n input) (p input) stepResult.2 := by
    have hstep' : Primrec fun input : α × (ℕ × RawPolynomial) =>
        RawPolynomial.mul (n input.1) (p input.1) input.2.2 :=
      RawPolynomial.mul_comp_primrec (hn.comp Primrec.fst)
        (hp.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
    exact hstep'.to₂
  exact (Primrec.nat_rec' hk hbase hstep).of_eq fun input => by
    induction k input with
    | zero => rfl
    | succ k ih => simp [pow, ih]

set_option maxHeartbeats 800000 in
theorem product_comp_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {polynomials : α → List RawPolynomial}
    (hn : Primrec n) (hpolynomials : Primrec polynomials) :
    Primrec fun input => product (n input) (polynomials input) := by
  let Z := α × (RawPolynomial × (List RawPolynomial × RawPolynomial))
  have hstep' : Primrec fun input : Z =>
      RawPolynomial.mul (n input.1) input.2.1 input.2.2.2 :=
    RawPolynomial.mul_comp_primrec (hn.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ fun (input : α)
      (data : RawPolynomial × (List RawPolynomial × RawPolynomial)) =>
      RawPolynomial.mul (n input) data.1 data.2.2 := hstep'.to₂
  exact (Primrec.list_rec hpolynomials
    (constant_comp_primrec hn (Primrec.const RationalCode.one)) hstep).of_eq
      fun input => by
        induction polynomials input with
        | nil => rfl
        | cons p polynomials ih =>
            rw [product]
            dsimp only [List.recOn] at ih ⊢
            exact congrArg (RawPolynomial.mul (n input) p) ih

set_option maxHeartbeats 800000 in
theorem pointGenerator_comp_primrec {α : Type*} [Primcodable α]
    {r i : α → ℕ} (hr : Primrec r) (hi : Primrec i) :
    Primrec fun input => pointGenerator (r input) (i input) := by
  have hn : Primrec fun input : α => 2 + r input :=
    Primrec.nat_add.comp (Primrec.const 2) hr
  have hsmall : PrimrecPred fun input : α => i input < 2 :=
    Primrec.nat_lt.comp hi (Primrec.const 2)
  have hcoefficient : Primrec fun input : α =>
      if i input < 2 then RationalCode.two else RationalCode.one :=
    Primrec.ite hsmall (Primrec.const RationalCode.two)
      (Primrec.const RationalCode.one)
  exact (sub_comp_primrec
    (scale_comp_primrec hn hcoefficient (standardVariable_comp_primrec hn hi))
    (constant_comp_primrec hn (Primrec.const RationalCode.one))).of_eq
      fun input => by simp [pointGenerator]

set_option maxHeartbeats 800000 in
theorem pointMonomial_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {e : α → List ℕ} (hr : Primrec r) (he : Primrec e) :
    Primrec fun input => pointMonomial (r input) (e input) := by
  let Y := α × ℕ
  have hn : Primrec fun input : α => 2 + r input :=
    Primrec.nat_add.comp (Primrec.const 2) hr
  have hexponent : Primrec fun input : Y => (e input.1).getD input.2 0 :=
    Primrec.list_getD 0 |>.comp (he.comp Primrec.fst) Primrec.snd
  have hpower : Primrec₂ fun (input : α) (i : ℕ) =>
      pow (2 + r input) (pointGenerator (r input) i) ((e input).getD i 0) := by
    have hpower' : Primrec fun input : Y =>
        pow (2 + r input.1) (pointGenerator (r input.1) input.2)
          ((e input.1).getD input.2 0) :=
      pow_comp_primrec (hn.comp Primrec.fst)
        (pointGenerator_comp_primrec (hr.comp Primrec.fst) Primrec.snd)
        hexponent
    exact hpower'.to₂
  have hfactors : Primrec fun input : α =>
      (List.range (2 + r input)).map fun i =>
        pow (2 + r input) (pointGenerator (r input) i) ((e input).getD i 0) :=
    Primrec.list_map (Primrec.list_range.comp hn) hpower
  exact (product_comp_primrec hn hfactors).of_eq fun input => by
    simp [pointMonomial]

set_option maxHeartbeats 800000 in
theorem expand_comp_primrec {α : Type*} [Primcodable α]
    {r : α → ℕ} {p : α → RawPolynomial} (hr : Primrec r) (hp : Primrec p) :
    Primrec fun input => expand (r input) (p input) := by
  let Y := α × (RationalCode × List ℕ)
  have hn : Primrec fun input : Y => 2 + r input.1 :=
    Primrec.nat_add.comp (Primrec.const 2) (hr.comp Primrec.fst)
  have hterm : Primrec₂ fun (input : α) (term : RationalCode × List ℕ) =>
      scale (2 + r input) term.1 (pointMonomial (r input) term.2) := by
    have hterm' : Primrec fun input : Y =>
        scale (2 + r input.1) input.2.1
          (pointMonomial (r input.1) input.2.2) :=
      scale_comp_primrec hn (Primrec.fst.comp Primrec.snd) <|
        pointMonomial_comp_primrec (hr.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd)
    exact hterm'.to₂
  exact (Primrec.list_flatMap hp hterm).of_eq fun input => by simp [expand]

end StandardPolynomialCode

/-! ### Computability of the complete compiler -/

set_option maxHeartbeats 800000 in
theorem compilerRaw_primrec : Primrec compilerRaw := by
  have hsystem : Primrec fun q : PolynomialInputRaw =>
      ProgramCode.guardedSystem q.1 q.2 :=
    ProgramCode.guardedSystem_primrec
  have hr : Primrec fun q : PolynomialInputRaw =>
      (ProgramCode.guardedSystem q.1 q.2).1 :=
    Primrec.fst.comp hsystem
  have hequations : Primrec fun q : PolynomialInputRaw =>
      (ProgramCode.guardedSystem q.1 q.2).2 :=
    Primrec.snd.comp hsystem
  have hgenerators : Primrec fun q : PolynomialInputRaw =>
      PointGeneratorCode.generators
        (ProgramCode.guardedSystem q.1 q.2).1
        (ProgramCode.guardedSystem q.1 q.2).2 :=
    PointGeneratorCode.generators_comp_primrec hr hequations
  have hexpand : Primrec₂ fun (q : PolynomialInputRaw) (p : RawPolynomial) =>
      StandardPolynomialCode.expand
        (ProgramCode.guardedSystem q.1 q.2).1 p := by
    have hexpand' : Primrec fun input : PolynomialInputRaw × RawPolynomial =>
        StandardPolynomialCode.expand
          (ProgramCode.guardedSystem input.1.1 input.1.2).1 input.2 :=
      StandardPolynomialCode.expand_comp_primrec
        (hr.comp Primrec.fst) Primrec.snd
    exact hexpand'.to₂
  have hcompiledGenerators : Primrec fun q : PolynomialInputRaw =>
      (PointGeneratorCode.generators
        (ProgramCode.guardedSystem q.1 q.2).1
        (ProgramCode.guardedSystem q.1 q.2).2).map
          (StandardPolynomialCode.expand
            (ProgramCode.guardedSystem q.1 q.2).1) :=
    Primrec.list_map hgenerators hexpand
  exact (Primrec.pair
    (Primrec.nat_add.comp (Primrec.const 2) hr) hcompiledGenerators).of_eq
      fun q => by simp [compilerRaw]

theorem compilerCode_primrec : Primrec compilerCode := by
  have hval : Primrec (Subtype.val : PolynomialInputCode → PolynomialInputRaw) :=
    Primrec.subtype_val (hp := polynomialInputRaw_valid_primrec)
  exact Primrec.subtype_mk (hp := idealPresentationRaw_valid_primrec)
    (compilerRaw_primrec.comp hval)

theorem compiler_primrec : Primrec compiler := by
  have hinput : Primrec polynomialInputToCode := by
    exact Primrec.of_equiv
  have houtput : Primrec idealPresentationOfCode := by
    exact Primrec.of_equiv_symm
  exact (houtput.comp (compilerCode_primrec.comp hinput)).of_eq fun _ => rfl

theorem compiler_computable : Computable compiler :=
  compiler_primrec.to_comp

end Trinomial
