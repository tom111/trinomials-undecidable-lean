import TrinomialUndecidability.Computability.MathlibDiophantineBinary

/-!
# Bitwise meet is Diophantine

The sparse power-cipher construction needs a Diophantine graph for bitwise conjunction.  The
graph is expressed using the bit-inclusion relation from `MathlibDiophantineBinary`: a meet is
split from each operand by disjoint additive remainders, and those remainders are themselves
disjoint.  Every relation in that characterization is Diophantine.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineBitwise

open TrinomialUndecidability.Computability.MathlibDiophantineBinary

/-! ## Arithmetic characterization -/

/-- Bitwise disjointness decomposes into the low bits and the shifted words. -/
theorem land_eq_zero_rec (a b : ℕ) :
    a &&& b = 0 ↔
      (a.bodd && b.bodd) = false ∧ a.div2 &&& b.div2 = 0 := by
  have hland :
      a &&& b = Nat.bit (a.bodd && b.bodd) (a.div2 &&& b.div2) := by
    conv_lhs =>
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b, Nat.land_bit]
  have hzero : 0 = Nat.bit false 0 := rfl
  rw [hland, hzero]
  simpa using bit_eq_bit_iff (a.bodd && b.bodd) false (a.div2 &&& b.div2) 0

/-- Adding `b` preserves every set bit of `a` exactly when the two summands are bitwise
disjoint. -/
theorem binaryLE_add_iff_land_eq_zero (a b : ℕ) :
    binaryLE a (a + b) ↔ a &&& b = 0 := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
      by_cases ha : a = 0
      · subst a
        simp [binaryLE]
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha
        have hadiv : a.div2 < a := by
          rw [Nat.div2_val]
          exact Nat.div_lt_self hapos (by omega)
        have hrec := ih a.div2 hadiv b.div2
        rw [binaryLE_rec, land_eq_zero_rec]
        cases hab : a.bodd <;> cases hbb : b.bodd
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          simp [Nat.bodd_add, hab, hbb, hdiv, hrec]
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          simp [Nat.bodd_add, hab, hbb, hdiv, hrec]
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          simp [Nat.bodd_add, hab, hbb, hdiv, hrec]
        · simp [Nat.bodd_add, hab, hbb]

/-- Bitwise-disjoint natural numbers add without carries, so addition equals bitwise union. -/
theorem add_eq_or_of_land_eq_zero {a b : ℕ} (hdisjoint : a &&& b = 0) :
    a + b = a ||| b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
      by_cases ha : a = 0
      · subst a
        simp
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha
        have hadiv : a.div2 < a := by
          rw [Nat.div2_val]
          exact Nat.div_lt_self hapos (by omega)
        rw [land_eq_zero_rec] at hdisjoint
        have hrec := ih a.div2 hadiv hdisjoint.2
        cases hab : a.bodd <;> cases hbb : b.bodd
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          calc
            a + b = Nat.bit (a + b).bodd (a + b).div2 :=
              (Nat.bit_bodd_div2 (a + b)).symm
            _ = Nat.bit (a.bodd || b.bodd) (a.div2 ||| b.div2) := by
              rw [hdiv, hrec]
              simp [Nat.bodd_add, hab, hbb]
            _ = Nat.bit a.bodd a.div2 ||| Nat.bit b.bodd b.div2 :=
              (Nat.lor_bit _ _ _ _).symm
            _ = a ||| b := by rw [Nat.bit_bodd_div2, Nat.bit_bodd_div2]
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          calc
            a + b = Nat.bit (a + b).bodd (a + b).div2 :=
              (Nat.bit_bodd_div2 (a + b)).symm
            _ = Nat.bit (a.bodd || b.bodd) (a.div2 ||| b.div2) := by
              rw [hdiv, hrec]
              simp [Nat.bodd_add, hab, hbb]
            _ = Nat.bit a.bodd a.div2 ||| Nat.bit b.bodd b.div2 :=
              (Nat.lor_bit _ _ _ _).symm
            _ = a ||| b := by rw [Nat.bit_bodd_div2, Nat.bit_bodd_div2]
        · have hdiv : (a + b).div2 = a.div2 + b.div2 := by
            rw [Nat.div2_val, Nat.div2_val, Nat.div2_val, Nat.add_div (by omega)]
            rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
            simp [hab, hbb]
          calc
            a + b = Nat.bit (a + b).bodd (a + b).div2 :=
              (Nat.bit_bodd_div2 (a + b)).symm
            _ = Nat.bit (a.bodd || b.bodd) (a.div2 ||| b.div2) := by
              rw [hdiv, hrec]
              simp [Nat.bodd_add, hab, hbb]
            _ = Nat.bit a.bodd a.div2 ||| Nat.bit b.bodd b.div2 :=
              (Nat.lor_bit _ _ _ _).symm
            _ = a ||| b := by rw [Nat.bit_bodd_div2, Nat.bit_bodd_div2]
        · simp [hab, hbb] at hdisjoint

/-- An exact additive-remainder characterization of bitwise conjunction. -/
theorem land_eq_iff_exists (result left right : ℕ) :
    result = left &&& right ↔
      ∃ leftRest rightRest,
        left = result + leftRest ∧
          right = result + rightRest ∧
          binaryLE result (result + leftRest) ∧
          binaryLE result (result + rightRest) ∧
          binaryLE leftRest (leftRest + rightRest) := by
  constructor
  · intro hresult
    let leftRest := left - result
    let rightRest := right - result
    have hresultLeft : result ≤ left := by
      rw [hresult]
      exact Nat.and_le_left
    have hresultRight : result ≤ right := by
      rw [hresult]
      exact Nat.and_le_right
    have hleft : left = result + leftRest := by
      unfold leftRest
      exact (Nat.add_sub_of_le hresultLeft).symm
    have hright : right = result + rightRest := by
      unfold rightRest
      exact (Nat.add_sub_of_le hresultRight).symm
    have hbinaryLeft : binaryLE result (result + leftRest) := by
      unfold binaryLE
      rw [← hleft, hresult]
      simp [Nat.and_comm]
    have hbinaryRight : binaryLE result (result + rightRest) := by
      unfold binaryLE
      rw [← hright, hresult]
      simp [Nat.and_comm, Nat.and_left_comm]
    have hdisjointLeft : result &&& leftRest = 0 :=
      (binaryLE_add_iff_land_eq_zero result leftRest).mp hbinaryLeft
    have hdisjointRight : result &&& rightRest = 0 :=
      (binaryLE_add_iff_land_eq_zero result rightRest).mp hbinaryRight
    have hleftOr : result ||| leftRest = left :=
      (add_eq_or_of_land_eq_zero hdisjointLeft).symm.trans hleft.symm
    have hrightOr : result ||| rightRest = right :=
      (add_eq_or_of_land_eq_zero hdisjointRight).symm.trans hright.symm
    have hor : result ||| (leftRest &&& rightRest) = result := by
      rw [Nat.or_and_distrib_left, hleftOr, hrightOr, ← hresult]
    have hrests : leftRest &&& rightRest = 0 := by
      apply Nat.eq_of_testBit_eq
      intro index
      have horBit := congrArg (fun value : ℕ ↦ value.testBit index) hor
      have hleftBit := congrArg (fun value : ℕ ↦ value.testBit index) hdisjointLeft
      simp only [Nat.testBit_or, Nat.testBit_and] at horBit hleftBit ⊢
      cases hr : result.testBit index <;>
        cases hl : leftRest.testBit index <;>
          cases hrr : rightRest.testBit index <;>
            simp [hr, hl, hrr] at horBit hleftBit ⊢
    exact ⟨leftRest, rightRest, hleft, hright, hbinaryLeft, hbinaryRight,
      (binaryLE_add_iff_land_eq_zero leftRest rightRest).mpr hrests⟩
  · rintro ⟨leftRest, rightRest, rfl, rfl, hresultLeft, hresultRight, hrests⟩
    have hleft : result &&& leftRest = 0 :=
      (binaryLE_add_iff_land_eq_zero result leftRest).mp hresultLeft
    have hright : result &&& rightRest = 0 :=
      (binaryLE_add_iff_land_eq_zero result rightRest).mp hresultRight
    have hrest : leftRest &&& rightRest = 0 :=
      (binaryLE_add_iff_land_eq_zero leftRest rightRest).mp hrests
    calc
      result = result ||| (leftRest &&& rightRest) := by simp [hrest]
      _ = (result ||| leftRest) &&& (result ||| rightRest) :=
        Nat.or_and_distrib_left _ _ _
      _ = (result + leftRest) &&& (result + rightRest) := by
        rw [add_eq_or_of_land_eq_zero hleft, add_eq_or_of_land_eq_zero hright]

/-! ## Fixed-width bit blocks -/

/-- Pack `length` little-endian digits into blocks of `width` bits. -/
def blockExpansion (length width : ℕ) (digits : ℕ → ℕ) : ℕ :=
  baseExpansion length (2 ^ width) digits

/-- Split off the highest block of a fixed-width expansion. -/
theorem blockExpansion_succ (length width : ℕ) (digits : ℕ → ℕ) :
    blockExpansion (length + 1) width digits =
      2 ^ (width * length) * digits length + blockExpansion length width digits := by
  unfold blockExpansion baseExpansion
  rw [Finset.sum_range_succ]
  rw [pow_mul]
  ring

/-- A fixed-width expansion of bounded digits fits below the next block boundary. -/
theorem blockExpansion_lt (length width : ℕ) (digits : ℕ → ℕ)
    (hdigits : ∀ index < length, digits index < 2 ^ width) :
    blockExpansion length width digits < 2 ^ (width * length) := by
  unfold blockExpansion
  rw [pow_mul]
  exact baseExpansion_lt (by positivity) hdigits

/-- Bitwise conjunction acts independently on every fixed-width block. -/
theorem blockExpansion_land (length width : ℕ) (left right : ℕ → ℕ)
    (hleft : ∀ index < length, left index < 2 ^ width)
    (hright : ∀ index < length, right index < 2 ^ width) :
    blockExpansion length width left &&& blockExpansion length width right =
      blockExpansion length width (fun index ↦ left index &&& right index) := by
  induction length with
  | zero => simp [blockExpansion, baseExpansion]
  | succ length ih =>
      rw [blockExpansion_succ, blockExpansion_succ, blockExpansion_succ]
      apply Nat.eq_of_testBit_eq
      intro bit
      have hleftPrefix :
          blockExpansion length width left < 2 ^ (width * length) :=
        blockExpansion_lt length width left fun index hindex ↦
          hleft index (Nat.lt_succ_of_lt hindex)
      have hrightPrefix :
          blockExpansion length width right < 2 ^ (width * length) :=
        blockExpansion_lt length width right fun index hindex ↦
          hright index (Nat.lt_succ_of_lt hindex)
      have hlandDigits :
          ∀ index < length,
            left index &&& right index < 2 ^ width := by
        intro index hindex
        exact Nat.and_lt_two_pow _
          (hright index (Nat.lt_succ_of_lt hindex))
      have hlandPrefix :
          blockExpansion length width (fun index ↦ left index &&& right index) <
            2 ^ (width * length) :=
        blockExpansion_lt length width _ hlandDigits
      rw [Nat.testBit_and]
      rw [Nat.testBit_two_pow_mul_add _ hleftPrefix]
      rw [Nat.testBit_two_pow_mul_add _ hrightPrefix]
      rw [Nat.testBit_two_pow_mul_add _ hlandPrefix]
      by_cases hbit : bit < width * length
      · simp only [hbit, if_true]
        have htest := congrFun (congrArg Nat.testBit (ih
          (fun index hindex ↦ hleft index (Nat.lt_succ_of_lt hindex))
          (fun index hindex ↦ hright index (Nat.lt_succ_of_lt hindex)))) bit
        simpa only [Nat.testBit_and] using htest
      · simp [hbit, Nat.testBit_and]

/-! ## Diophantine graph -/

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

/-- The ternary graph `result = left &&& right` is Diophantine. -/
theorem land_graph_dioph :
    Dioph fun values : Vector3 ℕ 3 ↦ values &0 = values &1 &&& values &2 := by
  have hinterior :
      Dioph fun values : Vector3 ℕ 5 ↦
        values &3 = values &2 + values &1 ∧
          values &4 = values &2 + values &0 ∧
          binaryLE (values &2) (values &2 + values &1) ∧
          binaryLE (values &2) (values &2 + values &0) ∧
          binaryLE (values &1) (values &1 + values &0) :=
    (D&3 D= (D&2 D+ D&1)) D∧
      ((D&4 D= (D&2 D+ D&0)) D∧
        (binaryLE_dioph (D&2) (D&2 D+ D&1) D∧
          (binaryLE_dioph (D&2) (D&2 D+ D&0) D∧
            binaryLE_dioph (D&1) (D&1 D+ D&0))))
  have hexists :
      Dioph fun values : Vector3 ℕ 3 ↦
        ∃ leftRest rightRest,
          values &1 = values &0 + leftRest ∧
            values &2 = values &0 + rightRest ∧
            binaryLE (values &0) (values &0 + leftRest) ∧
            binaryLE (values &0) (values &0 + rightRest) ∧
            binaryLE leftRest (leftRest + rightRest) := by
    apply Dioph.ext ((D∃) 3 <| (D∃) 4 <| hinterior)
    intro values
    constructor
    · rintro ⟨leftRest, rightRest, hleft, hright, hresultLeft,
        hresultRight, hrests⟩
      exact ⟨leftRest, rightRest, hleft, hright, hresultLeft,
        hresultRight, hrests⟩
    · rintro ⟨leftRest, rightRest, hleft, hright, hresultLeft,
        hresultRight, hrests⟩
      exact ⟨leftRest, rightRest, hleft, hright, hresultLeft,
        hresultRight, hrests⟩
  apply Dioph.ext hexists
  intro values
  exact (land_eq_iff_exists (values &0) (values &1) (values &2)).symm

/-- Bitwise conjunction is a Diophantine binary function. -/
theorem land_diophFn_base :
    DiophFn fun values : Vector3 ℕ 2 ↦ values &0 &&& values &1 := by
  apply (Dioph.diophFn_vec _).2
  apply Dioph.ext land_graph_dioph
  intro values
  change
    (values &0 = values &1 &&& values &2) ↔
      values &1 &&& values &2 = values &0
  exact eq_comm

/-- Composing bitwise conjunction with two Diophantine functions preserves
Diophantineness. -/
theorem land_diophFn {α : Type} {left right : (α → ℕ) → ℕ}
    (hleft : DiophFn left) (hright : DiophFn right) :
    DiophFn fun values ↦ left values &&& right values :=
  Dioph.diophFn_comp2 hleft hright land_diophFn_base

end TrinomialUndecidability.Computability.MathlibDiophantineBitwise
