import TrinomialUndecidability.Computability.MathlibDiophantineBitwise

/-!
# A two-view regular cipher for bounded Diophantine quantification

This module replaces the double-exponentially sparse one-view cipher with two regular radix
views.  If the left view places digit `a i` in block `i` and the right view places digit `b j`
in block `length * j`, their product places `a i * b j` in block `i + length * j`.  The diagonal
blocks are exactly `(length + 1) * i`; a geometric bit mask therefore extracts the pointwise
products.  The same construction compares the two views and gives an exact Diophantine cipher
predicate.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher

open scoped BigOperators

open TrinomialUndecidability.Computability.MathlibDiophantineBinary
open TrinomialUndecidability.Computability.MathlibDiophantineBitwise

def geometricSum (length base : ℕ) : ℕ :=
  ∑ index ∈ Finset.range length, base ^ index

theorem geometricSum_equation {length base : ℕ} (hbase : 1 ≤ base) :
    1 + (base - 1) * geometricSum length base = base ^ length := by
  induction length with
  | zero => simp [geometricSum]
  | succ length ih =>
      have hih :
          1 + (base - 1) *
              (∑ index ∈ Finset.range length, base ^ index) =
            base ^ length := by
        simpa [geometricSum] using ih
      rw [geometricSum, Finset.sum_range_succ]
      rw [pow_succ]
      calc
        1 + (base - 1) *
              ((∑ index ∈ Finset.range length, base ^ index) + base ^ length) =
            (1 + (base - 1) *
              (∑ index ∈ Finset.range length, base ^ index)) +
                (base - 1) * base ^ length := by ring
        _ = base ^ length + (base - 1) * base ^ length := by rw [hih]
        _ = base ^ length * (1 + (base - 1)) := by ring
        _ = base ^ length * base := by
          rw [show 1 + (base - 1) = base by omega]

theorem geometricSum_eq_of_equation {length base value : ℕ} (hbase : 2 ≤ base)
    (hequation : 1 + (base - 1) * value = base ^ length) :
    value = geometricSum length base := by
  have hcanonical := geometricSum_equation (length := length) (by omega : 1 ≤ base)
  rw [← hcanonical] at hequation
  have hmul : (base - 1) * value = (base - 1) * geometricSum length base :=
    Nat.add_left_cancel hequation
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

theorem geometricSum_closedForm {length base : ℕ} (hbase : 2 ≤ base) :
    geometricSum length base = (base ^ length - 1) / (base - 1) := by
  have hequation := geometricSum_equation (length := length) (by omega : 1 ≤ base)
  have hmul : base ^ length - 1 = (base - 1) * geometricSum length base := by
    omega
  rw [hmul]
  exact (Nat.mul_div_cancel_left _ (by omega)).symm

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

theorem geometricSum_diophFn {α : Type}
    {length base : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hbase : DiophFn base)
    (hbaseBound : ∀ values, 2 ≤ base values) :
    DiophFn fun values ↦ geometricSum (length values) (base values) := by
  have hpower : DiophFn fun values ↦ base values ^ length values :=
    Dioph.pow_dioph hbase hlength
  have hclosed :
      DiophFn fun values ↦
        (base values ^ length values - 1) / (base values - 1) :=
    (hpower D- D.1) D/ (hbase D- D.1)
  have hfunction :
      (fun values ↦ geometricSum (length values) (base values)) =
        fun values ↦ (base values ^ length values - 1) / (base values - 1) := by
    funext values
    exact geometricSum_closedForm (hbaseBound values)
  exact hfunction.symm ▸ hclosed

theorem geometricSum_zero (length : ℕ) :
    geometricSum length 0 = if length = 0 then 0 else 1 := by
  cases length with
  | zero => simp [geometricSum]
  | succ length =>
      simp [geometricSum, Finset.sum_range_succ']

theorem geometricSum_diophFn_base :
    DiophFn fun values : Vector3 ℕ 2 ↦ geometricSum (values &0) (values &1) := by
  apply (Dioph.diophFn_vec _).2
  have hpower :
      DiophFn fun values : Vector3 ℕ 3 ↦ (values &2) ^ (values &1) :=
    Dioph.pow_dioph (D&2) (D&1)
  have hgraph :
      Dioph fun values : Vector3 ℕ 3 ↦
        (values &2 = 0 ∧
            ((values &1 = 0 ∧ values &0 = 0) ∨
              (0 < values &1 ∧ values &0 = 1))) ∨
          (values &2 = 1 ∧ values &0 = values &1) ∨
          (2 ≤ values &2 ∧
            1 + (values &2 - 1) * values &0 = (values &2) ^ (values &1)) :=
    ((D&2 D= D.0) D∧
        (((D&1 D= D.0) D∧ (D&0 D= D.0)) D∨
          ((D.0 D< D&1) D∧ (D&0 D= D.1)))) D∨
      (((D&2 D= D.1) D∧ (D&0 D= D&1)) D∨
        ((D.2 D≤ D&2) D∧
          (((D.1 D+ ((D&2 D- D.1) D* D&0))) D= hpower)))
  apply Dioph.ext hgraph
  intro values
  change
    ((values &2 = 0 ∧
          ((values &1 = 0 ∧ values &0 = 0) ∨
            (0 < values &1 ∧ values &0 = 1))) ∨
        (values &2 = 1 ∧ values &0 = values &1) ∨
        (2 ≤ values &2 ∧
          1 + (values &2 - 1) * values &0 = (values &2) ^ (values &1))) ↔
      geometricSum (values &1) (values &2) = values &0
  rcases eq_or_ne (values &2) 0 with hzero | hzero
  · rw [hzero, geometricSum_zero]
    by_cases hlength : values &1 = 0
    · simp [hlength, eq_comm]
    · have hpositive : 0 < values &1 := Nat.pos_of_ne_zero hlength
      simp [hlength, hpositive, eq_comm]
  · rcases eq_or_ne (values &2) 1 with hone | hone
    · rw [hone]
      simp [geometricSum, eq_comm]
    · have hbase : 2 ≤ values &2 := by omega
      simp only [hzero, hone, false_and, hbase, true_and, false_or]
      constructor
      · intro hequation
        exact (geometricSum_eq_of_equation hbase hequation).symm
      · intro hequality
        rw [← hequality]
        exact geometricSum_equation (by omega)

theorem geometricSum_comp_diophFn {α : Type}
    {length base : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hbase : DiophFn base) :
    DiophFn fun values ↦ geometricSum (length values) (base values) :=
  Dioph.diophFn_comp2 hlength hbase geometricSum_diophFn_base

theorem sum_flatten (rows cols : ℕ) (hcols : 0 < cols) (term : ℕ → ℕ → ℕ) :
    (∑ flat ∈ Finset.range (rows * cols), term (flat % cols) (flat / cols)) =
      ∑ row ∈ Finset.range rows, ∑ col ∈ Finset.range cols, term col row := by
  induction rows with
  | zero => simp
  | succ rows ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
      congr 1
      apply Finset.sum_congr rfl
      intro col hcol
      have hcol' : col < cols := Finset.mem_range.mp hcol
      rw [Nat.add_comm (rows * cols) col, Nat.mul_comm rows cols]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hcols]
      rw [Nat.mod_eq_of_lt hcol', Nat.div_eq_of_lt hcol']
      simp

theorem baseExpansion_unique {length base : ℕ} {left right : ℕ → ℕ}
    (hbase : 0 < base)
    (hleft : ∀ index < length, left index < base)
    (hright : ∀ index < length, right index < base)
    (hequality : baseExpansion length base left = baseExpansion length base right) :
    ∀ index < length, left index = right index := by
  intro index hindex
  have hdigit := congrArg (fun value ↦ value / base ^ index % base) hequality
  change
    baseExpansion length base left / base ^ index % base =
      baseExpansion length base right / base ^ index % base at hdigit
  rw [baseExpansion_digit hindex hbase
    (fun position hposition ↦ hleft position (hposition.trans hindex))] at hdigit
  rw [baseExpansion_digit hindex hbase
    (fun position hposition ↦ hright position (hposition.trans hindex))] at hdigit
  simpa [Nat.mod_eq_of_lt (hleft index hindex),
    Nat.mod_eq_of_lt (hright index hindex)] using hdigit

theorem exists_baseExpansion_of_lt {length base value : ℕ} (hbase : 0 < base)
    (hvalue : value < base ^ length) :
    ∃ digits : ℕ → ℕ,
      (∀ index < length, digits index < base) ∧
        baseExpansion length base digits = value := by
  induction length generalizing value with
  | zero =>
      have hzero : value = 0 := by simpa using hvalue
      exact ⟨fun _ ↦ 0, by simp, by simp [baseExpansion, hzero]⟩
  | succ length ih =>
      have hquotient : value / base < base ^ length := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_comm, ← pow_succ]
        exact hvalue
      obtain ⟨tail, htailBound, htail⟩ := ih hquotient
      let digits : ℕ → ℕ := fun index ↦
        if index = 0 then value % base else tail (index - 1)
      refine ⟨digits, ?_, ?_⟩
      · intro index hindex
        by_cases hzero : index = 0
        · simp [digits, hzero, Nat.mod_lt _ hbase]
        · have hpred : index - 1 < length := by omega
          simpa [digits, hzero] using htailBound (index - 1) hpred
      · rw [baseExpansion_split (index := 0) (by omega)]
        simp only [baseExpansion, Finset.range_zero, Finset.sum_empty, pow_zero,
          zero_add, one_mul]
        change
          (if 0 = 0 then value % base else tail (0 - 1)) +
              base * baseExpansion length base
                (fun offset ↦
                  if 0 + 1 + offset = 0 then value % base
                  else tail (0 + 1 + offset - 1)) =
            value
        simp only [if_pos, zero_add, Nat.add_eq_zero_iff, one_ne_zero, false_and,
          if_false, Nat.add_sub_cancel_left]
        rw [htail]
        exact Nat.mod_add_div value base

def leftView (length width : ℕ) (digits : ℕ → ℕ) : ℕ :=
  blockExpansion length width digits

def rightView (length width : ℕ) (digits : ℕ → ℕ) : ℕ :=
  ∑ index ∈ Finset.range length,
    digits index * (2 ^ width) ^ (length * index)

def matrixView (length width : ℕ) (digits : ℕ → ℕ → ℕ) : ℕ :=
  blockExpansion (length * length) width
    (fun flat ↦ digits (flat % length) (flat / length))

def diagonalView (length width : ℕ) (digits : ℕ → ℕ) : ℕ :=
  ∑ index ∈ Finset.range length,
    digits index * (2 ^ width) ^ ((length + 1) * index)

def diagonalMask (length width : ℕ) : ℕ :=
  (2 ^ width - 1) * geometricSum length ((2 ^ width) ^ (length + 1))

theorem matrixView_eq_doubleSum {length width : ℕ} (hlength : 0 < length)
    (digits : ℕ → ℕ → ℕ) :
    matrixView length width digits =
      ∑ row ∈ Finset.range length,
        ∑ col ∈ Finset.range length,
          digits col row * (2 ^ width) ^ (col + length * row) := by
  unfold matrixView blockExpansion baseExpansion
  rw [← sum_flatten length length hlength
    (fun col row ↦ digits col row * (2 ^ width) ^ (col + length * row))]
  apply Finset.sum_congr rfl
  intro flat _
  rw [Nat.mod_add_div flat length]

theorem left_mul_right_eq_matrixView {length width : ℕ} (hlength : 0 < length)
    (left right : ℕ → ℕ) :
    leftView length width left * rightView length width right =
      matrixView length width (fun col row ↦ left col * right row) := by
  rw [matrixView_eq_doubleSum hlength]
  unfold leftView blockExpansion baseExpansion rightView
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  rw [pow_add]
  ring

theorem diagonalMask_eq_matrixView {length width : ℕ} (hlength : 0 < length) :
    diagonalMask length width =
      matrixView length width
        (fun col row ↦ if col = row then 2 ^ width - 1 else 0) := by
  rw [matrixView_eq_doubleSum hlength]
  unfold diagonalMask geometricSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row hrow
  have hrow' : row < length := Finset.mem_range.mp hrow
  rw [Finset.sum_eq_single row]
  · simp only [ite_true]
    rw [show row + length * row = (length + 1) * row by ring]
    rw [pow_mul]
  · intro col hcol hne
    simp [hne]
  · exact fun hnot ↦ (hnot hrow).elim

theorem diagonalView_eq_matrixView {length width : ℕ} (hlength : 0 < length)
    (digits : ℕ → ℕ) :
    diagonalView length width digits =
      matrixView length width
        (fun col row ↦ if col = row then digits row else 0) := by
  rw [matrixView_eq_doubleSum hlength]
  unfold diagonalView
  apply Finset.sum_congr rfl
  intro row hrow
  rw [Finset.sum_eq_single row]
  · simp only [ite_true]
    rw [show row + length * row = (length + 1) * row by ring]
  · intro col hcol hne
    simp [hne]
  · exact fun hnot ↦ (hnot hrow).elim

theorem matrixView_land {length width : ℕ} (hlength : 0 < length)
    (left right : ℕ → ℕ → ℕ)
    (hleft : ∀ col row, col < length → row < length → left col row < 2 ^ width)
    (hright : ∀ col row, col < length → row < length → right col row < 2 ^ width) :
    matrixView length width left &&& matrixView length width right =
      matrixView length width (fun col row ↦ left col row &&& right col row) := by
  unfold matrixView
  apply blockExpansion_land
  · intro flat hflat
    exact hleft _ _ (Nat.mod_lt _ hlength)
      (Nat.div_lt_of_lt_mul hflat)
  · intro flat hflat
    exact hright _ _ (Nat.mod_lt _ hlength)
      (Nat.div_lt_of_lt_mul hflat)

theorem matrixView_land_diagonal {length width : ℕ} (hlength : 0 < length)
    (digits : ℕ → ℕ → ℕ)
    (hdigits : ∀ col row, col < length → row < length → digits col row < 2 ^ width) :
    matrixView length width digits &&& diagonalMask length width =
      diagonalView length width (fun index ↦ digits index index) := by
  rw [diagonalMask_eq_matrixView hlength]
  rw [matrixView_land hlength]
  · rw [matrixView_eq_doubleSum hlength]
    unfold diagonalView
    apply Finset.sum_congr rfl
    intro row hrow
    have hrow' : row < length := Finset.mem_range.mp hrow
    rw [Finset.sum_eq_single row]
    · simp only [ite_true]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow (hdigits row row hrow' hrow')]
      rw [show row + length * row = (length + 1) * row by ring]
    · intro col hcol hne
      simp [hne]
    · exact fun hnot ↦ (hnot hrow).elim
  · exact hdigits
  · intro col row _ _
    split
    · exact Nat.sub_lt (by positivity) (by omega)
    · simp

theorem mixedProduct_land_diagonal {length width : ℕ} (hlength : 0 < length)
    (left right : ℕ → ℕ)
    (hproduct : ∀ col row, col < length → row < length →
      left col * right row < 2 ^ width) :
    (leftView length width left * rightView length width right) &&&
        diagonalMask length width =
      diagonalView length width (fun index ↦ left index * right index) := by
  rw [left_mul_right_eq_matrixView hlength]
  exact matrixView_land_diagonal hlength _ hproduct

theorem diagonalView_injective {length width : ℕ} (hlength : 0 < length)
    {left right : ℕ → ℕ}
    (hleft : ∀ index < length, left index < 2 ^ width)
    (hright : ∀ index < length, right index < 2 ^ width)
    (hequality : diagonalView length width left = diagonalView length width right) :
    ∀ index < length, left index = right index := by
  rw [diagonalView_eq_matrixView hlength,
    diagonalView_eq_matrixView hlength] at hequality
  unfold matrixView blockExpansion at hequality
  have hleftMatrix :
      ∀ flat < length * length,
        (if flat % length = flat / length then left (flat / length) else 0) <
          2 ^ width := by
    intro flat hflat
    split
    · exact hleft _ (Nat.div_lt_of_lt_mul hflat)
    · positivity
  have hrightMatrix :
      ∀ flat < length * length,
        (if flat % length = flat / length then right (flat / length) else 0) <
          2 ^ width := by
    intro flat hflat
    split
    · exact hright _ (Nat.div_lt_of_lt_mul hflat)
    · positivity
  have hmatrix := baseExpansion_unique (by positivity) hleftMatrix hrightMatrix hequality
  intro index hindex
  have hflat : (length + 1) * index < length * length := by
    nlinarith
  have hselected := hmatrix ((length + 1) * index) hflat
  have hmod : ((length + 1) * index) % length = index := by
    rw [Nat.add_mul, one_mul, Nat.add_comm (length * index) index,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hindex
  have hdiv : ((length + 1) * index) / length = index := by
    rw [Nat.add_mul, one_mul, Nat.add_comm (length * index) index,
      Nat.add_mul_div_left _ _ hlength]
    rw [Nat.div_eq_of_lt hindex, zero_add]
  simpa [hmod, hdiv] using hselected

def viewsAgree (length width leftCode rightCode : ℕ) : Prop :=
  (leftCode * rightView length width (fun _ ↦ 1)) &&&
      diagonalMask length width =
    (leftView length width (fun _ ↦ 1) * rightCode) &&&
      diagonalMask length width

theorem viewsAgree_spec {length width : ℕ} (hlength : 0 < length)
    {left right : ℕ → ℕ}
    (hleft : ∀ index < length, left index < 2 ^ width)
    (hright : ∀ index < length, right index < 2 ^ width) :
    viewsAgree length width (leftView length width left) (rightView length width right) ↔
      ∀ index < length, left index = right index := by
  unfold viewsAgree
  rw [mixedProduct_land_diagonal hlength left (fun _ ↦ 1)]
  rw [mixedProduct_land_diagonal hlength (fun _ ↦ 1) right]
  simp only [Nat.mul_one, Nat.one_mul]
  constructor
  · exact diagonalView_injective hlength hleft hright
  · intro hequal
    unfold diagonalView
    apply Finset.sum_congr rfl
    intro index hindex
    change
      left index * (2 ^ width) ^ ((length + 1) * index) =
        right index * (2 ^ width) ^ ((length + 1) * index)
    rw [hequal index (Finset.mem_range.mp hindex)]
  · intro col row _ hrow
    simpa using hright row hrow
  · intro col row hcol _
    simpa using hleft col hcol

theorem leftView_add (length width : ℕ) (left right : ℕ → ℕ) :
    leftView length width left + leftView length width right =
      leftView length width (fun index ↦ left index + right index) := by
  unfold leftView blockExpansion baseExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem rightView_add (length width : ℕ) (left right : ℕ → ℕ) :
    rightView length width left + rightView length width right =
      rightView length width (fun index ↦ left index + right index) := by
  unfold rightView
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem leftView_const (length width constant : ℕ) :
    leftView length width (fun _ ↦ constant) =
      constant * geometricSum length (2 ^ width) := by
  unfold leftView blockExpansion baseExpansion geometricSum
  rw [Finset.mul_sum]

theorem rightView_eq_blockExpansion (length width : ℕ) (digits : ℕ → ℕ) :
    rightView length width digits = blockExpansion length (width * length) digits := by
  unfold rightView blockExpansion baseExpansion
  apply Finset.sum_congr rfl
  intro index _
  rw [pow_mul, pow_mul]

theorem rightView_const (length width constant : ℕ) :
    rightView length width (fun _ ↦ constant) =
      constant * geometricSum length ((2 ^ width) ^ length) := by
  simpa only [rightView_eq_blockExpansion, leftView, pow_mul] using
    leftView_const length (width * length) constant

def leftDigitMask (length digitWidth blockWidth : ℕ) : ℕ :=
  (2 ^ digitWidth - 1) * geometricSum length (2 ^ blockWidth)

def rightDigitMask (length digitWidth blockWidth : ℕ) : ℕ :=
  (2 ^ digitWidth - 1) * geometricSum length ((2 ^ blockWidth) ^ length)

theorem leftDigitMask_eq_leftView (length digitWidth blockWidth : ℕ) :
    leftDigitMask length digitWidth blockWidth =
      leftView length blockWidth (fun _ ↦ 2 ^ digitWidth - 1) := by
  unfold leftDigitMask
  rw [leftView_const]

theorem rightDigitMask_eq_rightView (length digitWidth blockWidth : ℕ) :
    rightDigitMask length digitWidth blockWidth =
      rightView length blockWidth (fun _ ↦ 2 ^ digitWidth - 1) := by
  unfold rightDigitMask
  rw [rightView_const]

theorem leftView_binaryLE_mask {length digitWidth blockWidth : ℕ}
    (hwidth : digitWidth ≤ blockWidth) {digits : ℕ → ℕ}
    (hdigits : ∀ index < length, digits index < 2 ^ digitWidth) :
    binaryLE (leftView length blockWidth digits)
      (leftDigitMask length digitWidth blockWidth) := by
  rw [leftDigitMask_eq_leftView]
  unfold binaryLE leftView
  rw [blockExpansion_land]
  · unfold blockExpansion baseExpansion
    apply Finset.sum_congr rfl
    intro index hindex
    change
      (digits index &&& (2 ^ digitWidth - 1)) * (2 ^ blockWidth) ^ index =
        digits index * (2 ^ blockWidth) ^ index
    rw [Nat.and_two_pow_sub_one_of_lt_two_pow
      (hdigits index (Finset.mem_range.mp hindex))]
  · intro index hindex
    exact (hdigits index hindex).trans_le
      (Nat.pow_le_pow_right (by omega) hwidth)
  · intro index hindex
    have hpow : 2 ^ digitWidth ≤ 2 ^ blockWidth :=
      Nat.pow_le_pow_right (by omega) hwidth
    exact (Nat.sub_lt (by positivity) (by omega)).trans_le hpow

theorem leftView_exists_of_binaryLE_mask {length digitWidth blockWidth code : ℕ}
    (hwidth : digitWidth ≤ blockWidth)
    (hcode : binaryLE code (leftDigitMask length digitWidth blockWidth)) :
    ∃ digits : ℕ → ℕ,
      (∀ index < length, digits index < 2 ^ digitWidth) ∧
        leftView length blockWidth digits = code := by
  have hmaskExpansion :
      leftDigitMask length digitWidth blockWidth =
        blockExpansion length blockWidth (fun _ ↦ 2 ^ digitWidth - 1) := by
    simpa [leftView] using
      leftDigitMask_eq_leftView length digitWidth blockWidth
  have hmaskBound :
      leftDigitMask length digitWidth blockWidth <
        2 ^ (blockWidth * length) := by
    rw [hmaskExpansion]
    apply blockExpansion_lt
    intro index hindex
    have hpow : 2 ^ digitWidth ≤ 2 ^ blockWidth :=
      Nat.pow_le_pow_right (by omega) hwidth
    exact (Nat.sub_lt (by positivity) (by omega)).trans_le hpow
  have hcodeLe : code ≤ leftDigitMask length digitWidth blockWidth := by
    unfold binaryLE at hcode
    rw [← hcode]
    exact Nat.and_le_right
  have hcodeBound : code < (2 ^ blockWidth) ^ length := by
    simpa only [pow_mul] using hcodeLe.trans_lt hmaskBound
  obtain ⟨digits, hdigitBlock, hcodeExpansion⟩ :=
    exists_baseExpansion_of_lt (by positivity) hcodeBound
  have hblockEquality :
      blockExpansion length blockWidth
          (fun index ↦ digits index &&& (2 ^ digitWidth - 1)) =
        blockExpansion length blockWidth digits := by
    unfold binaryLE at hcode
    rw [hmaskExpansion, ← hcodeExpansion] at hcode
    change
      blockExpansion length blockWidth digits &&&
          blockExpansion length blockWidth (fun _ ↦ 2 ^ digitWidth - 1) =
        blockExpansion length blockWidth digits at hcode
    rw [blockExpansion_land] at hcode
    · exact hcode
    · exact hdigitBlock
    · intro index hindex
      have hpow : 2 ^ digitWidth ≤ 2 ^ blockWidth :=
        Nat.pow_le_pow_right (by omega) hwidth
      exact (Nat.sub_lt (by positivity) (by omega)).trans_le hpow
  have hmaskBlock :
      ∀ index < length, 2 ^ digitWidth - 1 < 2 ^ blockWidth := by
    intro index hindex
    have hpow : 2 ^ digitWidth ≤ 2 ^ blockWidth :=
      Nat.pow_le_pow_right (by omega) hwidth
    exact (Nat.sub_lt (by positivity) (by omega)).trans_le hpow
  unfold blockExpansion at hblockEquality
  have hdigitFixed := baseExpansion_unique (base := 2 ^ blockWidth)
    (by positivity)
    (fun index hindex ↦ Nat.and_lt_two_pow _ (hmaskBlock index hindex))
    hdigitBlock hblockEquality
  refine ⟨digits, ?_, ?_⟩
  · intro index hindex
    rw [← hdigitFixed index hindex]
    exact Nat.and_lt_two_pow _ (Nat.sub_lt (by positivity) (by omega))
  · simpa [leftView, blockExpansion] using hcodeExpansion

theorem rightView_binaryLE_mask {length digitWidth blockWidth : ℕ}
    (hlength : 0 < length) (hwidth : digitWidth ≤ blockWidth)
    {digits : ℕ → ℕ}
    (hdigits : ∀ index < length, digits index < 2 ^ digitWidth) :
    binaryLE (rightView length blockWidth digits)
      (rightDigitMask length digitWidth blockWidth) := by
  have htotal : digitWidth ≤ blockWidth * length :=
    hwidth.trans (Nat.le_mul_of_pos_right blockWidth hlength)
  have hleft := leftView_binaryLE_mask (length := length) htotal hdigits
  rw [leftDigitMask_eq_leftView] at hleft
  rw [rightDigitMask_eq_rightView, rightView_eq_blockExpansion,
    rightView_eq_blockExpansion]
  exact hleft

theorem rightView_exists_of_binaryLE_mask
    {length digitWidth blockWidth code : ℕ}
    (hlength : 0 < length) (hwidth : digitWidth ≤ blockWidth)
    (hcode : binaryLE code (rightDigitMask length digitWidth blockWidth)) :
    ∃ digits : ℕ → ℕ,
      (∀ index < length, digits index < 2 ^ digitWidth) ∧
        rightView length blockWidth digits = code := by
  have htotal : digitWidth ≤ blockWidth * length :=
    hwidth.trans (Nat.le_mul_of_pos_right blockWidth hlength)
  have hcode' :
      binaryLE code (leftDigitMask length digitWidth (blockWidth * length)) := by
    simpa [leftDigitMask, rightDigitMask, pow_mul] using hcode
  obtain ⟨digits, hdigits, hleft⟩ :=
    leftView_exists_of_binaryLE_mask htotal hcode'
  refine ⟨digits, hdigits, ?_⟩
  rw [rightView_eq_blockExpansion]
  exact hleft

def cipherBlockWidth (digitWidth : ℕ) : ℕ :=
  2 * digitWidth + 2

theorem digitWidth_le_cipherBlockWidth (digitWidth : ℕ) :
    digitWidth ≤ cipherBlockWidth digitWidth := by
  unfold cipherBlockWidth
  omega

def regularCipher (length digitWidth leftCode rightCode : ℕ) : Prop :=
  let blockWidth := cipherBlockWidth digitWidth
  binaryLE leftCode (leftDigitMask length digitWidth blockWidth) ∧
    binaryLE rightCode (rightDigitMask length digitWidth blockWidth) ∧
    viewsAgree length blockWidth leftCode rightCode

theorem regularCipher_spec {length digitWidth leftCode rightCode : ℕ}
    (hlength : 0 < length) :
    regularCipher length digitWidth leftCode rightCode ↔
      ∃ digits : ℕ → ℕ,
        (∀ index < length, digits index < 2 ^ digitWidth) ∧
          leftView length (cipherBlockWidth digitWidth) digits = leftCode ∧
          rightView length (cipherBlockWidth digitWidth) digits = rightCode := by
  unfold regularCipher
  let blockWidth := cipherBlockWidth digitWidth
  have hwidth : digitWidth ≤ blockWidth :=
    digitWidth_le_cipherBlockWidth digitWidth
  constructor
  · rintro ⟨hleftMask, hrightMask, hagree⟩
    obtain ⟨leftDigits, hleftDigits, hleftCode⟩ :=
      leftView_exists_of_binaryLE_mask hwidth hleftMask
    obtain ⟨rightDigits, hrightDigits, hrightCode⟩ :=
      rightView_exists_of_binaryLE_mask hlength hwidth hrightMask
    have hleftBlock :
        ∀ index < length, leftDigits index < 2 ^ blockWidth := by
      intro index hindex
      exact (hleftDigits index hindex).trans_le
        (Nat.pow_le_pow_right (by omega) hwidth)
    have hrightBlock :
        ∀ index < length, rightDigits index < 2 ^ blockWidth := by
      intro index hindex
      exact (hrightDigits index hindex).trans_le
        (Nat.pow_le_pow_right (by omega) hwidth)
    have hagreeDigits :
        ∀ index < length, leftDigits index = rightDigits index := by
      apply (viewsAgree_spec (width := blockWidth) hlength hleftBlock hrightBlock).mp
      rw [hleftCode, hrightCode]
      exact hagree
    refine ⟨leftDigits, hleftDigits, hleftCode, ?_⟩
    calc
      rightView length blockWidth leftDigits =
          rightView length blockWidth rightDigits := by
        unfold rightView
        apply Finset.sum_congr rfl
        intro index hindex
        rw [hagreeDigits index (Finset.mem_range.mp hindex)]
      _ = rightCode := hrightCode
  · rintro ⟨digits, hdigits, hleftCode, hrightCode⟩
    subst leftCode
    subst rightCode
    refine ⟨leftView_binaryLE_mask hwidth hdigits,
      rightView_binaryLE_mask hlength hwidth hdigits, ?_⟩
    have hdigitBlock :
        ∀ index < length, digits index < 2 ^ blockWidth := by
      intro index hindex
      exact (hdigits index hindex).trans_le
        (Nat.pow_le_pow_right (by omega) hwidth)
    exact (viewsAgree_spec (width := blockWidth) hlength hdigitBlock hdigitBlock).mpr
      fun _ _ ↦ rfl

theorem regularCipher_dioph {α : Type}
    {length digitWidth leftCode rightCode : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hdigitWidth : DiophFn digitWidth)
    (hleftCode : DiophFn leftCode) (hrightCode : DiophFn rightCode) :
    Dioph fun values ↦
      regularCipher (length values) (digitWidth values)
        (leftCode values) (rightCode values) := by
  let blockWidth : (α → ℕ) → ℕ := fun values ↦
    cipherBlockWidth (digitWidth values)
  let radix : (α → ℕ) → ℕ := fun values ↦
    2 ^ blockWidth values
  let digitBase : (α → ℕ) → ℕ := fun values ↦
    2 ^ digitWidth values
  let leftOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (radix values)
  let rightBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ length values
  let rightOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (rightBase values)
  let diagonalBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ (length values + 1)
  let diagonalOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (diagonalBase values)
  let leftMask : (α → ℕ) → ℕ := fun values ↦
    (digitBase values - 1) * leftOnes values
  let rightMask : (α → ℕ) → ℕ := fun values ↦
    (digitBase values - 1) * rightOnes values
  let diagonalBlockMask : (α → ℕ) → ℕ := fun values ↦
    (radix values - 1) * diagonalOnes values
  have hblockWidth : DiophFn blockWidth := by
    unfold blockWidth cipherBlockWidth
    exact ((Dioph.const_dioph 2 D* hdigitWidth) D+ Dioph.const_dioph 2)
  have hradix : DiophFn radix := by
    unfold radix
    exact Dioph.pow_dioph (Dioph.const_dioph 2) hblockWidth
  have hdigitBase : DiophFn digitBase := by
    unfold digitBase
    exact Dioph.pow_dioph (Dioph.const_dioph 2) hdigitWidth
  have hleftOnes : DiophFn leftOnes := by
    unfold leftOnes
    exact geometricSum_comp_diophFn hlength hradix
  have hrightBase : DiophFn rightBase := by
    unfold rightBase
    exact Dioph.pow_dioph hradix hlength
  have hrightOnes : DiophFn rightOnes := by
    unfold rightOnes
    exact geometricSum_comp_diophFn hlength hrightBase
  have hdiagonalBase : DiophFn diagonalBase := by
    unfold diagonalBase
    exact Dioph.pow_dioph hradix (hlength D+ Dioph.const_dioph 1)
  have hdiagonalOnes : DiophFn diagonalOnes := by
    unfold diagonalOnes
    exact geometricSum_comp_diophFn hlength hdiagonalBase
  have hleftMask : DiophFn leftMask := by
    unfold leftMask
    exact (hdigitBase D- Dioph.const_dioph 1) D* hleftOnes
  have hrightMask : DiophFn rightMask := by
    unfold rightMask
    exact (hdigitBase D- Dioph.const_dioph 1) D* hrightOnes
  have hdiagonalBlockMask : DiophFn diagonalBlockMask := by
    unfold diagonalBlockMask
    exact (hradix D- Dioph.const_dioph 1) D* hdiagonalOnes
  have hleftProduct :
      DiophFn fun values ↦ leftCode values * rightOnes values :=
    hleftCode D* hrightOnes
  have hrightProduct :
      DiophFn fun values ↦ leftOnes values * rightCode values :=
    hleftOnes D* hrightCode
  have hleftDiagonal :
      DiophFn fun values ↦
        (leftCode values * rightOnes values) &&& diagonalBlockMask values :=
    land_diophFn hleftProduct hdiagonalBlockMask
  have hrightDiagonal :
      DiophFn fun values ↦
        (leftOnes values * rightCode values) &&& diagonalBlockMask values :=
    land_diophFn hrightProduct hdiagonalBlockMask
  have hrelation :
      Dioph fun values ↦
        binaryLE (leftCode values) (leftMask values) ∧
          binaryLE (rightCode values) (rightMask values) ∧
          (leftCode values * rightOnes values &&& diagonalBlockMask values) =
            (leftOnes values * rightCode values &&& diagonalBlockMask values) :=
    (binaryLE_dioph hleftCode hleftMask) D∧
      ((binaryLE_dioph hrightCode hrightMask) D∧
        (hleftDiagonal D= hrightDiagonal))
  apply Dioph.ext hrelation
  intro values
  simp only [regularCipher, viewsAgree, leftDigitMask, rightDigitMask,
    diagonalMask, blockWidth, radix, digitBase, leftOnes, rightBase,
    rightOnes, diagonalBase, diagonalOnes, leftMask, rightMask,
    diagonalBlockMask, leftView_const, rightView_const, Nat.one_mul]

end TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher
