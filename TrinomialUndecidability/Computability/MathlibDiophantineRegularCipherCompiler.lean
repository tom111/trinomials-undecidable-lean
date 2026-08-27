import TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherFormula

/-!
# Bounded universal quantification via two-view regular ciphers

This module compiles mathlib's proof-valued integer polynomials into signed pointwise cipher
circuits.  It proves both directions of the cipher semantics, constructs a sufficient finite digit
width, packs one independent Diophantine witness sequence for every bounded index, and derives
closure of arbitrary Diophantine relations under bounded universal quantification.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherCompiler

open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherOps
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherFormula
open TrinomialUndecidability.Computability.MathlibDiophantineBinary
open TrinomialUndecidability.Computability.MathlibDiophantineBitwise

open Dioph Fin2 Nat Vector3
open scoped BigOperators Dioph Vector3

inductive PolyExpr (α : Type) where
  | var (index : α)
  | const (value : ℤ)
  | sub (left right : PolyExpr α)
  | mul (left right : PolyExpr α)

namespace PolyExpr

def eval {index : Type} (assignment : index → ℕ) : PolyExpr index → ℤ
  | .var symbol => Int.ofNat (assignment symbol)
  | .const value => value
  | .sub left right => left.eval assignment - right.eval assignment
  | .mul left right => left.eval assignment * right.eval assignment

mutual
  def positive {index : Type} (assignment : index → ℕ) : PolyExpr index → ℕ
    | .var symbol => assignment symbol
    | .const value => value.toNat
    | .sub left right => left.positive assignment + right.negative assignment
    | .mul left right =>
        left.positive assignment * right.positive assignment +
          left.negative assignment * right.negative assignment

  def negative {index : Type} (assignment : index → ℕ) : PolyExpr index → ℕ
    | .var _ => 0
    | .const value => (-value).toNat
    | .sub left right => left.negative assignment + right.positive assignment
    | .mul left right =>
        left.positive assignment * right.negative assignment +
          left.negative assignment * right.positive assignment
end

theorem int_eq_positive_sub_negative {index : Type} (expression : PolyExpr index)
    (assignment : index → ℕ) :
    expression.eval assignment =
      Int.ofNat (expression.positive assignment) -
        Int.ofNat (expression.negative assignment) := by
  induction expression with
  | var symbol => simp [eval, positive, negative]
  | const value => exact (Int.toNat_sub_toNat_neg value).symm
  | sub left right ihLeft ihRight =>
      simp only [eval, positive, negative, ihLeft, ihRight,
        Int.ofNat_eq_natCast, Int.natCast_add]
      ring
  | mul left right ihLeft ihRight =>
      simp only [eval, positive, negative, ihLeft, ihRight,
        Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
      ring

def CipherRelation {index : Type} (length digitWidth : ℕ)
    (inputLeft inputRight : index → ℕ) :
    PolyExpr index → ℕ → ℕ → ℕ → ℕ → Prop
  | .var symbol, positiveLeft, positiveRight, negativeLeft, negativeRight =>
      positiveLeft = inputLeft symbol ∧
        positiveRight = inputRight symbol ∧
        regularCipher length digitWidth positiveLeft positiveRight ∧
        regularCipherConst length digitWidth 0 negativeLeft negativeRight ∧
        regularCipher length digitWidth negativeLeft negativeRight
  | .const value, positiveLeft, positiveRight, negativeLeft, negativeRight =>
      value.toNat < 2 ^ digitWidth ∧
        (-value).toNat < 2 ^ digitWidth ∧
        regularCipherConst length digitWidth value.toNat positiveLeft positiveRight ∧
        regularCipher length digitWidth positiveLeft positiveRight ∧
        regularCipherConst length digitWidth (-value).toNat negativeLeft negativeRight ∧
        regularCipher length digitWidth negativeLeft negativeRight
  | .sub left right, positiveLeft, positiveRight, negativeLeft, negativeRight =>
      ∃ codes : Fin 8 → ℕ,
        CipherRelation length digitWidth inputLeft inputRight left
            (codes 0) (codes 1) (codes 2) (codes 3) ∧
          CipherRelation length digitWidth inputLeft inputRight right
            (codes 4) (codes 5) (codes 6) (codes 7) ∧
          regularCipherAdd (codes 0) (codes 1) (codes 6) (codes 7)
            positiveLeft positiveRight ∧
          regularCipher length digitWidth positiveLeft positiveRight ∧
          regularCipherAdd (codes 2) (codes 3) (codes 4) (codes 5)
            negativeLeft negativeRight ∧
          regularCipher length digitWidth negativeLeft negativeRight
  | .mul left right, positiveLeft, positiveRight, negativeLeft, negativeRight =>
      ∃ codes : Fin 16 → ℕ,
        CipherRelation length digitWidth inputLeft inputRight left
            (codes 0) (codes 1) (codes 2) (codes 3) ∧
          CipherRelation length digitWidth inputLeft inputRight right
            (codes 4) (codes 5) (codes 6) (codes 7) ∧
          regularCipherMul length digitWidth (codes 0) (codes 5) (codes 8) ∧
          regularCipher length digitWidth (codes 8) (codes 9) ∧
          regularCipherMul length digitWidth (codes 2) (codes 7) (codes 10) ∧
          regularCipher length digitWidth (codes 10) (codes 11) ∧
          regularCipherMul length digitWidth (codes 0) (codes 7) (codes 12) ∧
          regularCipher length digitWidth (codes 12) (codes 13) ∧
          regularCipherMul length digitWidth (codes 2) (codes 5) (codes 14) ∧
          regularCipher length digitWidth (codes 14) (codes 15) ∧
          regularCipherAdd (codes 8) (codes 9) (codes 10) (codes 11)
            positiveLeft positiveRight ∧
          regularCipher length digitWidth positiveLeft positiveRight ∧
          regularCipherAdd (codes 12) (codes 13) (codes 14) (codes 15)
            negativeLeft negativeRight ∧
          regularCipher length digitWidth negativeLeft negativeRight

def decodeDigit (digitWidth leftCode index : ℕ) : ℕ :=
  let radix := 2 ^ cipherBlockWidth digitWidth
  leftCode / radix ^ index % radix

structure CipherDigits (length digitWidth leftCode rightCode : ℕ) where
  digits : ℕ → ℕ
  bound : ∀ index < length, digits index < 2 ^ digitWidth
  leftCode_eq :
    leftView length (cipherBlockWidth digitWidth) digits = leftCode
  rightCode_eq :
    rightView length (cipherBlockWidth digitWidth) digits = rightCode

theorem exists_cipherDigits_of_regularCipher {length digitWidth leftCode rightCode : ℕ}
    (hlength : 0 < length)
    (hcipher : regularCipher length digitWidth leftCode rightCode) :
    Nonempty (CipherDigits length digitWidth leftCode rightCode) := by
  obtain ⟨digits, hbound, hleft, hright⟩ :=
    (regularCipher_spec hlength).mp hcipher
  exact ⟨⟨digits, hbound, hleft, hright⟩⟩

theorem CipherDigits.decodeDigit_eq {length digitWidth leftCode rightCode : ℕ}
    (cipher : CipherDigits length digitWidth leftCode rightCode)
    {index : ℕ} (hindex : index < length) :
    decodeDigit digitWidth leftCode index = cipher.digits index := by
  have hdigit :
      leftView length (cipherBlockWidth digitWidth) cipher.digits /
            (2 ^ cipherBlockWidth digitWidth) ^ index %
          (2 ^ cipherBlockWidth digitWidth) =
        cipher.digits index := by
    unfold leftView blockExpansion
    rw [baseExpansion_digit hindex (by positivity)]
    · exact Nat.mod_eq_of_lt ((cipher.bound index hindex).trans_le
        (Nat.pow_le_pow_right (by omega)
          (digitWidth_le_cipherBlockWidth digitWidth)))
    · intro position hposition
      exact (cipher.bound position (hposition.trans hindex)).trans_le
        (Nat.pow_le_pow_right (by omega)
          (digitWidth_le_cipherBlockWidth digitWidth))
  unfold decodeDigit
  exact (congrArg
    (fun code ↦
      code / (2 ^ cipherBlockWidth digitWidth) ^ index %
        (2 ^ cipherBlockWidth digitWidth))
    cipher.leftCode_eq.symm).trans hdigit

def constantCipherDigits {length digitWidth constant leftCode rightCode : ℕ}
    (hbound : constant < 2 ^ digitWidth)
    (hcipher : regularCipherConst length digitWidth constant leftCode rightCode) :
    CipherDigits length digitWidth leftCode rightCode := by
  refine {
    digits := fun _ ↦ constant
    bound := fun _ _ ↦ hbound
    leftCode_eq := ?_
    rightCode_eq := ?_
  }
  · exact (regularCipherConst_spec.mp hcipher).1
  · exact (regularCipherConst_spec.mp hcipher).2

theorem cipherRelation_sound {index : Type} (expression : PolyExpr index)
    {length digitWidth : ℕ} (hlength : 0 < length)
    {inputLeft inputRight : index → ℕ}
    {positiveLeft positiveRight negativeLeft negativeRight : ℕ}
    (hrelation : CipherRelation length digitWidth inputLeft inputRight expression
      positiveLeft positiveRight negativeLeft negativeRight) :
    ∃ positive : CipherDigits length digitWidth positiveLeft positiveRight,
      ∃ negative : CipherDigits length digitWidth negativeLeft negativeRight,
        ∀ position < length,
          Int.ofNat (positive.digits position) -
              Int.ofNat (negative.digits position) =
            expression.eval (fun symbol ↦
              decodeDigit digitWidth (inputLeft symbol) position) := by
  induction expression generalizing positiveLeft positiveRight
      negativeLeft negativeRight with
  | var symbol =>
      rcases hrelation with
        ⟨hpositiveLeft, hpositiveRight, hpositiveCipher,
          hnegativeConst, hnegativeCipher⟩
      obtain ⟨positive⟩ :=
        exists_cipherDigits_of_regularCipher hlength hpositiveCipher
      let negative : CipherDigits length digitWidth negativeLeft negativeRight :=
        constantCipherDigits (by positivity) hnegativeConst
      refine ⟨positive, negative, ?_⟩
      intro position hposition
      have hdigit :
          positive.digits position =
            decodeDigit digitWidth (inputLeft symbol) position := by
        rw [← positive.decodeDigit_eq hposition, hpositiveLeft]
      change
        Int.ofNat (positive.digits position) - Int.ofNat 0 =
          Int.ofNat (decodeDigit digitWidth (inputLeft symbol) position)
      simpa only [Int.ofNat_eq_natCast, Int.natCast_zero, Int.sub_zero] using
        congrArg Int.ofNat hdigit
  | const value =>
      rcases hrelation with
        ⟨hpositiveBound, hnegativeBound, hpositiveConst, hpositiveCipher,
          hnegativeConst, hnegativeCipher⟩
      let positive : CipherDigits length digitWidth positiveLeft positiveRight :=
        constantCipherDigits hpositiveBound hpositiveConst
      let negative : CipherDigits length digitWidth negativeLeft negativeRight :=
        constantCipherDigits hnegativeBound hnegativeConst
      refine ⟨positive, negative, ?_⟩
      intro position hposition
      change Int.ofNat value.toNat - Int.ofNat (-value).toNat = value
      exact Int.toNat_sub_toNat_neg value
  | sub left right ihLeft ihRight =>
      obtain ⟨codes, hleft, hright, haddPositive, hpositiveCipher,
        haddNegative, hnegativeCipher⟩ := hrelation
      obtain ⟨leftPositive, leftNegative, hleftEval⟩ := ihLeft hleft
      obtain ⟨rightPositive, rightNegative, hrightEval⟩ := ihRight hright
      obtain ⟨positive⟩ :=
        exists_cipherDigits_of_regularCipher hlength hpositiveCipher
      obtain ⟨negative⟩ :=
        exists_cipherDigits_of_regularCipher hlength hnegativeCipher
      have hpositiveDigits := (regularCipherAdd_spec
        leftPositive.bound rightNegative.bound positive.bound
        leftPositive.leftCode_eq leftPositive.rightCode_eq
        rightNegative.leftCode_eq rightNegative.rightCode_eq
        positive.leftCode_eq positive.rightCode_eq).mp haddPositive
      have hnegativeDigits := (regularCipherAdd_spec
        leftNegative.bound rightPositive.bound negative.bound
        leftNegative.leftCode_eq leftNegative.rightCode_eq
        rightPositive.leftCode_eq rightPositive.rightCode_eq
        negative.leftCode_eq negative.rightCode_eq).mp haddNegative
      refine ⟨positive, negative, ?_⟩
      intro position hposition
      rw [hpositiveDigits position hposition, hnegativeDigits position hposition]
      rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast,
        Int.natCast_add, Int.natCast_add]
      have hleftValue := hleftEval position hposition
      have hrightValue := hrightEval position hposition
      simp only [Int.ofNat_eq_natCast] at hleftValue hrightValue
      simp only [eval]
      rw [← hleftValue, ← hrightValue]
      ring
  | mul left right ihLeft ihRight =>
      obtain ⟨codes, hleft, hright, hmulPP, hregularPP, hmulNN,
        hregularNN, hmulPN, hregularPN, hmulNP, hregularNP,
        haddPositive, hpositiveCipher, haddNegative, hnegativeCipher⟩ := hrelation
      obtain ⟨leftPositive, leftNegative, hleftEval⟩ := ihLeft hleft
      obtain ⟨rightPositive, rightNegative, hrightEval⟩ := ihRight hright
      obtain ⟨productPP⟩ :=
        exists_cipherDigits_of_regularCipher hlength hregularPP
      obtain ⟨productNN⟩ :=
        exists_cipherDigits_of_regularCipher hlength hregularNN
      obtain ⟨productPN⟩ :=
        exists_cipherDigits_of_regularCipher hlength hregularPN
      obtain ⟨productNP⟩ :=
        exists_cipherDigits_of_regularCipher hlength hregularNP
      obtain ⟨positive⟩ :=
        exists_cipherDigits_of_regularCipher hlength hpositiveCipher
      obtain ⟨negative⟩ :=
        exists_cipherDigits_of_regularCipher hlength hnegativeCipher
      have hproductPP := (regularCipherMul_spec hlength
        leftPositive.bound rightPositive.bound productPP.bound
        leftPositive.leftCode_eq rightPositive.rightCode_eq
        productPP.leftCode_eq).mp hmulPP
      have hproductNN := (regularCipherMul_spec hlength
        leftNegative.bound rightNegative.bound productNN.bound
        leftNegative.leftCode_eq rightNegative.rightCode_eq
        productNN.leftCode_eq).mp hmulNN
      have hproductPN := (regularCipherMul_spec hlength
        leftPositive.bound rightNegative.bound productPN.bound
        leftPositive.leftCode_eq rightNegative.rightCode_eq
        productPN.leftCode_eq).mp hmulPN
      have hproductNP := (regularCipherMul_spec hlength
        leftNegative.bound rightPositive.bound productNP.bound
        leftNegative.leftCode_eq rightPositive.rightCode_eq
        productNP.leftCode_eq).mp hmulNP
      have hpositiveDigits := (regularCipherAdd_spec
        productPP.bound productNN.bound positive.bound
        productPP.leftCode_eq productPP.rightCode_eq
        productNN.leftCode_eq productNN.rightCode_eq
        positive.leftCode_eq positive.rightCode_eq).mp haddPositive
      have hnegativeDigits := (regularCipherAdd_spec
        productPN.bound productNP.bound negative.bound
        productPN.leftCode_eq productPN.rightCode_eq
        productNP.leftCode_eq productNP.rightCode_eq
        negative.leftCode_eq negative.rightCode_eq).mp haddNegative
      refine ⟨positive, negative, ?_⟩
      intro position hposition
      rw [hpositiveDigits position hposition, hnegativeDigits position hposition]
      rw [hproductPP position hposition, hproductNN position hposition,
        hproductPN position hposition, hproductNP position hposition]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
      have hleftValue := hleftEval position hposition
      have hrightValue := hrightEval position hposition
      simp only [Int.ofNat_eq_natCast] at hleftValue hrightValue
      simp only [eval]
      rw [← hleftValue, ← hrightValue]
      ring

def Fits {index : Type} (digitWidth : ℕ) (assignment : index → ℕ) :
    PolyExpr index → Prop
  | .var symbol => assignment symbol < 2 ^ digitWidth
  | .const value =>
      value.toNat < 2 ^ digitWidth ∧ (-value).toNat < 2 ^ digitWidth
  | .sub left right =>
      left.Fits digitWidth assignment ∧
        right.Fits digitWidth assignment ∧
        (left.sub right).positive assignment < 2 ^ digitWidth ∧
        (left.sub right).negative assignment < 2 ^ digitWidth
  | .mul left right =>
      left.Fits digitWidth assignment ∧
        right.Fits digitWidth assignment ∧
        (left.mul right).positive assignment < 2 ^ digitWidth ∧
        (left.mul right).negative assignment < 2 ^ digitWidth

theorem Fits.positive_lt {index : Type} {digitWidth : ℕ}
    {assignment : index → ℕ} {expression : PolyExpr index}
    (hfits : expression.Fits digitWidth assignment) :
    expression.positive assignment < 2 ^ digitWidth := by
  cases expression <;> simp [Fits, positive] at hfits ⊢
  · exact hfits
  · exact hfits.1
  · exact hfits.2.2.1
  · exact hfits.2.2.1

theorem Fits.negative_lt {index : Type} {digitWidth : ℕ}
    {assignment : index → ℕ} {expression : PolyExpr index}
    (hfits : expression.Fits digitWidth assignment) :
    expression.negative assignment < 2 ^ digitWidth := by
  cases expression with
  | var symbol =>
      simp only [negative]
      positivity
  | const value => exact hfits.2
  | sub left right => exact hfits.2.2.2
  | mul left right => exact hfits.2.2.2

theorem regularCipher_of_digits {length digitWidth : ℕ} (hlength : 0 < length)
    (digits : ℕ → ℕ)
    (hbound : ∀ position < length, digits position < 2 ^ digitWidth) :
    regularCipher length digitWidth
      (leftView length (cipherBlockWidth digitWidth) digits)
      (rightView length (cipherBlockWidth digitWidth) digits) :=
  (regularCipher_spec hlength).mpr ⟨digits, hbound, rfl, rfl⟩

theorem regularCipherConst_of_digits (length digitWidth constant : ℕ) :
    regularCipherConst length digitWidth constant
      (leftView length (cipherBlockWidth digitWidth) (fun _ ↦ constant))
      (rightView length (cipherBlockWidth digitWidth) (fun _ ↦ constant)) :=
  regularCipherConst_spec.mpr ⟨rfl, rfl⟩

theorem cipherRelation_complete {index : Type} (expression : PolyExpr index)
    {length digitWidth : ℕ} (hlength : 0 < length)
    (digits : index → ℕ → ℕ) {inputLeft inputRight : index → ℕ}
    (hinputLeft : ∀ symbol,
      leftView length (cipherBlockWidth digitWidth) (digits symbol) = inputLeft symbol)
    (hinputRight : ∀ symbol,
      rightView length (cipherBlockWidth digitWidth) (digits symbol) = inputRight symbol)
    (hfits : ∀ position < length,
      expression.Fits digitWidth (fun symbol ↦ digits symbol position)) :
    CipherRelation length digitWidth inputLeft inputRight expression
      (leftView length (cipherBlockWidth digitWidth)
        (fun position ↦ expression.positive (fun symbol ↦ digits symbol position)))
      (rightView length (cipherBlockWidth digitWidth)
        (fun position ↦ expression.positive (fun symbol ↦ digits symbol position)))
      (leftView length (cipherBlockWidth digitWidth)
        (fun position ↦ expression.negative (fun symbol ↦ digits symbol position)))
      (rightView length (cipherBlockWidth digitWidth)
        (fun position ↦ expression.negative (fun symbol ↦ digits symbol position))) := by
  induction expression with
  | var symbol =>
      have hbound : ∀ position < length,
          digits symbol position < 2 ^ digitWidth := by
        intro position hposition
        exact hfits position hposition
      refine ⟨hinputLeft symbol, hinputRight symbol, ?_, ?_, ?_⟩
      · exact regularCipher_of_digits hlength (digits symbol) hbound
      · exact regularCipherConst_of_digits length digitWidth 0
      · exact regularCipher_of_digits hlength (fun _ ↦ 0)
          (fun _ _ ↦ Nat.two_pow_pos digitWidth)
  | const value =>
      have hconstant := hfits 0 hlength
      refine ⟨hconstant.1, hconstant.2, ?_, ?_, ?_, ?_⟩
      · exact regularCipherConst_of_digits length digitWidth value.toNat
      · exact regularCipher_of_digits hlength (fun _ ↦ value.toNat)
          (fun _ _ ↦ hconstant.1)
      · exact regularCipherConst_of_digits length digitWidth (-value).toNat
      · exact regularCipher_of_digits hlength (fun _ ↦ (-value).toNat)
          (fun _ _ ↦ hconstant.2)
  | sub left right ihLeft ihRight =>
      let leftPositive : ℕ → ℕ := fun position ↦
        left.positive (fun symbol ↦ digits symbol position)
      let leftNegative : ℕ → ℕ := fun position ↦
        left.negative (fun symbol ↦ digits symbol position)
      let rightPositive : ℕ → ℕ := fun position ↦
        right.positive (fun symbol ↦ digits symbol position)
      let rightNegative : ℕ → ℕ := fun position ↦
        right.negative (fun symbol ↦ digits symbol position)
      let outputPositive : ℕ → ℕ := fun position ↦
        (left.sub right).positive (fun symbol ↦ digits symbol position)
      let outputNegative : ℕ → ℕ := fun position ↦
        (left.sub right).negative (fun symbol ↦ digits symbol position)
      have hleftFits : ∀ position < length,
          left.Fits digitWidth (fun symbol ↦ digits symbol position) :=
        fun position hposition ↦ (hfits position hposition).1
      have hrightFits : ∀ position < length,
          right.Fits digitWidth (fun symbol ↦ digits symbol position) :=
        fun position hposition ↦ (hfits position hposition).2.1
      have hleft := ihLeft hleftFits
      have hright := ihRight hrightFits
      have hleftPositiveBound : ∀ position < length,
          leftPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hleftFits position hposition).positive_lt
      have hleftNegativeBound : ∀ position < length,
          leftNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hleftFits position hposition).negative_lt
      have hrightPositiveBound : ∀ position < length,
          rightPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hrightFits position hposition).positive_lt
      have hrightNegativeBound : ∀ position < length,
          rightNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hrightFits position hposition).negative_lt
      have houtputPositiveBound : ∀ position < length,
          outputPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hfits position hposition).positive_lt
      have houtputNegativeBound : ∀ position < length,
          outputNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hfits position hposition).negative_lt
      let codes : Fin 8 → ℕ := ![
        leftView length (cipherBlockWidth digitWidth) leftPositive,
        rightView length (cipherBlockWidth digitWidth) leftPositive,
        leftView length (cipherBlockWidth digitWidth) leftNegative,
        rightView length (cipherBlockWidth digitWidth) leftNegative,
        leftView length (cipherBlockWidth digitWidth) rightPositive,
        rightView length (cipherBlockWidth digitWidth) rightPositive,
        leftView length (cipherBlockWidth digitWidth) rightNegative,
        rightView length (cipherBlockWidth digitWidth) rightNegative]
      refine ⟨codes, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hleft
      · exact hright
      · exact (regularCipherAdd_spec hleftPositiveBound hrightNegativeBound
          houtputPositiveBound rfl rfl rfl rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength outputPositive houtputPositiveBound
      · exact (regularCipherAdd_spec hleftNegativeBound hrightPositiveBound
          houtputNegativeBound rfl rfl rfl rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength outputNegative houtputNegativeBound
  | mul left right ihLeft ihRight =>
      let leftPositive : ℕ → ℕ := fun position ↦
        left.positive (fun symbol ↦ digits symbol position)
      let leftNegative : ℕ → ℕ := fun position ↦
        left.negative (fun symbol ↦ digits symbol position)
      let rightPositive : ℕ → ℕ := fun position ↦
        right.positive (fun symbol ↦ digits symbol position)
      let rightNegative : ℕ → ℕ := fun position ↦
        right.negative (fun symbol ↦ digits symbol position)
      let productPP : ℕ → ℕ := fun position ↦
        leftPositive position * rightPositive position
      let productNN : ℕ → ℕ := fun position ↦
        leftNegative position * rightNegative position
      let productPN : ℕ → ℕ := fun position ↦
        leftPositive position * rightNegative position
      let productNP : ℕ → ℕ := fun position ↦
        leftNegative position * rightPositive position
      let outputPositive : ℕ → ℕ := fun position ↦
        (left.mul right).positive (fun symbol ↦ digits symbol position)
      let outputNegative : ℕ → ℕ := fun position ↦
        (left.mul right).negative (fun symbol ↦ digits symbol position)
      have hleftFits : ∀ position < length,
          left.Fits digitWidth (fun symbol ↦ digits symbol position) :=
        fun position hposition ↦ (hfits position hposition).1
      have hrightFits : ∀ position < length,
          right.Fits digitWidth (fun symbol ↦ digits symbol position) :=
        fun position hposition ↦ (hfits position hposition).2.1
      have hleft := ihLeft hleftFits
      have hright := ihRight hrightFits
      have hleftPositiveBound : ∀ position < length,
          leftPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hleftFits position hposition).positive_lt
      have hleftNegativeBound : ∀ position < length,
          leftNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hleftFits position hposition).negative_lt
      have hrightPositiveBound : ∀ position < length,
          rightPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hrightFits position hposition).positive_lt
      have hrightNegativeBound : ∀ position < length,
          rightNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hrightFits position hposition).negative_lt
      have hproductPPBound : ∀ position < length,
          productPP position < 2 ^ digitWidth := by
        intro position hposition
        exact Nat.lt_of_le_of_lt
          (Nat.le_add_right (productPP position) (productNN position))
          (hfits position hposition).positive_lt
      have hproductNNBound : ∀ position < length,
          productNN position < 2 ^ digitWidth := by
        intro position hposition
        exact (Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
          (hfits position hposition).positive_lt)
      have hproductPNBound : ∀ position < length,
          productPN position < 2 ^ digitWidth := by
        intro position hposition
        exact Nat.lt_of_le_of_lt
          (Nat.le_add_right (productPN position) (productNP position))
          (hfits position hposition).negative_lt
      have hproductNPBound : ∀ position < length,
          productNP position < 2 ^ digitWidth := by
        intro position hposition
        exact (Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
          (hfits position hposition).negative_lt)
      have houtputPositiveBound : ∀ position < length,
          outputPositive position < 2 ^ digitWidth :=
        fun position hposition ↦ (hfits position hposition).positive_lt
      have houtputNegativeBound : ∀ position < length,
          outputNegative position < 2 ^ digitWidth :=
        fun position hposition ↦ (hfits position hposition).negative_lt
      let codes : Fin 16 → ℕ := ![
        leftView length (cipherBlockWidth digitWidth) leftPositive,
        rightView length (cipherBlockWidth digitWidth) leftPositive,
        leftView length (cipherBlockWidth digitWidth) leftNegative,
        rightView length (cipherBlockWidth digitWidth) leftNegative,
        leftView length (cipherBlockWidth digitWidth) rightPositive,
        rightView length (cipherBlockWidth digitWidth) rightPositive,
        leftView length (cipherBlockWidth digitWidth) rightNegative,
        rightView length (cipherBlockWidth digitWidth) rightNegative,
        leftView length (cipherBlockWidth digitWidth) productPP,
        rightView length (cipherBlockWidth digitWidth) productPP,
        leftView length (cipherBlockWidth digitWidth) productNN,
        rightView length (cipherBlockWidth digitWidth) productNN,
        leftView length (cipherBlockWidth digitWidth) productPN,
        rightView length (cipherBlockWidth digitWidth) productPN,
        leftView length (cipherBlockWidth digitWidth) productNP,
        rightView length (cipherBlockWidth digitWidth) productNP]
      refine ⟨codes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hleft
      · exact hright
      · exact (regularCipherMul_spec hlength hleftPositiveBound
          hrightPositiveBound hproductPPBound rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength productPP hproductPPBound
      · exact (regularCipherMul_spec hlength hleftNegativeBound
          hrightNegativeBound hproductNNBound rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength productNN hproductNNBound
      · exact (regularCipherMul_spec hlength hleftPositiveBound
          hrightNegativeBound hproductPNBound rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength productPN hproductPNBound
      · exact (regularCipherMul_spec hlength hleftNegativeBound
          hrightPositiveBound hproductNPBound rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength productNP hproductNPBound
      · exact (regularCipherAdd_spec hproductPPBound hproductNNBound
          houtputPositiveBound rfl rfl rfl rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength outputPositive houtputPositiveBound
      · exact (regularCipherAdd_spec hproductPNBound hproductNPBound
          houtputNegativeBound rfl rfl rfl rfl rfl rfl).mpr fun _ _ ↦ rfl
      · exact regularCipher_of_digits hlength outputNegative houtputNegativeBound

def magnitude {index : Type} (assignment : index → ℕ) : PolyExpr index → ℕ
  | .var symbol => assignment symbol
  | .const value => max value.toNat (-value).toNat
  | .sub left right =>
      max (max (left.magnitude assignment) (right.magnitude assignment))
        (max ((left.sub right).positive assignment)
          ((left.sub right).negative assignment))
  | .mul left right =>
      max (max (left.magnitude assignment) (right.magnitude assignment))
        (max ((left.mul right).positive assignment)
          ((left.mul right).negative assignment))

theorem fits_of_magnitude_lt {index : Type} {digitWidth : ℕ}
    (expression : PolyExpr index) (assignment : index → ℕ)
    (hbound : expression.magnitude assignment < 2 ^ digitWidth) :
    expression.Fits digitWidth assignment := by
  induction expression with
  | var symbol => exact hbound
  | const value =>
      exact ⟨(Nat.le_max_left _ _).trans_lt hbound,
        (Nat.le_max_right _ _).trans_lt hbound⟩
  | sub left right ihLeft ihRight =>
      refine ⟨ihLeft ?_, ihRight ?_, ?_, ?_⟩
      · exact (show left.magnitude assignment ≤
          (left.sub right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show right.magnitude assignment ≤
          (left.sub right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show (left.sub right).positive assignment ≤
          (left.sub right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show (left.sub right).negative assignment ≤
          (left.sub right).magnitude assignment by simp [magnitude]).trans_lt hbound
  | mul left right ihLeft ihRight =>
      refine ⟨ihLeft ?_, ihRight ?_, ?_, ?_⟩
      · exact (show left.magnitude assignment ≤
          (left.mul right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show right.magnitude assignment ≤
          (left.mul right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show (left.mul right).positive assignment ≤
          (left.mul right).magnitude assignment by simp [magnitude]).trans_lt hbound
      · exact (show (left.mul right).negative assignment ≤
          (left.mul right).magnitude assignment by simp [magnitude]).trans_lt hbound

def requiredDigitWidth {index : Type} (length : ℕ) (expression : PolyExpr index)
    (digits : index → ℕ → ℕ) : ℕ :=
  ∑ position ∈ Finset.range length,
    expression.magnitude (fun symbol ↦ digits symbol position)

theorem fits_requiredDigitWidth {index : Type} {length : ℕ}
    (expression : PolyExpr index) (digits : index → ℕ → ℕ) :
    ∀ position < length,
      expression.Fits (requiredDigitWidth length expression digits)
        (fun symbol ↦ digits symbol position) := by
  intro position hposition
  let value := expression.magnitude (fun symbol ↦ digits symbol position)
  have hvalueWidth : value ≤ requiredDigitWidth length expression digits := by
    unfold requiredDigitWidth
    change
      expression.magnitude (fun symbol ↦ digits symbol position) ≤
        ∑ candidate ∈ Finset.range length,
          expression.magnitude (fun symbol ↦ digits symbol candidate)
    exact Finset.single_le_sum
      (f := fun candidate ↦
        expression.magnitude (fun symbol ↦ digits symbol candidate))
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hposition)
  apply fits_of_magnitude_lt
  exact value.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by omega) hvalueWidth)

theorem exists_polyExpr {index : Type} (polynomial : Poly index) :
    ∃ expression : PolyExpr index,
      ∀ assignment, expression.eval assignment = polynomial assignment := by
  apply Poly.induction
    (C := fun candidate ↦
      ∃ expression : PolyExpr index,
        ∀ assignment, expression.eval assignment = candidate assignment)
  · intro symbol
    exact ⟨.var symbol, fun _ ↦ rfl⟩
  · intro value
    exact ⟨.const value, fun _ ↦ rfl⟩
  · rintro left right ⟨leftExpression, hleft⟩
      ⟨rightExpression, hright⟩
    refine ⟨leftExpression.sub rightExpression, ?_⟩
    intro assignment
    simp only [eval, Poly.sub_apply, hleft, hright]
  · rintro left right ⟨leftExpression, hleft⟩
      ⟨rightExpression, hright⟩
    refine ⟨leftExpression.mul rightExpression, ?_⟩
    intro assignment
    simp only [eval, Poly.mul_apply, hleft, hright]

private def liftFunction {α hidden : Type} (function : (α → ℕ) → ℕ) :
    (α ⊕ hidden → ℕ) → ℕ :=
  fun values ↦ function (values ∘ Sum.inl)

private def hiddenFunction {α hidden : Type} (index : hidden) :
    (α ⊕ hidden → ℕ) → ℕ :=
  fun values ↦ values (Sum.inr index)

private theorem liftFunction_diophFn {α hidden : Type}
    {function : (α → ℕ) → ℕ} (hfunction : DiophFn function) :
    DiophFn (liftFunction (hidden := hidden) function) :=
  Dioph.reindex_diophFn Sum.inl hfunction

private theorem hiddenFunction_diophFn {α hidden : Type} (index : hidden) :
    DiophFn (hiddenFunction (α := α) index) :=
  Dioph.proj_dioph (Sum.inr index)

theorem cipherRelation_dioph {index α : Type} (expression : PolyExpr index)
    {length digitWidth positiveLeft positiveRight negativeLeft negativeRight :
      (α → ℕ) → ℕ}
    {inputLeft inputRight : index → (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hdigitWidth : DiophFn digitWidth)
    (hinputLeft : ∀ symbol, DiophFn (inputLeft symbol))
    (hinputRight : ∀ symbol, DiophFn (inputRight symbol))
    (hpositiveLeft : DiophFn positiveLeft)
    (hpositiveRight : DiophFn positiveRight)
    (hnegativeLeft : DiophFn negativeLeft)
    (hnegativeRight : DiophFn negativeRight) :
    Dioph fun values ↦
      CipherRelation (length values) (digitWidth values)
        (fun symbol ↦ inputLeft symbol values)
        (fun symbol ↦ inputRight symbol values) expression
        (positiveLeft values) (positiveRight values)
        (negativeLeft values) (negativeRight values) := by
  induction expression generalizing α with
  | var symbol =>
      exact
        (hpositiveLeft D= hinputLeft symbol) D∧
          ((hpositiveRight D= hinputRight symbol) D∧
            (regularCipher_dioph hlength hdigitWidth hpositiveLeft hpositiveRight D∧
              (regularCipherConst_dioph hlength hdigitWidth
                  (Dioph.const_dioph 0) hnegativeLeft hnegativeRight D∧
                regularCipher_dioph hlength hdigitWidth
                  hnegativeLeft hnegativeRight)))
  | const value =>
      have hdigitBase : DiophFn fun values ↦ 2 ^ digitWidth values :=
        Dioph.pow_dioph (Dioph.const_dioph 2) hdigitWidth
      exact
        ((Dioph.const_dioph value.toNat D< hdigitBase) D∧
          ((Dioph.const_dioph (-value).toNat D< hdigitBase) D∧
            (regularCipherConst_dioph hlength hdigitWidth
                (Dioph.const_dioph value.toNat) hpositiveLeft hpositiveRight D∧
              (regularCipher_dioph hlength hdigitWidth
                  hpositiveLeft hpositiveRight D∧
                (regularCipherConst_dioph hlength hdigitWidth
                    (Dioph.const_dioph (-value).toNat) hnegativeLeft hnegativeRight D∧
                  regularCipher_dioph hlength hdigitWidth
                    hnegativeLeft hnegativeRight)))))
  | sub left right ihLeft ihRight =>
      have hLiftLength :
          DiophFn (liftFunction (hidden := Fin 8) length) :=
        liftFunction_diophFn hlength
      have hLiftDigitWidth :
          DiophFn (liftFunction (hidden := Fin 8) digitWidth) :=
        liftFunction_diophFn hdigitWidth
      have hLiftInputLeft : ∀ symbol,
          DiophFn (liftFunction (hidden := Fin 8) (inputLeft symbol)) :=
        fun symbol ↦ liftFunction_diophFn (hinputLeft symbol)
      have hLiftInputRight : ∀ symbol,
          DiophFn (liftFunction (hidden := Fin 8) (inputRight symbol)) :=
        fun symbol ↦ liftFunction_diophFn (hinputRight symbol)
      have hLiftPositiveLeft :
          DiophFn (liftFunction (hidden := Fin 8) positiveLeft) :=
        liftFunction_diophFn hpositiveLeft
      have hLiftPositiveRight :
          DiophFn (liftFunction (hidden := Fin 8) positiveRight) :=
        liftFunction_diophFn hpositiveRight
      have hLiftNegativeLeft :
          DiophFn (liftFunction (hidden := Fin 8) negativeLeft) :=
        liftFunction_diophFn hnegativeLeft
      have hLiftNegativeRight :
          DiophFn (liftFunction (hidden := Fin 8) negativeRight) :=
        liftFunction_diophFn hnegativeRight
      have hleft := ihLeft hLiftLength hLiftDigitWidth
        hLiftInputLeft hLiftInputRight
        (hiddenFunction_diophFn (0 : Fin 8))
        (hiddenFunction_diophFn (1 : Fin 8))
        (hiddenFunction_diophFn (2 : Fin 8))
        (hiddenFunction_diophFn (3 : Fin 8))
      have hright := ihRight hLiftLength hLiftDigitWidth
        hLiftInputLeft hLiftInputRight
        (hiddenFunction_diophFn (4 : Fin 8))
        (hiddenFunction_diophFn (5 : Fin 8))
        (hiddenFunction_diophFn (6 : Fin 8))
        (hiddenFunction_diophFn (7 : Fin 8))
      have haddPositive := regularCipherAdd_dioph
        (hiddenFunction_diophFn (0 : Fin 8))
        (hiddenFunction_diophFn (1 : Fin 8))
        (hiddenFunction_diophFn (6 : Fin 8))
        (hiddenFunction_diophFn (7 : Fin 8))
        hLiftPositiveLeft hLiftPositiveRight
      have hregularPositive := regularCipher_dioph
        hLiftLength hLiftDigitWidth hLiftPositiveLeft hLiftPositiveRight
      have haddNegative := regularCipherAdd_dioph
        (hiddenFunction_diophFn (2 : Fin 8))
        (hiddenFunction_diophFn (3 : Fin 8))
        (hiddenFunction_diophFn (4 : Fin 8))
        (hiddenFunction_diophFn (5 : Fin 8))
        hLiftNegativeLeft hLiftNegativeRight
      have hregularNegative := regularCipher_dioph
        hLiftLength hLiftDigitWidth hLiftNegativeLeft hLiftNegativeRight
      have hinterior := hleft D∧
        (hright D∧
          (haddPositive D∧
            (hregularPositive D∧
              (haddNegative D∧ hregularNegative))))
      exact Dioph.ext (Dioph.ex_dioph hinterior) fun _ ↦ Iff.rfl
  | mul left right ihLeft ihRight =>
      have hLiftLength :
          DiophFn (liftFunction (hidden := Fin 16) length) :=
        liftFunction_diophFn hlength
      have hLiftDigitWidth :
          DiophFn (liftFunction (hidden := Fin 16) digitWidth) :=
        liftFunction_diophFn hdigitWidth
      have hleft := ihLeft hLiftLength hLiftDigitWidth
        (fun symbol ↦ liftFunction_diophFn (hinputLeft symbol))
        (fun symbol ↦ liftFunction_diophFn (hinputRight symbol))
        (hiddenFunction_diophFn (0 : Fin 16))
        (hiddenFunction_diophFn (1 : Fin 16))
        (hiddenFunction_diophFn (2 : Fin 16))
        (hiddenFunction_diophFn (3 : Fin 16))
      have hright := ihRight hLiftLength hLiftDigitWidth
        (fun symbol ↦ liftFunction_diophFn (hinputLeft symbol))
        (fun symbol ↦ liftFunction_diophFn (hinputRight symbol))
        (hiddenFunction_diophFn (4 : Fin 16))
        (hiddenFunction_diophFn (5 : Fin 16))
        (hiddenFunction_diophFn (6 : Fin 16))
        (hiddenFunction_diophFn (7 : Fin 16))
      have hmulPP := regularCipherMul_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (0 : Fin 16))
        (hiddenFunction_diophFn (5 : Fin 16))
        (hiddenFunction_diophFn (8 : Fin 16))
      have hregularPP := regularCipher_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (8 : Fin 16))
        (hiddenFunction_diophFn (9 : Fin 16))
      have hmulNN := regularCipherMul_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (2 : Fin 16))
        (hiddenFunction_diophFn (7 : Fin 16))
        (hiddenFunction_diophFn (10 : Fin 16))
      have hregularNN := regularCipher_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (10 : Fin 16))
        (hiddenFunction_diophFn (11 : Fin 16))
      have hmulPN := regularCipherMul_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (0 : Fin 16))
        (hiddenFunction_diophFn (7 : Fin 16))
        (hiddenFunction_diophFn (12 : Fin 16))
      have hregularPN := regularCipher_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (12 : Fin 16))
        (hiddenFunction_diophFn (13 : Fin 16))
      have hmulNP := regularCipherMul_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (2 : Fin 16))
        (hiddenFunction_diophFn (5 : Fin 16))
        (hiddenFunction_diophFn (14 : Fin 16))
      have hregularNP := regularCipher_dioph hLiftLength hLiftDigitWidth
        (hiddenFunction_diophFn (14 : Fin 16))
        (hiddenFunction_diophFn (15 : Fin 16))
      have haddPositive := regularCipherAdd_dioph
        (hiddenFunction_diophFn (8 : Fin 16))
        (hiddenFunction_diophFn (9 : Fin 16))
        (hiddenFunction_diophFn (10 : Fin 16))
        (hiddenFunction_diophFn (11 : Fin 16))
        (liftFunction_diophFn hpositiveLeft)
        (liftFunction_diophFn hpositiveRight)
      have hregularPositive := regularCipher_dioph hLiftLength hLiftDigitWidth
        (liftFunction_diophFn hpositiveLeft)
        (liftFunction_diophFn hpositiveRight)
      have haddNegative := regularCipherAdd_dioph
        (hiddenFunction_diophFn (12 : Fin 16))
        (hiddenFunction_diophFn (13 : Fin 16))
        (hiddenFunction_diophFn (14 : Fin 16))
        (hiddenFunction_diophFn (15 : Fin 16))
        (liftFunction_diophFn hnegativeLeft)
        (liftFunction_diophFn hnegativeRight)
      have hregularNegative := regularCipher_dioph hLiftLength hLiftDigitWidth
        (liftFunction_diophFn hnegativeLeft)
        (liftFunction_diophFn hnegativeRight)
      have hinterior := hleft D∧
        (hright D∧
          (hmulPP D∧
            (hregularPP D∧
              (hmulNN D∧
                (hregularNN D∧
                  (hmulPN D∧
                    (hregularPN D∧
                      (hmulNP D∧
                        (hregularNP D∧
                          (haddPositive D∧
                            (hregularPositive D∧
                              (haddNegative D∧ hregularNegative))))))))))))
      exact Dioph.ext (Dioph.ex_dioph hinterior) fun _ ↦ Iff.rfl

inductive BoundedCipherHidden (arity : ℕ) (witness : Type) where
  | digitWidth
  | indexLeft
  | indexRight
  | freeLeft (index : Fin2 arity)
  | freeRight (index : Fin2 arity)
  | witnessLeft (index : witness)
  | witnessRight (index : witness)
  | positiveLeft
  | positiveRight
  | negativeLeft
  | negativeRight

def boundedInputLeft {arity : ℕ} {witness : Type}
    (values : Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ) :
    Fin2 (Nat.succ arity) ⊕ witness → ℕ
  | .inl .fz => values (.inr .indexLeft)
  | .inl (.fs index) => values (.inr (.freeLeft index))
  | .inr index => values (.inr (.witnessLeft index))

def boundedInputRight {arity : ℕ} {witness : Type}
    (values : Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ) :
    Fin2 (Nat.succ arity) ⊕ witness → ℕ
  | .inl .fz => values (.inr .indexRight)
  | .inl (.fs index) => values (.inr (.freeRight index))
  | .inr index => values (.inr (.witnessRight index))

def freeCipherCondition {arity : ℕ} {witness : Type}
    (bound : (Fin2 arity → ℕ) → ℕ)
    (index : Fin2 arity)
    (values : Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ) : Prop :=
  let outer := values ∘ Sum.inl
  let length := bound outer
  let digitWidth := values (.inr .digitWidth)
  outer index < 2 ^ digitWidth ∧
    regularCipherConst length digitWidth (outer index)
      (values (.inr (.freeLeft index)))
      (values (.inr (.freeRight index))) ∧
    regularCipher length digitWidth
      (values (.inr (.freeLeft index)))
      (values (.inr (.freeRight index)))

def boundedCipherInterior {arity : ℕ} {witness : Type}
    (bound : (Fin2 arity → ℕ) → ℕ)
    (expression : PolyExpr (Fin2 (Nat.succ arity) ⊕ witness))
    (values : Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ) : Prop :=
  let outer := values ∘ Sum.inl
  let length := bound outer
  let digitWidth := values (.inr .digitWidth)
  0 < length ∧
    length ≤ 2 ^ digitWidth ∧
    regularCipherIndex length digitWidth
      (values (.inr .indexLeft)) (values (.inr .indexRight)) ∧
    regularCipher length digitWidth
      (values (.inr .indexLeft)) (values (.inr .indexRight)) ∧
    (∀ index, freeCipherCondition bound index values) ∧
    CipherRelation length digitWidth (boundedInputLeft values)
      (boundedInputRight values) expression
      (values (.inr .positiveLeft)) (values (.inr .positiveRight))
      (values (.inr .negativeLeft)) (values (.inr .negativeRight)) ∧
    values (.inr .positiveLeft) = values (.inr .negativeLeft)

private theorem dioph_forall_fin2 {α : Type} {arity : ℕ}
    {relation : Fin2 arity → Set (α → ℕ)}
    (hrelation : ∀ index, Dioph (relation index)) :
    Dioph fun values ↦ ∀ index, relation index values := by
  induction arity with
  | zero =>
      apply Dioph.ext
        ((Dioph.const_dioph 0 : DiophFn fun _ : α → ℕ ↦ 0) D=
          Dioph.const_dioph 0)
      intro values
      constructor
      · intro _ index
        exact Fin2.elim0 (C := fun candidate ↦ relation candidate values) index
      · intro _
        rfl
  | succ arity ih =>
      have htail :
          Dioph fun values ↦ ∀ index : Fin2 arity,
            relation (.fs index) values :=
        ih (fun index ↦ hrelation (.fs index))
      apply Dioph.ext (hrelation .fz D∧ htail)
      intro values
      constructor
      · rintro ⟨hzero, htail⟩ index
        cases index with
        | fz => exact hzero
        | fs index => exact htail index
      · intro hall
        exact ⟨hall .fz, fun index ↦ hall (.fs index)⟩

theorem boundedCipherInterior_dioph {arity : ℕ} {witness : Type}
    {bound : (Fin2 arity → ℕ) → ℕ} (hbound : DiophFn bound)
    (expression : PolyExpr (Fin2 (Nat.succ arity) ⊕ witness)) :
    Dioph fun values ↦ boundedCipherInterior bound expression values := by
  have hlength :
      DiophFn (liftFunction (hidden := BoundedCipherHidden arity witness) bound) :=
    liftFunction_diophFn hbound
  have hdigitWidth :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.digitWidth : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hdigitBase : DiophFn fun values ↦
      2 ^ hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.digitWidth : BoundedCipherHidden arity witness) values :=
    Dioph.pow_dioph (Dioph.const_dioph 2) hdigitWidth
  have hindexLeft :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.indexLeft : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hindexRight :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.indexRight : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hinputLeft : ∀ symbol : Fin2 (Nat.succ arity) ⊕ witness,
      DiophFn fun values ↦ boundedInputLeft values symbol := by
    intro symbol
    rcases symbol with coordinate | index
    · cases coordinate with
      | fz => exact hindexLeft
      | fs coordinate =>
          exact hiddenFunction_diophFn
            (BoundedCipherHidden.freeLeft coordinate)
    · exact hiddenFunction_diophFn (BoundedCipherHidden.witnessLeft index)
  have hinputRight : ∀ symbol : Fin2 (Nat.succ arity) ⊕ witness,
      DiophFn fun values ↦ boundedInputRight values symbol := by
    intro symbol
    rcases symbol with coordinate | index
    · cases coordinate with
      | fz => exact hindexRight
      | fs coordinate =>
          exact hiddenFunction_diophFn
            (BoundedCipherHidden.freeRight coordinate)
    · exact hiddenFunction_diophFn (BoundedCipherHidden.witnessRight index)
  have hpositiveLeft :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.positiveLeft : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hpositiveRight :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.positiveRight : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hnegativeLeft :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.negativeLeft : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hnegativeRight :
      DiophFn (hiddenFunction (α := Fin2 arity)
        (BoundedCipherHidden.negativeRight : BoundedCipherHidden arity witness)) :=
    hiddenFunction_diophFn _
  have hfree : Dioph fun values :
      Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ ↦
      ∀ index, freeCipherCondition (witness := witness) bound index values := by
    apply dioph_forall_fin2
    intro index
    have hvalue : DiophFn fun values :
        Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ ↦
          values (Sum.inl index) :=
      Dioph.proj_dioph (Sum.inl index)
    have hleft : DiophFn fun values :
        Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ ↦
          values (Sum.inr
            (BoundedCipherHidden.freeLeft index :
              BoundedCipherHidden arity witness)) :=
      Dioph.proj_dioph (Sum.inr
        (BoundedCipherHidden.freeLeft index :
          BoundedCipherHidden arity witness))
    have hright : DiophFn fun values :
        Fin2 arity ⊕ BoundedCipherHidden arity witness → ℕ ↦
          values (Sum.inr
            (BoundedCipherHidden.freeRight index :
              BoundedCipherHidden arity witness)) :=
      Dioph.proj_dioph (Sum.inr
        (BoundedCipherHidden.freeRight index :
          BoundedCipherHidden arity witness))
    exact (hvalue D< hdigitBase) D∧
      (regularCipherConst_dioph hlength hdigitWidth hvalue hleft hright D∧
        regularCipher_dioph hlength hdigitWidth hleft hright)
  have hcompiler := cipherRelation_dioph expression hlength hdigitWidth
    hinputLeft hinputRight hpositiveLeft hpositiveRight
    hnegativeLeft hnegativeRight
  have hinterior :=
    ((Dioph.const_dioph 0 D< hlength) D∧
      ((hlength D≤ hdigitBase) D∧
        (regularCipherIndex_dioph hlength hdigitWidth hindexLeft hindexRight D∧
          (regularCipher_dioph hlength hdigitWidth hindexLeft hindexRight D∧
            (hfree D∧
              (hcompiler D∧ (hpositiveLeft D= hnegativeLeft)))))))
  exact Dioph.ext hinterior fun _ ↦ Iff.rfl

theorem exists_boundedCipherInterior_iff {arity : ℕ} {witness : Type}
    {bound : (Fin2 arity → ℕ) → ℕ}
    {relation : Set (Vector3 ℕ (Nat.succ arity))}
    (polynomial : Poly (Fin2 (Nat.succ arity) ⊕ witness))
    (hpolynomial : ∀ assignment,
      relation assignment ↔ ∃ hidden,
        polynomial (Sum.elim assignment hidden) = 0)
    (expression : PolyExpr (Fin2 (Nat.succ arity) ⊕ witness))
    (hexpression : ∀ assignment,
      expression.eval assignment = polynomial assignment)
    (outer : Vector3 ℕ arity) (hlength : 0 < bound outer) :
    (∃ hidden : BoundedCipherHidden arity witness → ℕ,
        boundedCipherInterior bound expression (Sum.elim outer hidden)) ↔
      ∀ position < bound outer, relation (position :: outer) := by
  constructor
  · rintro ⟨hidden, hinterior⟩ position hposition
    simp only [boundedCipherInterior, Sum.elim_inr] at hinterior
    rcases hinterior with
      ⟨hlengthPositive, hlengthWidth, hindexRelation, _,
        hfree, hcompiler, houtput⟩
    obtain ⟨positive, negative, hevaluation⟩ :=
      cipherRelation_sound expression hlengthPositive hcompiler
    have hdigitsEqual :
        positive.digits position = negative.digits position := by
      rw [← positive.decodeDigit_eq hposition, ← negative.decodeDigit_eq hposition,
        houtput]
    have hevaluationZero :
        expression.eval (fun symbol ↦
            decodeDigit (hidden .digitWidth)
              (boundedInputLeft (Sum.elim outer hidden) symbol) position) = 0 := by
      rw [← hevaluation position hposition, hdigitsEqual]
      simp
    have hindexViews :=
      (regularCipherIndex_spec hlengthPositive).mp hindexRelation
    let indexDigits : CipherDigits (bound outer) (hidden .digitWidth)
        (hidden .indexLeft) (hidden .indexRight) := {
      digits := fun index ↦ index
      bound := fun index hindex ↦ hindex.trans_le hlengthWidth
      leftCode_eq := hindexViews.1
      rightCode_eq := hindexViews.2
    }
    let polynomialWitness : witness → ℕ := fun index ↦
      decodeDigit (hidden .digitWidth) (hidden (.witnessLeft index)) position
    have hassignment :
        (fun symbol ↦
            decodeDigit (hidden .digitWidth)
              (boundedInputLeft (Sum.elim outer hidden) symbol) position) =
          Sum.elim (position :: outer) polynomialWitness := by
      funext symbol
      rcases symbol with coordinate | index
      · cases coordinate with
        | fz => exact indexDigits.decodeDigit_eq hposition
        | fs coordinate =>
            rcases hfree coordinate with
              ⟨hvalueBound, hconstant, _⟩
            let constantDigits : CipherDigits (bound outer) (hidden .digitWidth)
                (hidden (.freeLeft coordinate))
                (hidden (.freeRight coordinate)) :=
              constantCipherDigits hvalueBound hconstant
            exact constantDigits.decodeDigit_eq hposition
      · rfl
    apply (hpolynomial (position :: outer)).2
    refine ⟨polynomialWitness, ?_⟩
    rw [← hexpression]
    rw [← hassignment]
    exact hevaluationZero
  · intro hall
    classical
    let length := bound outer
    have hrelationAt (position : Fin length) :
        relation (position.1 :: outer) :=
      hall position.1 position.2
    have hwitnessExists (position : Fin length) :
        ∃ hidden, polynomial
          (Sum.elim (position.1 :: outer) hidden) = 0 :=
      (hpolynomial (position.1 :: outer)).mp (hrelationAt position)
    let witnessAt (position : Fin length) : witness → ℕ :=
      Classical.choose (hwitnessExists position)
    have hwitnessZero (position : Fin length) :
        polynomial (Sum.elim (position.1 :: outer) (witnessAt position)) = 0 :=
      Classical.choose_spec (hwitnessExists position)
    let witnessDigits : witness → ℕ → ℕ := fun index position ↦
      if hposition : position < length then
        witnessAt ⟨position, hposition⟩ index
      else 0
    let digits : (Fin2 (Nat.succ arity) ⊕ witness) → ℕ → ℕ
      | .inl .fz => fun position ↦ position
      | .inl (.fs index) => fun _ ↦ outer index
      | .inr index => witnessDigits index
    let expressionWidth := requiredDigitWidth length expression digits
    let freeWidth := ∑ index : Fin2 arity, outer index
    let digitWidth := length + freeWidth + expressionWidth
    have hlengthLe : length ≤ digitWidth := by
      unfold digitWidth
      omega
    have hlengthWidth : length ≤ 2 ^ digitWidth :=
      length.lt_two_pow_self.le.trans
        (Nat.pow_le_pow_right (by omega) hlengthLe)
    have hfreeLe (index : Fin2 arity) : outer index ≤ freeWidth := by
      unfold freeWidth
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ index)
    have hfreeWidth (index : Fin2 arity) : outer index < 2 ^ digitWidth := by
      have hvalueLe : outer index ≤ digitWidth :=
        (hfreeLe index).trans (by unfold digitWidth; omega)
      exact (outer index).lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by omega) hvalueLe)
    have hmagnitudeLe (position : ℕ) (hposition : position < length) :
        expression.magnitude (fun symbol ↦ digits symbol position) ≤
          expressionWidth := by
      unfold expressionWidth requiredDigitWidth
      exact Finset.single_le_sum
        (f := fun candidate ↦
          expression.magnitude (fun symbol ↦ digits symbol candidate))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hposition)
    have hfits : ∀ position < length,
        expression.Fits digitWidth (fun symbol ↦ digits symbol position) := by
      intro position hposition
      apply fits_of_magnitude_lt
      have hmagnitudeDigitWidth :
          expression.magnitude (fun symbol ↦ digits symbol position) ≤
            digitWidth :=
        (hmagnitudeLe position hposition).trans (by unfold digitWidth; omega)
      exact (expression.magnitude
          (fun symbol ↦ digits symbol position)).lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by omega) hmagnitudeDigitWidth)
    let indexLeft :=
      leftView length (cipherBlockWidth digitWidth) (fun position ↦ position)
    let indexRight :=
      rightView length (cipherBlockWidth digitWidth) (fun position ↦ position)
    let freeLeft : Fin2 arity → ℕ := fun index ↦
      leftView length (cipherBlockWidth digitWidth) (fun _ ↦ outer index)
    let freeRight : Fin2 arity → ℕ := fun index ↦
      rightView length (cipherBlockWidth digitWidth) (fun _ ↦ outer index)
    let witnessLeft : witness → ℕ := fun index ↦
      leftView length (cipherBlockWidth digitWidth) (witnessDigits index)
    let witnessRight : witness → ℕ := fun index ↦
      rightView length (cipherBlockWidth digitWidth) (witnessDigits index)
    let positiveLeft := leftView length (cipherBlockWidth digitWidth)
      (fun position ↦ expression.positive (fun symbol ↦ digits symbol position))
    let positiveRight := rightView length (cipherBlockWidth digitWidth)
      (fun position ↦ expression.positive (fun symbol ↦ digits symbol position))
    let negativeLeft := leftView length (cipherBlockWidth digitWidth)
      (fun position ↦ expression.negative (fun symbol ↦ digits symbol position))
    let negativeRight := rightView length (cipherBlockWidth digitWidth)
      (fun position ↦ expression.negative (fun symbol ↦ digits symbol position))
    let hidden : BoundedCipherHidden arity witness → ℕ
      | .digitWidth => digitWidth
      | .indexLeft => indexLeft
      | .indexRight => indexRight
      | .freeLeft index => freeLeft index
      | .freeRight index => freeRight index
      | .witnessLeft index => witnessLeft index
      | .witnessRight index => witnessRight index
      | .positiveLeft => positiveLeft
      | .positiveRight => positiveRight
      | .negativeLeft => negativeLeft
      | .negativeRight => negativeRight
    refine ⟨hidden, ?_⟩
    simp only [boundedCipherInterior, Sum.elim_inr]
    refine ⟨hlength, hlengthWidth, ?_, ?_, ?_, ?_, ?_⟩
    · exact (regularCipherIndex_spec hlength).mpr ⟨rfl, rfl⟩
    · exact regularCipher_of_digits hlength (fun position ↦ position)
        (fun position hposition ↦ hposition.trans_le hlengthWidth)
    · intro index
      simp only [freeCipherCondition, Function.comp_apply, Sum.elim_inl,
        Sum.elim_inr]
      refine ⟨hfreeWidth index, ?_, ?_⟩
      · exact regularCipherConst_of_digits length digitWidth (outer index)
      · exact regularCipher_of_digits hlength (fun _ ↦ outer index)
          (fun _ _ ↦ hfreeWidth index)
    · apply cipherRelation_complete expression hlength digits
      · intro symbol
        rcases symbol with coordinate | index
        · cases coordinate <;> rfl
        · rfl
      · intro symbol
        rcases symbol with coordinate | index
        · cases coordinate <;> rfl
        · rfl
      · exact hfits
    · change positiveLeft = negativeLeft
      unfold positiveLeft negativeLeft
      unfold leftView blockExpansion baseExpansion
      apply Finset.sum_congr rfl
      intro position hpositionMem
      have hposition : position < length := Finset.mem_range.mp hpositionMem
      have hwitnessAssignment :
          (fun symbol ↦ digits symbol position) =
            Sum.elim (position :: outer) (witnessAt ⟨position, hposition⟩) := by
        funext symbol
        rcases symbol with coordinate | index
        · cases coordinate <;> rfl
        · simp [digits, witnessDigits, hposition]
      have hevalZero :
          expression.eval (fun symbol ↦ digits symbol position) = 0 := by
        rw [hwitnessAssignment, hexpression]
        exact hwitnessZero ⟨position, hposition⟩
      have hsigned := expression.int_eq_positive_sub_negative
        (fun symbol ↦ digits symbol position)
      rw [hevalZero] at hsigned
      have hnat :
          expression.positive (fun symbol ↦ digits symbol position) =
            expression.negative (fun symbol ↦ digits symbol position) :=
        Int.ofNat_inj.mp (sub_eq_zero.mp hsigned.symm)
      exact congrArg
        (fun value ↦ value * (2 ^ cipherBlockWidth digitWidth) ^ position)
        hnat

theorem boundedForallLt_dioph {arity : ℕ}
    {bound : Vector3 ℕ arity → ℕ}
    {relation : Set (Vector3 ℕ (Nat.succ arity))}
    (hbound : DiophFn bound) (hrelation : Dioph relation) :
    Dioph fun outer : Vector3 ℕ arity ↦
      ∀ position < bound outer, relation (position :: outer) := by
  rcases hrelation with ⟨witness, polynomial, hpolynomial⟩
  obtain ⟨expression, hexpression⟩ := exists_polyExpr polynomial
  have hinterior : Dioph fun values ↦
      boundedCipherInterior bound expression values :=
    boundedCipherInterior_dioph hbound expression
  have hexists : Dioph fun outer : Vector3 ℕ arity ↦
      ∃ hidden : BoundedCipherHidden arity witness → ℕ,
        boundedCipherInterior bound expression (Sum.elim outer hidden) :=
    Dioph.ex_dioph hinterior
  have hzero : Dioph fun outer : Vector3 ℕ arity ↦ bound outer = 0 :=
    hbound D= Dioph.const_dioph 0
  apply Dioph.ext (hzero D∨ hexists)
  intro outer
  constructor
  · rintro (hboundZero | ⟨hidden, hhidden⟩)
    · intro position hposition
      change bound outer = 0 at hboundZero
      omega
    · have hboundPositive : 0 < bound outer := by
        simpa only [boundedCipherInterior, Sum.elim_inl, Sum.elim_inr]
          using hhidden.1
      exact (exists_boundedCipherInterior_iff polynomial hpolynomial
        expression hexpression outer hboundPositive).mp ⟨hidden, hhidden⟩
  · intro hall
    by_cases hboundZero : bound outer = 0
    · exact Or.inl hboundZero
    · right
      exact (exists_boundedCipherInterior_iff polynomial hpolynomial
        expression hexpression outer (Nat.pos_of_ne_zero hboundZero)).mpr hall

end PolyExpr

/-- Public bounded-universal closure exported by the regular-cipher compiler. -/
theorem boundedForallLt_dioph {arity : ℕ}
    {bound : Vector3 ℕ arity → ℕ}
    {relation : Set (Vector3 ℕ (Nat.succ arity))}
    (hbound : DiophFn bound) (hrelation : Dioph relation) :
    Dioph fun outer : Vector3 ℕ arity ↦
      ∀ position < bound outer, relation (position :: outer) :=
  PolyExpr.boundedForallLt_dioph hbound hrelation

end TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherCompiler
