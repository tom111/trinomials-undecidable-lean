import TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherOps

/-!
# Formula inputs for two-view regular ciphers

This module constructs regular-cipher codes for constant digit sequences and for the bounded
index sequence.  A weighted geometric-series equation characterizes the index codes without
division, and all graph relations are Diophantine.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherFormula

open TrinomialUndecidability.Computability.MathlibDiophantineBinary
open TrinomialUndecidability.Computability.MathlibDiophantineBitwise
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherOps

open scoped BigOperators

def weightedGeometricSum (length base : ℕ) : ℕ :=
  ∑ index ∈ Finset.range length, index * base ^ index

theorem weightedGeometricSum_equation (length base : ℕ) :
    (base - 1) * weightedGeometricSum length base +
          geometricSum length base + base ^ length =
      length * base ^ length + 1 := by
  cases base with
  | zero =>
      cases length with
      | zero => simp [weightedGeometricSum, geometricSum]
      | succ length =>
          by_cases hlength : length = 0
          · subst length
            simp [weightedGeometricSum, geometricSum]
          · simp [weightedGeometricSum, geometricSum,
              Finset.sum_range_succ, hlength]
  | succ predecessor =>
      induction length with
      | zero => simp [weightedGeometricSum, geometricSum]
      | succ length ih =>
          rw [weightedGeometricSum, Finset.sum_range_succ]
          rw [geometricSum, Finset.sum_range_succ]
          rw [pow_succ]
          simp only [Nat.add_sub_cancel] at ih ⊢
          calc
            predecessor *
                    ((∑ index ∈ Finset.range length,
                        index * (predecessor + 1) ^ index) +
                      length * (predecessor + 1) ^ length) +
                  ((∑ index ∈ Finset.range length,
                      (predecessor + 1) ^ index) +
                    (predecessor + 1) ^ length) +
                  (predecessor + 1) ^ length * (predecessor + 1) =
                (predecessor * weightedGeometricSum length (predecessor + 1) +
                    geometricSum length (predecessor + 1) +
                    (predecessor + 1) ^ length) +
                  predecessor * length * (predecessor + 1) ^ length +
                  (predecessor + 1) ^ length * (predecessor + 1) := by
              simp only [weightedGeometricSum, geometricSum]
              ring
            _ =
                (length * (predecessor + 1) ^ length + 1) +
                  predecessor * length * (predecessor + 1) ^ length +
                  (predecessor + 1) ^ length * (predecessor + 1) := by
              rw [ih]
            _ =
                (length + 1) *
                    ((predecessor + 1) ^ length * (predecessor + 1)) +
                  1 := by
              ring

def weightedGeometricEquation (length base value : ℕ) : Prop :=
  (base - 1) * value + geometricSum length base + base ^ length =
    length * base ^ length + 1

theorem weightedGeometricEquation_spec {length base value : ℕ} (hbase : 2 ≤ base) :
    weightedGeometricEquation length base value ↔
      value = weightedGeometricSum length base := by
  constructor
  · intro hequation
    unfold weightedGeometricEquation at hequation
    have hcanonical := weightedGeometricSum_equation length base
    have hmul :
        (base - 1) * value =
          (base - 1) * weightedGeometricSum length base := by
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  · rintro rfl
    exact weightedGeometricSum_equation length base

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

theorem weightedGeometricEquation_dioph {α : Type}
    {length base value : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hbase : DiophFn base)
    (hvalue : DiophFn value) :
    Dioph fun values ↦
      weightedGeometricEquation (length values) (base values) (value values) := by
  have hsum :
      DiophFn fun values ↦ geometricSum (length values) (base values) :=
    geometricSum_comp_diophFn hlength hbase
  have hpower : DiophFn fun values ↦ base values ^ length values :=
    Dioph.pow_dioph hbase hlength
  exact
    ((((hbase D- Dioph.const_dioph 1) D* hvalue) D+ hsum) D+ hpower) D=
      ((hlength D* hpower) D+ Dioph.const_dioph 1)

def regularCipherConst
    (length digitWidth constant leftCode rightCode : ℕ) : Prop :=
  let blockWidth := cipherBlockWidth digitWidth
  let radix := 2 ^ blockWidth
  leftCode = constant * geometricSum length radix ∧
    rightCode = constant * geometricSum length (radix ^ length)

def regularCipherIndex (length digitWidth leftCode rightCode : ℕ) : Prop :=
  let blockWidth := cipherBlockWidth digitWidth
  let radix := 2 ^ blockWidth
  weightedGeometricEquation length radix leftCode ∧
    weightedGeometricEquation length (radix ^ length) rightCode

theorem regularCipherConst_dioph {α : Type}
    {length digitWidth constant leftCode rightCode : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hdigitWidth : DiophFn digitWidth)
    (hconstant : DiophFn constant) (hleftCode : DiophFn leftCode)
    (hrightCode : DiophFn rightCode) :
    Dioph fun values ↦
      regularCipherConst (length values) (digitWidth values) (constant values)
        (leftCode values) (rightCode values) := by
  let blockWidth : (α → ℕ) → ℕ := fun values ↦
    cipherBlockWidth (digitWidth values)
  let radix : (α → ℕ) → ℕ := fun values ↦
    2 ^ blockWidth values
  let leftOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (radix values)
  let rightBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ length values
  let rightOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (rightBase values)
  have hblockWidth : DiophFn blockWidth := by
    unfold blockWidth cipherBlockWidth
    exact ((Dioph.const_dioph 2 D* hdigitWidth) D+ Dioph.const_dioph 2)
  have hradix : DiophFn radix := by
    unfold radix
    exact Dioph.pow_dioph (Dioph.const_dioph 2) hblockWidth
  have hleftOnes : DiophFn leftOnes := by
    unfold leftOnes
    exact geometricSum_comp_diophFn hlength hradix
  have hrightBase : DiophFn rightBase := by
    unfold rightBase
    exact Dioph.pow_dioph hradix hlength
  have hrightOnes : DiophFn rightOnes := by
    unfold rightOnes
    exact geometricSum_comp_diophFn hlength hrightBase
  exact Dioph.ext
    ((hleftCode D= (hconstant D* hleftOnes)) D∧
      (hrightCode D= (hconstant D* hrightOnes)))
    fun _ ↦ Iff.rfl

theorem regularCipherIndex_dioph {α : Type}
    {length digitWidth leftCode rightCode : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hdigitWidth : DiophFn digitWidth)
    (hleftCode : DiophFn leftCode) (hrightCode : DiophFn rightCode) :
    Dioph fun values ↦
      regularCipherIndex (length values) (digitWidth values)
        (leftCode values) (rightCode values) := by
  let blockWidth : (α → ℕ) → ℕ := fun values ↦
    cipherBlockWidth (digitWidth values)
  let radix : (α → ℕ) → ℕ := fun values ↦
    2 ^ blockWidth values
  let rightBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ length values
  have hblockWidth : DiophFn blockWidth := by
    unfold blockWidth cipherBlockWidth
    exact ((Dioph.const_dioph 2 D* hdigitWidth) D+ Dioph.const_dioph 2)
  have hradix : DiophFn radix := by
    unfold radix
    exact Dioph.pow_dioph (Dioph.const_dioph 2) hblockWidth
  have hrightBase : DiophFn rightBase := by
    unfold rightBase
    exact Dioph.pow_dioph hradix hlength
  exact
    (weightedGeometricEquation_dioph hlength hradix hleftCode) D∧
      (weightedGeometricEquation_dioph hlength hrightBase hrightCode)

theorem weightedGeometricSum_eq_leftView (length width : ℕ) :
    weightedGeometricSum length (2 ^ width) =
      leftView length width (fun index ↦ index) := rfl

theorem weightedGeometricSum_eq_rightView (length width : ℕ) :
    weightedGeometricSum length ((2 ^ width) ^ length) =
      rightView length width (fun index ↦ index) := by
  unfold weightedGeometricSum rightView
  apply Finset.sum_congr rfl
  intro index _
  rw [pow_mul]

theorem regularCipherConst_spec
    {length digitWidth constant leftCode rightCode : ℕ} :
    regularCipherConst length digitWidth constant leftCode rightCode ↔
      leftView length (cipherBlockWidth digitWidth) (fun _ ↦ constant) =
          leftCode ∧
        rightView length (cipherBlockWidth digitWidth) (fun _ ↦ constant) =
          rightCode := by
  simp only [regularCipherConst, leftView_const, rightView_const, eq_comm]

theorem regularCipherIndex_spec {length digitWidth leftCode rightCode : ℕ}
    (hlength : 0 < length) :
    regularCipherIndex length digitWidth leftCode rightCode ↔
      leftView length (cipherBlockWidth digitWidth) (fun index ↦ index) =
          leftCode ∧
        rightView length (cipherBlockWidth digitWidth) (fun index ↦ index) =
          rightCode := by
  let blockWidth := cipherBlockWidth digitWidth
  let radix := 2 ^ blockWidth
  have hradix : 2 ≤ radix := by
    unfold radix blockWidth
    exact Nat.one_lt_two_pow (by unfold cipherBlockWidth; omega)
  have hrightBase : 2 ≤ radix ^ length :=
    hradix.trans (Nat.le_pow hlength)
  unfold regularCipherIndex
  dsimp only
  rw [weightedGeometricEquation_spec hradix,
    weightedGeometricEquation_spec hrightBase]
  rw [weightedGeometricSum_eq_leftView,
    weightedGeometricSum_eq_rightView]
  simp only [blockWidth, eq_comm]

end TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherFormula
