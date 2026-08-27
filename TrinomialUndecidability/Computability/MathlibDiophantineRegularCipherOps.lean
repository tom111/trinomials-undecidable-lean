import TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher

/-!
# Pointwise arithmetic on two-view regular ciphers

Addition is componentwise in either regular view.  Multiplication uses the cross-view product and
the diagonal geometric mask from `MathlibDiophantineRegularCipher`.  Both graph relations are
Diophantine and have exact pointwise specifications under the cipher digit bound.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherOps

open TrinomialUndecidability.Computability.MathlibDiophantineBinary
open TrinomialUndecidability.Computability.MathlibDiophantineBitwise
open TrinomialUndecidability.Computability.MathlibDiophantineRegularCipher

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

def regularCipherAdd
    (leftCodeA rightCodeA leftCodeB rightCodeB leftCodeC rightCodeC : ℕ) : Prop :=
  leftCodeC = leftCodeA + leftCodeB ∧ rightCodeC = rightCodeA + rightCodeB

def regularCipherMul (length digitWidth leftCodeA rightCodeB leftCodeC : ℕ) : Prop :=
  let blockWidth := cipherBlockWidth digitWidth
  ((leftCodeA * rightCodeB) &&& diagonalMask length blockWidth) =
    ((leftCodeC * rightView length blockWidth (fun _ ↦ 1)) &&&
      diagonalMask length blockWidth)

theorem sum_lt_cipherRadix {digitWidth left right : ℕ}
    (hleft : left < 2 ^ digitWidth) (hright : right < 2 ^ digitWidth) :
    left + right < 2 ^ cipherBlockWidth digitWidth := by
  have hsum : left + right < 2 ^ (digitWidth + 1) := by
    rw [pow_succ]
    omega
  exact hsum.trans_le (Nat.pow_le_pow_right (by omega) (by
    unfold cipherBlockWidth
    omega))

theorem product_lt_cipherRadix {digitWidth left right : ℕ}
    (hleft : left < 2 ^ digitWidth) (hright : right < 2 ^ digitWidth) :
    left * right < 2 ^ cipherBlockWidth digitWidth := by
  have hproduct : left * right < 2 ^ (2 * digitWidth) := by
    rw [show 2 * digitWidth = digitWidth + digitWidth by omega, pow_add]
    nlinarith
  exact hproduct.trans_le (Nat.pow_le_pow_right (by omega) (by
    unfold cipherBlockWidth
    omega))

theorem regularCipherAdd_spec {length digitWidth : ℕ}
    {leftA rightA leftB rightB leftC rightC : ℕ}
    {digitsA digitsB digitsC : ℕ → ℕ}
    (hDigitsA : ∀ index < length, digitsA index < 2 ^ digitWidth)
    (hDigitsB : ∀ index < length, digitsB index < 2 ^ digitWidth)
    (hDigitsC : ∀ index < length, digitsC index < 2 ^ digitWidth)
    (hLeftA : leftView length (cipherBlockWidth digitWidth) digitsA = leftA)
    (hRightA : rightView length (cipherBlockWidth digitWidth) digitsA = rightA)
    (hLeftB : leftView length (cipherBlockWidth digitWidth) digitsB = leftB)
    (hRightB : rightView length (cipherBlockWidth digitWidth) digitsB = rightB)
    (hLeftC : leftView length (cipherBlockWidth digitWidth) digitsC = leftC)
    (hRightC : rightView length (cipherBlockWidth digitWidth) digitsC = rightC) :
    regularCipherAdd leftA rightA leftB rightB leftC rightC ↔
      ∀ index < length, digitsC index = digitsA index + digitsB index := by
  constructor
  · rintro ⟨hleft, hright⟩
    have hcode :
        leftView length (cipherBlockWidth digitWidth) digitsC =
          leftView length (cipherBlockWidth digitWidth)
            (fun index ↦ digitsA index + digitsB index) := by
      rw [hLeftC, hleft, ← hLeftA, ← hLeftB, leftView_add]
    unfold leftView blockExpansion at hcode
    exact baseExpansion_unique (by positivity)
      (fun index hindex ↦ (hDigitsC index hindex).trans_le
        (Nat.pow_le_pow_right (by omega)
          (digitWidth_le_cipherBlockWidth digitWidth)))
      (fun index hindex ↦
        sum_lt_cipherRadix (hDigitsA index hindex) (hDigitsB index hindex))
      hcode
  · intro hdigits
    constructor
    · rw [← hLeftC, ← hLeftA, ← hLeftB, leftView_add]
      unfold leftView blockExpansion baseExpansion
      apply Finset.sum_congr rfl
      intro index hindex
      rw [hdigits index (Finset.mem_range.mp hindex)]
    · rw [← hRightC, ← hRightA, ← hRightB, rightView_add]
      unfold rightView
      apply Finset.sum_congr rfl
      intro index hindex
      rw [hdigits index (Finset.mem_range.mp hindex)]

theorem regularCipherMul_spec {length digitWidth : ℕ} (hlength : 0 < length)
    {leftA rightB leftC : ℕ} {digitsA digitsB digitsC : ℕ → ℕ}
    (hDigitsA : ∀ index < length, digitsA index < 2 ^ digitWidth)
    (hDigitsB : ∀ index < length, digitsB index < 2 ^ digitWidth)
    (hDigitsC : ∀ index < length, digitsC index < 2 ^ digitWidth)
    (hLeftA : leftView length (cipherBlockWidth digitWidth) digitsA = leftA)
    (hRightB : rightView length (cipherBlockWidth digitWidth) digitsB = rightB)
    (hLeftC : leftView length (cipherBlockWidth digitWidth) digitsC = leftC) :
    regularCipherMul length digitWidth leftA rightB leftC ↔
      ∀ index < length, digitsC index = digitsA index * digitsB index := by
  let blockWidth := cipherBlockWidth digitWidth
  have hproduct :
      ∀ col row, col < length → row < length →
        digitsA col * digitsB row < 2 ^ blockWidth := by
    intro col row hcol hrow
    exact product_lt_cipherRadix (hDigitsA col hcol) (hDigitsB row hrow)
  have hresult :
      ∀ col row, col < length → row < length →
        digitsC col * 1 < 2 ^ blockWidth := by
    intro col _ hcol _
    simpa only [Nat.mul_one] using (hDigitsC col hcol).trans_le
      (Nat.pow_le_pow_right (by omega)
        (digitWidth_le_cipherBlockWidth digitWidth))
  have hleftDiagonal :=
    mixedProduct_land_diagonal hlength digitsA digitsB hproduct
  have hrightDiagonal :=
    mixedProduct_land_diagonal hlength digitsC (fun _ ↦ 1) hresult
  unfold regularCipherMul
  dsimp only
  rw [← hLeftA, ← hRightB, ← hLeftC]
  rw [hleftDiagonal, hrightDiagonal]
  simp only [Nat.mul_one]
  constructor
  · intro hequality index hindex
    exact (diagonalView_injective hlength
      (fun index hindex ↦
        product_lt_cipherRadix (hDigitsA index hindex) (hDigitsB index hindex))
      (fun index hindex ↦ (hDigitsC index hindex).trans_le
        (Nat.pow_le_pow_right (by omega)
          (digitWidth_le_cipherBlockWidth digitWidth)))
      hequality index hindex).symm
  · intro hdigits
    unfold diagonalView
    apply Finset.sum_congr rfl
    intro index hindex
    change
      (digitsA index * digitsB index) *
          (2 ^ blockWidth) ^ ((length + 1) * index) =
        digitsC index * (2 ^ blockWidth) ^ ((length + 1) * index)
    rw [hdigits index (Finset.mem_range.mp hindex)]

theorem regularCipherAdd_dioph {α : Type}
    {leftA rightA leftB rightB leftC rightC : (α → ℕ) → ℕ}
    (hleftA : DiophFn leftA) (hrightA : DiophFn rightA)
    (hleftB : DiophFn leftB) (hrightB : DiophFn rightB)
    (hleftC : DiophFn leftC) (hrightC : DiophFn rightC) :
    Dioph fun values ↦
      regularCipherAdd (leftA values) (rightA values)
        (leftB values) (rightB values) (leftC values) (rightC values) :=
  (hleftC D= (hleftA D+ hleftB)) D∧
    (hrightC D= (hrightA D+ hrightB))

theorem regularCipherMul_dioph {α : Type}
    {length digitWidth leftA rightB leftC : (α → ℕ) → ℕ}
    (hlength : DiophFn length) (hdigitWidth : DiophFn digitWidth)
    (hleftA : DiophFn leftA) (hrightB : DiophFn rightB)
    (hleftC : DiophFn leftC) :
    Dioph fun values ↦
      regularCipherMul (length values) (digitWidth values)
        (leftA values) (rightB values) (leftC values) := by
  let blockWidth : (α → ℕ) → ℕ := fun values ↦
    cipherBlockWidth (digitWidth values)
  let radix : (α → ℕ) → ℕ := fun values ↦
    2 ^ blockWidth values
  let rightBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ length values
  let rightOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (rightBase values)
  let diagonalBase : (α → ℕ) → ℕ := fun values ↦
    radix values ^ (length values + 1)
  let diagonalOnes : (α → ℕ) → ℕ := fun values ↦
    geometricSum (length values) (diagonalBase values)
  let diagonalBlockMask : (α → ℕ) → ℕ := fun values ↦
    (radix values - 1) * diagonalOnes values
  have hblockWidth : DiophFn blockWidth := by
    unfold blockWidth cipherBlockWidth
    exact ((Dioph.const_dioph 2 D* hdigitWidth) D+ Dioph.const_dioph 2)
  have hradix : DiophFn radix := by
    unfold radix
    exact Dioph.pow_dioph (Dioph.const_dioph 2) hblockWidth
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
  have hdiagonalBlockMask : DiophFn diagonalBlockMask := by
    unfold diagonalBlockMask
    exact (hradix D- Dioph.const_dioph 1) D* hdiagonalOnes
  have hleftProduct :
      DiophFn fun values ↦ leftA values * rightB values :=
    hleftA D* hrightB
  have hrightProduct :
      DiophFn fun values ↦ leftC values * rightOnes values :=
    hleftC D* hrightOnes
  have hleftDiagonal :
      DiophFn fun values ↦
        (leftA values * rightB values) &&& diagonalBlockMask values :=
    land_diophFn hleftProduct hdiagonalBlockMask
  have hrightDiagonal :
      DiophFn fun values ↦
        (leftC values * rightOnes values) &&& diagonalBlockMask values :=
    land_diophFn hrightProduct hdiagonalBlockMask
  apply Dioph.ext (hleftDiagonal D= hrightDiagonal)
  intro values
  simp only [regularCipherMul, blockWidth, radix, rightBase, rightOnes,
    diagonalBase, diagonalOnes, diagonalBlockMask, diagonalMask,
    rightView_const, Nat.one_mul]

end TrinomialUndecidability.Computability.MathlibDiophantineRegularCipherOps
