import Mathlib.NumberTheory.Dioph
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Bitwise

/-!
# Binomial digits and binary masks are Diophantine

This is the first arithmetic layer of the sparse power-cipher proof used to eliminate bounded
universal quantifiers.  The binomial coefficient is recovered as one digit of `(q + 1) ^ n` in a
base larger than every coefficient.  Lucas's theorem modulo two then identifies bitwise inclusion
with oddness of a binomial coefficient.  Mathlib's Diophantine exponentiation theorem turns both
identities into exact Diophantine graphs.
-/

set_option autoImplicit false

namespace TrinomialUndecidability.Computability.MathlibDiophantineBinary

open scoped BigOperators

/-! ## Base expansions and binomial digits -/

/-- The first `length` digits of a finite base expansion, in little-endian order. -/
def baseExpansion (length base : ℕ) (digits : ℕ → ℕ) : ℕ :=
  ∑ index ∈ Finset.range length, digits index * base ^ index

/-- Split a finite base expansion immediately before a selected digit. -/
theorem baseExpansion_split {length index base : ℕ} {digits : ℕ → ℕ}
    (hindex : index < length) :
    baseExpansion length base digits =
      baseExpansion index base digits + base ^ index *
        (digits index + base *
          baseExpansion (length - index - 1) base
            (fun offset ↦ digits (index + 1 + offset))) := by
  unfold baseExpansion
  have hlength : index + (length - index) = length := Nat.add_sub_of_le hindex.le
  nth_rewrite 1 [← hlength]
  rw [Finset.sum_range_add]
  have hsucc : length - index = (length - index - 1) + 1 := by omega
  nth_rewrite 1 [hsucc]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have htail :
      (∑ offset ∈ Finset.range (length - index - 1),
          digits (index + (offset + 1)) * base ^ (index + (offset + 1))) =
        base ^ (index + 1) *
          ∑ offset ∈ Finset.range (length - index - 1),
            digits (index + 1 + offset) * base ^ offset := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro offset _
    rw [show index + (offset + 1) = index + 1 + offset by omega, pow_add]
    ring
  rw [htail, pow_succ]
  ring

/-- A base expansion with every digit strictly below the positive base is below the next power. -/
theorem baseExpansion_lt {length base : ℕ} {digits : ℕ → ℕ} (hbase : 0 < base)
    (hdigits : ∀ index < length, digits index < base) :
    baseExpansion length base digits < base ^ length := by
  unfold baseExpansion
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hdigit : digits length < base := hdigits length (Nat.lt_succ_self length)
      have hprefix :
          (∑ index ∈ Finset.range length, digits index * base ^ index) <
            base ^ length := by
        apply ih
        intro index hindex
        exact hdigits index (hindex.trans (Nat.lt_succ_self length))
      nlinarith [pow_pos hbase length]

/-- Division by `base ^ index`, followed by reduction modulo `base`, reads the selected digit. -/
theorem baseExpansion_digit {length index base : ℕ} {digits : ℕ → ℕ}
    (hindex : index < length) (hbase : 0 < base)
    (hdigits : ∀ position < index, digits position < base) :
    baseExpansion length base digits / base ^ index % base = digits index % base := by
  rw [baseExpansion_split hindex]
  have hpower : 0 < base ^ index := pow_pos hbase _
  have hprefix : baseExpansion index base digits < base ^ index :=
    baseExpansion_lt hbase hdigits
  rw [Nat.add_mul_div_left _ _ hpower, Nat.div_eq_of_lt hprefix, zero_add]
  exact Nat.add_mul_mod_self_left _ _ _

/-- A power of two larger than every binomial coefficient in row `n`. -/
def chooseBase (n : ℕ) : ℕ :=
  2 ^ (n + 1)

/-- Every binomial coefficient in row `n` is strictly below `chooseBase n`. -/
theorem choose_lt_chooseBase (n k : ℕ) : n.choose k < chooseBase n := by
  have hle : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have hpos : 0 < 2 ^ n := pow_pos (by omega) n
  unfold chooseBase
  rw [pow_succ]
  omega

/-- The binomial theorem viewed as a little-endian base expansion. -/
theorem add_one_pow_eq_baseExpansion (n base : ℕ) :
    (base + 1) ^ n = baseExpansion (n + 1) base (Nat.choose n) := by
  rw [add_pow]
  unfold baseExpansion
  apply Finset.sum_congr rfl
  intro index _
  simp
  ring

/-- The `k`th binomial coefficient is the `k`th base-`chooseBase n` digit of the binomial
expansion of `(chooseBase n + 1) ^ n`. -/
theorem choose_digit (n k : ℕ) :
    (chooseBase n + 1) ^ n / chooseBase n ^ k % chooseBase n = n.choose k := by
  have hbase : 0 < chooseBase n := by
    unfold chooseBase
    positivity
  by_cases hk : k < n + 1
  · rw [add_one_pow_eq_baseExpansion]
    rw [baseExpansion_digit hk hbase]
    exact Nat.mod_eq_of_lt (choose_lt_chooseBase n k)
    intro index _
    exact choose_lt_chooseBase n index
  · have hnk : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hnk]
    have hexpansion :
        baseExpansion (n + 1) (chooseBase n) (Nat.choose n) <
          chooseBase n ^ (n + 1) := by
      apply baseExpansion_lt hbase
      intro index _
      exact choose_lt_chooseBase n index
    have hpower : chooseBase n ^ (n + 1) ≤ chooseBase n ^ k :=
      Nat.pow_le_pow_right hbase (by omega)
    rw [add_one_pow_eq_baseExpansion]
    rw [Nat.div_eq_of_lt (hexpansion.trans_le hpower)]
    simp

/-! ## Lucas parity and bitwise inclusion -/

/-- Injectivity of `Nat.bit` in its Boolean digit and remaining binary word. -/
theorem bit_eq_bit_iff (a b : Bool) (m n : ℕ) :
    Nat.bit a m = Nat.bit b n ↔ a = b ∧ m = n := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Nat.bodd h, by simpa using congrArg Nat.div2 h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- `binaryLE a b` means that every set bit of `a` is also a set bit of `b`. -/
def binaryLE (a b : ℕ) : Prop :=
  a &&& b = a

/-- Bitwise inclusion decomposes into its low bit and the two shifted binary words. -/
theorem binaryLE_rec (a b : ℕ) :
    binaryLE a b ↔
      ((a.bodd && b.bodd) = a.bodd) ∧ binaryLE a.div2 b.div2 := by
  have hland :
      a &&& b = Nat.bit (a.bodd && b.bodd) (a.div2 &&& b.div2) := by
    conv_lhs =>
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b, Nat.land_bit]
  have hbits :
      Nat.bit (a.bodd && b.bodd) (a.div2 &&& b.div2) = a ↔
        ((a.bodd && b.bodd) = a.bodd) ∧ a.div2 &&& b.div2 = a.div2 := by
    conv_lhs => rhs; rw [← Nat.bit_bodd_div2 a]
    exact bit_eq_bit_iff _ _ _ _
  unfold binaryLE
  rw [hland]
  exact hbits

/-- The one-digit form of Lucas's theorem modulo two. -/
theorem choose_mod_two_recurrence (a b : ℕ) :
    b.choose a % 2 =
      ((b % 2).choose (a % 2) * (b / 2).choose (a / 2)) % 2 := by
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- The remainder modulo two is one exactly when the low binary digit is set. -/
theorem mod_two_eq_one_iff_bodd (x : ℕ) :
    x % 2 = 1 ↔ x.bodd = true := by
  rw [Nat.mod_two_of_bodd]
  cases x.bodd <;> simp

/-- Lucas parity: `b.choose a` is odd exactly when the set bits of `a` are contained in those of
`b`. -/
theorem choose_mod_two_eq_one_iff_binaryLE (a b : ℕ) :
    b.choose a % 2 = 1 ↔ binaryLE a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      by_cases hb : b = 0
      · subst b
        cases a <;> simp [binaryLE]
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hbdiv : b / 2 < b := Nat.div_lt_self hbpos (by omega)
        have hrec := ih (b / 2) hbdiv (a / 2)
        rw [choose_mod_two_recurrence, binaryLE_rec]
        rw [Nat.mod_two_of_bodd a, Nat.mod_two_of_bodd b]
        rw [Nat.div2_val, Nat.div2_val]
        cases a.bodd <;> cases b.bodd <;> simp
        all_goals exact hrec

/-! ## Diophantine graphs -/

open Dioph Fin2 Nat
open Vector3
open scoped Dioph Vector3

/-- `chooseBase` is a Diophantine function because exponentiation is Diophantine. -/
theorem chooseBase_diophFn {α : Type} {function : (α → ℕ) → ℕ}
    (hfunction : DiophFn function) :
    DiophFn fun values ↦ chooseBase (function values) := by
  unfold chooseBase
  exact Dioph.pow_dioph (Dioph.const_dioph 2) (hfunction D+ D.1)

/-- The binomial coefficient is a Diophantine function. -/
theorem choose_diophFn {α : Type} {upper lower : (α → ℕ) → ℕ}
    (hupper : DiophFn upper) (hlower : DiophFn lower) :
    DiophFn fun values ↦ (upper values).choose (lower values) := by
  have hbase : DiophFn fun values ↦ chooseBase (upper values) :=
    chooseBase_diophFn hupper
  have hnumerator :
      DiophFn fun values ↦ (chooseBase (upper values) + 1) ^ upper values :=
    Dioph.pow_dioph (hbase D+ D.1) hupper
  have hdenominator :
      DiophFn fun values ↦ chooseBase (upper values) ^ lower values :=
    Dioph.pow_dioph hbase hlower
  have hdigit :
      DiophFn fun values ↦
        (chooseBase (upper values) + 1) ^ upper values /
            chooseBase (upper values) ^ lower values % chooseBase (upper values) :=
    (hnumerator D/ hdenominator) D% hbase
  simpa only [choose_digit] using hdigit

/-- Bitwise inclusion is a Diophantine relation. -/
theorem binaryLE_dioph {α : Type} {left right : (α → ℕ) → ℕ}
    (hleft : DiophFn left) (hright : DiophFn right) :
    Dioph fun values ↦ binaryLE (left values) (right values) := by
  have hchoose :
      DiophFn fun values ↦ (right values).choose (left values) :=
    choose_diophFn hright hleft
  have hparity :
      DiophFn fun values ↦ (right values).choose (left values) % 2 :=
    hchoose D% (Dioph.const_dioph 2)
  exact Dioph.ext (hparity D= D.1) fun values ↦
    choose_mod_two_eq_one_iff_binaryLE (left values) (right values)

end TrinomialUndecidability.Computability.MathlibDiophantineBinary
