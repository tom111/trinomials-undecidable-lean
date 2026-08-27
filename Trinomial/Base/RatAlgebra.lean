import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# Small helpers for `ℚ`-algebras

The unit `2` of an arbitrary `ℚ`-algebra and the value of its inverse powers.  Both the
evaluation `φ_Q : L_N → A_Q` [§3] and the normal-form evaluation `L_N → A₀`
[Lemma 2.2] carry a factor `2^{−a−b}`, expressed through this unit.
-/

set_option autoImplicit false

namespace Trinomial

/-- `2` as a unit of any `ℚ`-algebra. -/
noncomputable def twoUnit (A : Type*) [CommRing A] [Algebra ℚ A] : Aˣ :=
  Units.map (algebraMap ℚ A).toMonoidHom (Units.mk0 2 two_ne_zero)

lemma twoUnit_inv_zpow_val (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℤ) :
    (((twoUnit A)⁻¹ ^ n : Aˣ) : A) = algebraMap ℚ A ((1 / 2 : ℚ) ^ n) := by
  have h : ((twoUnit A)⁻¹ ^ n : Aˣ) =
      Units.map (algebraMap ℚ A).toMonoidHom ((Units.mk0 2 two_ne_zero)⁻¹ ^ n) := by
    rw [map_zpow, map_inv]
    rfl
  rw [h, Units.coe_map]
  show algebraMap ℚ A (((Units.mk0 2 two_ne_zero)⁻¹ ^ n : ℚˣ) : ℚ) = _
  congr 1
  rw [Units.val_zpow_eq_zpow_val]
  norm_num

end Trinomial
