import Trinomial.Base.Laurent

/-!
# The two trinomial families and the quadrinomial `Ω`

[§2, Definition 2.3]:

* affine type:   `τ_d = 1 − S·D^d − T·D^{−d}`  for `d ∈ ℤ^N`;
* infinite type: `θ_e^{p,q} = (p−q) + q·D^{pe} − p·D^{qe}` for `e ∈ ℤ^N` primitive and
  `p, q ∈ ℤ` distinct and nonzero;
* the quadrinomial `Ω = (S+T−1)(S−T) = S² − T² − S + T`  [Proposition 2.4 (iii)].

This module defines the three families and computes their supports; membership in the
base ideal is proved in `Trinomial/Base/BaseIdeal.lean`.
-/

set_option autoImplicit false

namespace Trinomial

variable {N : ℕ}

open AddMonoidAlgebra

/-- The affine trinomial `τ_d = 1 − S·D^d − T·D^{−d}`. -/
noncomputable def tau (d : Fin N → ℤ) : Laurent N :=
  1 - mono ⟨1, 0, d⟩ - mono ⟨0, 1, -d⟩

/-- The infinite trinomial `θ_e^{p,q} = (p−q) + q·D^{pe} − p·D^{qe}`.
The definition makes sense for all `e, p, q`; the paper's side conditions (`e` primitive,
`p ≠ q` both nonzero) appear as hypotheses where needed. -/
noncomputable def theta (e : Fin N → ℤ) (p q : ℤ) : Laurent N :=
  ((p : ℚ) - (q : ℚ)) • 1 + (q : ℚ) • mono ⟨0, 0, p • e⟩ - (p : ℚ) • mono ⟨0, 0, q • e⟩

/-- The quadrinomial `Ω = (S+T−1)(S−T)`. -/
noncomputable def Omega (N : ℕ) : Laurent N := (S N + T N - 1) * (S N - T N)

/-! ### Support computations

A helper for the support of a sum of three "singles" with distinct exponents, then the
support of each family.  Recall `mono x = single x 1` and `c • single x 1 = single x c`.
-/

theorem single_smul_mono (c : ℚ) (x : Exponent N) :
    c • mono x = AddMonoidAlgebra.single x c := by
  rw [mono, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Support of a combination of three distinct monomials with nonzero coefficients
(`Finsupp.support_single_add_single` and `Finsupp.support_add_single`). -/
theorem support_three {x y z : Exponent N} {a b c : ℚ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (AddMonoidAlgebra.single x a + AddMonoidAlgebra.single y b
      + AddMonoidAlgebra.single z c).support = {x, y, z} := by
  have h2 : (AddMonoidAlgebra.single x a + AddMonoidAlgebra.single y b : Laurent N).support
      = {x, y} := Finsupp.support_single_add_single hxy ha hb
  rw [Finsupp.support_add_single (by simp [h2, hxz.symm, hyz.symm]) hc, Finset.cons_eq_insert, h2]
  ext w
  simp [or_comm, or_left_comm]

/-- Cardinality of a three-element exponent set. -/
theorem card_three {x y z : Exponent N} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Exponent N)).card = 3 :=
  Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

/-- `τ_d` written as a sum of singles. -/
theorem tau_eq_singles (d : Fin N → ℤ) :
    tau d = AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single ⟨1, 0, d⟩ (-1)
      + AddMonoidAlgebra.single ⟨0, 1, -d⟩ (-1) := by
  rw [tau, AddMonoidAlgebra.one_def, mono, mono, sub_eq_add_neg, sub_eq_add_neg,
    add_assoc, ← Finsupp.single_neg, ← Finsupp.single_neg]
  exact (add_assoc _ _ _).symm

/-- The affine trinomial has exactly the three expected exponents in its support. -/
theorem support_tau (d : Fin N → ℤ) :
    (tau d).support = {0, ⟨1, 0, d⟩, ⟨0, 1, -d⟩} := by
  rw [tau_eq_singles]
  refine support_three ?_ ?_ ?_ one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero)
  · intro h; exact one_ne_zero (congrArg Exponent.s h).symm
  · intro h; exact one_ne_zero (congrArg Exponent.t h).symm
  · intro h; exact one_ne_zero (congrArg Exponent.s h)

/-- `τ_d` is an honest trinomial: three collected terms. -/
theorem supportCard_tau (d : Fin N → ℤ) : (tau d).support.card = 3 := by
  rw [support_tau]
  refine card_three ?_ ?_ ?_
  · intro h; exact one_ne_zero (congrArg Exponent.s h).symm
  · intro h; exact one_ne_zero (congrArg Exponent.t h).symm
  · intro h; exact one_ne_zero (congrArg Exponent.s h)

theorem tau_ne_zero (d : Fin N → ℤ) : tau d ≠ 0 := by
  intro h
  have := supportCard_tau d
  rw [h] at this
  simp at this

/-- `θ_e^{p,q}` written as a sum of singles. -/
theorem theta_eq_singles (e : Fin N → ℤ) (p q : ℤ) :
    theta e p q = AddMonoidAlgebra.single 0 ((p : ℚ) - (q : ℚ))
      + AddMonoidAlgebra.single ⟨0, 0, p • e⟩ (q : ℚ)
      + AddMonoidAlgebra.single ⟨0, 0, q • e⟩ (-(p : ℚ)) := by
  rw [theta, sub_eq_add_neg, single_smul_mono, single_smul_mono, ← Finsupp.single_neg]
  congr 1
  congr 1
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

section ThetaSupport

variable {e : Fin N → ℤ} {p q : ℤ}

/-- Distinct nonzero multiples of a nonzero integer vector are distinct
(`smul_left_injective`). -/
theorem smul_ne_smul (he : e ≠ 0) (hpq : p ≠ q) : p • e ≠ q • e :=
  fun h => hpq (smul_left_injective ℤ he h)

/-- The infinite trinomial has exactly the three expected exponents in its support. -/
theorem support_theta (he : e ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    (theta e p q).support = {0, ⟨0, 0, p • e⟩, ⟨0, 0, q • e⟩} := by
  rw [theta_eq_singles]
  refine support_three ?_ ?_ ?_ ?_ (by exact_mod_cast hq) ?_
  · intro h
    exact smul_ne_zero hp he (congrArg Exponent.d h).symm
  · intro h
    exact smul_ne_zero hq he (congrArg Exponent.d h).symm
  · intro h
    exact smul_ne_smul he hpq (congrArg Exponent.d h)
  · simpa [sub_eq_zero] using fun h => hpq (by exact_mod_cast h)
  · simpa using (fun h => hp (by exact_mod_cast h) : ¬((p : ℚ) = 0))

/-- `θ_e^{p,q}` is an honest trinomial: three collected terms. -/
theorem supportCard_theta (he : e ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    (theta e p q).support.card = 3 := by
  rw [support_theta he hp hq hpq]
  refine card_three ?_ ?_ ?_
  · intro h
    exact smul_ne_zero hp he (congrArg Exponent.d h).symm
  · intro h
    exact smul_ne_zero hq he (congrArg Exponent.d h).symm
  · intro h
    exact smul_ne_smul he hpq (congrArg Exponent.d h)

theorem theta_ne_zero (he : e ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    theta e p q ≠ 0 := by
  intro h
  have := supportCard_theta he hp hq hpq
  rw [h] at this
  simp at this

end ThetaSupport

/-- `Ω` expanded into monomials: `S² − T² − S + T`. -/
theorem Omega_eq_singles :
    Omega N = mono ⟨2, 0, 0⟩ - mono ⟨0, 2, 0⟩ - mono ⟨1, 0, 0⟩ + mono ⟨0, 1, 0⟩ := by
  have expand : ∀ a b : Laurent N, (a + b - 1) * (a - b) = a * a - b * b - a + b := by
    intro a b; ring
  rw [Omega, expand, show S N * S N = mono ⟨2, 0, 0⟩ by
      rw [S, mono_mul]; congr 1,
    show T N * T N = mono ⟨0, 2, 0⟩ by
      rw [T, mono_mul]; congr 1]
  rfl

/-- Support of a combination of four distinct monomials with nonzero coefficients. -/
theorem support_four {w x y z : Exponent N} {a b c d : ℚ}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (AddMonoidAlgebra.single w a + (AddMonoidAlgebra.single x b
      + (AddMonoidAlgebra.single y c + AddMonoidAlgebra.single z d))).support
      = {w, x, y, z} := by
  have h3 : (AddMonoidAlgebra.single x b + (AddMonoidAlgebra.single y c
      + AddMonoidAlgebra.single z d) : Laurent N).support = {x, y, z} := by
    rw [← add_assoc]
    exact support_three hxy hxz hyz hb hc hd
  rw [add_comm, Finsupp.support_add_single (by simp [h3, hwx, hwy, hwz]) ha,
    Finset.cons_eq_insert, h3]

/-- The quadrinomial `Ω` has exactly four collected terms  [the paper: "the quadrinomial
`Ω = (S+T−1)(S−T)` lies in `J₀`", used for `t(I) ≤ 4`]. -/
theorem supportCard_Omega : (Omega N).support.card = 4 := by
  have h1 : Omega N = AddMonoidAlgebra.single (⟨2, 0, 0⟩ : Exponent N) 1
      + (AddMonoidAlgebra.single (⟨0, 1, 0⟩ : Exponent N) 1
      + (AddMonoidAlgebra.single (⟨0, 2, 0⟩ : Exponent N) (-1)
      + AddMonoidAlgebra.single (⟨1, 0, 0⟩ : Exponent N) (-1))) := by
    rw [Omega_eq_singles, mono, mono, mono, mono, sub_eq_add_neg, sub_eq_add_neg,
      ← Finsupp.single_neg, ← Finsupp.single_neg]
    abel
  rw [h1, support_four]
  · rfl
  -- the six pairwise distinctness goals and the four `≠ 0` coefficient goals
  all_goals simp

theorem Omega_ne_zero : Omega N ≠ 0 := by
  intro h
  have := supportCard_Omega (N := N)
  rw [h] at this
  simp at this

end Trinomial
