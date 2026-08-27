import Trinomial.Encoding.GuardedSystem
import Trinomial.ShortestPolynomial

/-!
# Theorem 4.5, polynomial side: the ideal `I_P ⊆ ℚ[S, T, D₁, …, D_N]`

[Theorem 4.5, last paragraph of the proof].  The Laurent ideal `J_P` is
contracted to the ordinary polynomial ring: `I_P = J_P ∩ ℚ[S,T,D]`.  Every `k`-nomial
of `I_P` maps to a `k`-nomial of `J_P` (the embedding preserves supports exactly), and
conversely the trinomial `τ_d` and the quadrinomial `Ω` are cleared into polynomials by
explicit monomial multiplications (only these two witnesses are transferred back; the
general `k`-nomial transfer is not formalized).  Theorem 4.5 descends:

* `Var N` — the variables `S, T, D i` of the polynomial ring;
* `toLaurent` — the support-preserving embedding `ℚ[S,T,D] → L_N`;
* `polyReductionIdeal Q` — the contraction `I_P`;
* `hasShort_of_hasShortPoly`, `hasShortPoly_three_of_tau`, `hasShortPoly_four` — the transfer
  of the short-support statements of `Trinomial/Encoding/MainLaurent.lean` to `I_P`, assembled into
  Theorem 4.5 for the definite ideal `I_P` in `Trinomial/Encoding/StraightLineProgram.lean` and
  `Trinomial/Encoding/MainTheorem.lean`.
-/

set_option autoImplicit false

namespace Trinomial

/-- The variables of the polynomial ring `ℚ[S, T, D₁, …, D_N]`. -/
inductive Var (N : ℕ) where
  | S : Var N
  | T : Var N
  | D : Fin N → Var N
deriving DecidableEq

variable {N : ℕ}

/-- A monomial of `ℚ[S,T,D]` determines a (nonnegative) Laurent exponent. -/
def expEmb (N : ℕ) : (Var N →₀ ℕ) →+ Exponent N where
  toFun m := ⟨m Var.S, m Var.T, fun i => m (Var.D i)⟩
  map_zero' := by
    ext <;> simp
  map_add' m₁ m₂ := by
    ext <;> push_cast <;> simp

theorem expEmb_injective : Function.Injective (expEmb N) := by
  intro m₁ m₂ h
  ext v
  cases v with
  | S =>
      have h' : ((m₁ Var.S : ℕ) : ℤ) = ((m₂ Var.S : ℕ) : ℤ) := congrArg Exponent.s h
      exact_mod_cast h'
  | T =>
      have h' : ((m₁ Var.T : ℕ) : ℤ) = ((m₂ Var.T : ℕ) : ℤ) := congrArg Exponent.t h
      exact_mod_cast h'
  | D i =>
      have h' : ((m₁ (Var.D i) : ℕ) : ℤ) = ((m₂ (Var.D i) : ℕ) : ℤ) :=
        congrFun (congrArg Exponent.d h) i
      exact_mod_cast h'

/-- The support-preserving embedding `ℚ[S, T, D₁, …, D_N] → L_N`
[the paper: "the contraction `I_P = J_P ∩ ℚ[S,T,D]`"]. -/
noncomputable def toLaurent (N : ℕ) : MvPolynomial (Var N) ℚ →ₐ[ℚ] Laurent N :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (expEmb N)

theorem toLaurent_apply (p : MvPolynomial (Var N) ℚ) :
    toLaurent N p = Finsupp.mapDomain (expEmb N) p := rfl

theorem support_toLaurent (p : MvPolynomial (Var N) ℚ) :
    (toLaurent N p).support = Finset.image (expEmb N) p.support := by
  rw [toLaurent_apply]
  exact Finsupp.mapDomain_support_of_injective expEmb_injective p

theorem supportCard_toLaurent (p : MvPolynomial (Var N) ℚ) :
    (toLaurent N p).support.card = p.support.card := by
  rw [support_toLaurent]
  exact Finset.card_image_of_injective p.support expEmb_injective

theorem toLaurent_injective : Function.Injective (toLaurent N) := by
  intro p q hpq
  rw [toLaurent_apply, toLaurent_apply] at hpq
  exact Finsupp.mapDomain_injective expEmb_injective hpq

theorem toLaurent_ne_zero {p : MvPolynomial (Var N) ℚ} (hp : p ≠ 0) :
    toLaurent N p ≠ 0 := by
  intro h
  exact hp (toLaurent_injective (by simpa using h))

theorem toLaurent_single (m : Var N →₀ ℕ) (c : ℚ) :
    toLaurent N (AddMonoidAlgebra.single m c)
      = AddMonoidAlgebra.single (expEmb N m) c := by
  rw [toLaurent_apply]
  exact Finsupp.mapDomain_single

/-- The contraction `I_P = J_P ∩ ℚ[S,T,D]`  [proof of Theorem 4.5]. -/
noncomputable def polyReductionIdeal {M : ℕ}
    (Q : Fin M → BilinearFormMatrix (Option (Fin N))) : Ideal (MvPolynomial (Var N) ℚ) :=
  Ideal.comap (toLaurent N) (reductionIdeal Q)

theorem mem_polyReductionIdeal_iff {M : ℕ} {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    {p : MvPolynomial (Var N) ℚ} :
    p ∈ polyReductionIdeal Q ↔ toLaurent N p ∈ reductionIdeal Q :=
  Ideal.mem_comap

/-- Short polynomials of `I_P` are short polynomials of `J_P` (the embedding preserves
supports exactly). -/
theorem hasShort_of_hasShortPoly {M : ℕ} {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    {k : ℕ} (h : HasShortPoly k (polyReductionIdeal Q)) :
    HasShort k (reductionIdeal Q) := by
  obtain ⟨p, hp, hp0, hpc⟩ := h
  exact ⟨toLaurent N p, mem_polyReductionIdeal_iff.mp hp, toLaurent_ne_zero hp0,
    by rw [supportCard_toLaurent]; exact hpc⟩

/-! ### Clearing `τ_d` and `Ω` into polynomials -/

/-- The polynomial monomial with `D`-exponents `f`. -/
noncomputable def dMonExp (f : Fin N → ℕ) : Var N →₀ ℕ :=
  ∑ i, Finsupp.single (Var.D i) (f i)

theorem expEmb_dMonExp (f : Fin N → ℕ) :
    expEmb N (dMonExp f) = ⟨0, 0, fun i => (f i : ℤ)⟩ := by
  -- evaluate the coordinates of the sum of singles pointwise
  dsimp only [expEmb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ext <;> simp [dMonExp, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem expEmb_S_add_dMonExp (f : Fin N → ℕ) :
    expEmb N (Finsupp.single Var.S 1 + dMonExp f) = ⟨1, 0, fun i => (f i : ℤ)⟩ := by
  rw [map_add, expEmb_dMonExp]
  ext <;> simp [expEmb]

theorem expEmb_T_add_dMonExp (f : Fin N → ℕ) :
    expEmb N (Finsupp.single Var.T 1 + dMonExp f) = ⟨0, 1, fun i => (f i : ℤ)⟩ := by
  rw [map_add, expEmb_dMonExp]
  ext <;> simp [expEmb]

/-- The polynomial trinomial `D^{|d|} − S·D^{|d|+d} − T·D^{|d|−d}`, the clearing of
`τ_d` by the monomial `D^{|d|}`  [the paper: "Clearing of denominator type arguments"]. -/
noncomputable def tauPoly (d : Fin N → ℤ) : MvPolynomial (Var N) ℚ :=
  AddMonoidAlgebra.single (dMonExp fun i => (d i).toNat + (-d i).toNat) 1
    - AddMonoidAlgebra.single (Finsupp.single Var.S 1
        + dMonExp fun i => 2 * (d i).toNat) 1
    - AddMonoidAlgebra.single (Finsupp.single Var.T 1
        + dMonExp fun i => 2 * (-d i).toNat) 1

/-- `tauPoly d` maps to the unit multiple `D^{|d|}·τ_d` of the affine trinomial. -/
theorem toLaurent_tauPoly (d : Fin N → ℤ) :
    toLaurent N (tauPoly d)
      = mono ⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ * tau d := by
  have hz0 : expEmb N (dMonExp fun i => (d i).toNat + (-d i).toNat)
      = (⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ : Exponent N) := by
    rw [expEmb_dMonExp]
    ext
    · rfl
    · rfl
    · push_cast
      omega
  have h1 : expEmb N (Finsupp.single Var.S 1 + dMonExp fun i => 2 * (d i).toNat)
      = (⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ : Exponent N)
        + ⟨1, 0, d⟩ := by
    rw [expEmb_S_add_dMonExp]
    ext
    · simp
    · simp
    · simp only [Exponent.add_d, Pi.add_apply]
      push_cast
      omega
  have h2 : expEmb N (Finsupp.single Var.T 1 + dMonExp fun i => 2 * (-d i).toNat)
      = (⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ : Exponent N)
        + ⟨0, 1, -d⟩ := by
    rw [expEmb_T_add_dMonExp]
    ext
    · simp
    · simp
    · simp only [Exponent.add_d, Pi.add_apply, Pi.neg_apply]
      push_cast
      omega
  rw [tauPoly, map_sub, map_sub, toLaurent_single, toLaurent_single, toLaurent_single,
    hz0, h1, h2,
    show mono (⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ : Exponent N) * tau d
      = (1 : ℚ) • (mono ⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ * tau d) from
      (one_smul _ _).symm,
    smul_mono_mul_tau]

/-- A monomial multiple of `τ_d` has exactly three terms. -/
theorem supportCard_mono_mul_tau (z : Exponent N) (d : Fin N → ℤ) :
    (mono z * tau d).support.card = 3 := by
  rw [show mono z * tau d = (1 : ℚ) • (mono z * tau d) from (one_smul _ _).symm,
    smul_mono_mul_tau, sub_eq_add_neg, sub_eq_add_neg, ← singleNeg_eq, ← singleNeg_eq]
  have h1 : z ≠ z + (⟨1, 0, d⟩ : Exponent N) := by
    intro h
    have := congrArg Exponent.s h
    simp only [Exponent.add_s] at this
    omega
  have h2 : z ≠ z + (⟨0, 1, -d⟩ : Exponent N) := by
    intro h
    have := congrArg Exponent.t h
    simp only [Exponent.add_t] at this
    omega
  have h3 : z + (⟨1, 0, d⟩ : Exponent N) ≠ z + (⟨0, 1, -d⟩ : Exponent N) := by
    intro h
    have := congrArg Exponent.s h
    simp only [Exponent.add_s] at this
    omega
  rw [support_three h1 h2 h3 one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero)]
  exact card_three h1 h2 h3

/-- If the affine trinomial `τ_d` lies in `J_P`, then its clearing lies in `I_P`, and it
is an honest trinomial. -/
theorem hasShortPoly_three_of_tau {M : ℕ} {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    {d : Fin N → ℤ} (h : tau d ∈ reductionIdeal Q) :
    HasShortPoly 3 (polyReductionIdeal Q) := by
  have hcard : (tauPoly d).support.card = 3 := by
    rw [← supportCard_toLaurent, toLaurent_tauPoly, supportCard_mono_mul_tau]
  refine ⟨tauPoly d, ?_, ?_, le_of_eq hcard⟩
  · rw [mem_polyReductionIdeal_iff, toLaurent_tauPoly]
    exact Ideal.mul_mem_left _ _ h
  · intro h0
    rw [h0] at hcard
    simp at hcard

/-- The quadrinomial `Ω = S² − T² − S + T` as an ordinary polynomial. -/
noncomputable def OmegaPoly (N : ℕ) : MvPolynomial (Var N) ℚ :=
  AddMonoidAlgebra.single (Finsupp.single Var.S 2) 1
    - AddMonoidAlgebra.single (Finsupp.single Var.T 2) 1
    - AddMonoidAlgebra.single (Finsupp.single Var.S 1) 1
    + AddMonoidAlgebra.single (Finsupp.single Var.T 1) 1

theorem toLaurent_OmegaPoly : toLaurent N (OmegaPoly N) = Omega N := by
  rw [Omega_eq_singles, OmegaPoly, map_add, map_sub, map_sub, toLaurent_single,
    toLaurent_single, toLaurent_single, toLaurent_single]
  have e1 : expEmb N (Finsupp.single Var.S 2) = (⟨2, 0, 0⟩ : Exponent N) := by
    ext <;> simp [expEmb]
  have e2 : expEmb N (Finsupp.single Var.T 2) = (⟨0, 2, 0⟩ : Exponent N) := by
    ext <;> simp [expEmb]
  have e3 : expEmb N (Finsupp.single Var.S 1) = (⟨1, 0, 0⟩ : Exponent N) := by
    ext <;> simp [expEmb]
  have e4 : expEmb N (Finsupp.single Var.T 1) = (⟨0, 1, 0⟩ : Exponent N) := by
    ext <;> simp [expEmb]
  rw [e1, e2, e3, e4]
  rfl

open MvPolynomial in
theorem single_eq_X_pow (v : Var N) (e : ℕ) :
    (AddMonoidAlgebra.single (Finsupp.single v e) 1 : MvPolynomial (Var N) ℚ) = X v ^ e :=
  X_pow_eq_monomial.symm

open MvPolynomial in
/-- `Ω = S² − T² − S + T` in the variables of `ℚ[S, T, D]`. -/
theorem OmegaPoly_eq : OmegaPoly N = X Var.S ^ 2 - X Var.T ^ 2 - X Var.S + X Var.T := by
  rw [OmegaPoly, single_eq_X_pow, single_eq_X_pow, single_eq_X_pow, single_eq_X_pow, pow_one,
    pow_one]

open MvPolynomial in
/-- The monomial `D^f = ∏ᵢ Dᵢ^{fᵢ}` of `ℚ[S, T, D]`. -/
theorem monomial_dMonExp (f : Fin N → ℕ) :
    (monomial (dMonExp f) 1 : MvPolynomial (Var N) ℚ) = ∏ i, X (Var.D i) ^ f i := by
  rw [dMonExp, monomial_sum_index]
  simp only [X_pow_eq_monomial, C_1, one_mul]

open MvPolynomial in
/-- The cleared affine trinomial `τ̃_d = D^{|d|} − S·D^{|d|+d} − T·D^{|d|−d}` in the variables
of `ℚ[S, T, D]`, with `|d| + d = 2·d⁺` and `|d| − d = 2·d⁻` (`Int.toNat`). -/
theorem tauPoly_eq (d : Fin N → ℤ) :
    tauPoly d = (∏ i, X (Var.D i) ^ (d i).natAbs)
      - X Var.S * ∏ i, X (Var.D i) ^ (2 * (d i).toNat)
      - X Var.T * ∏ i, X (Var.D i) ^ (2 * (-d i).toNat) := by
  simp only [tauPoly, Int.toNat_add_toNat_neg_eq_natAbs,
    show ∀ (m : Var N →₀ ℕ) (c : ℚ),
      (AddMonoidAlgebra.single m c : MvPolynomial (Var N) ℚ) = monomial m c from fun _ _ => rfl]
  rw [← monomial_dMonExp, ← monomial_dMonExp, ← monomial_dMonExp, X, X, monomial_mul,
    monomial_mul, one_mul]

theorem hasShortPoly_four {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    HasShortPoly 4 (polyReductionIdeal Q) := by
  have hcard : (OmegaPoly N).support.card = 4 := by
    rw [← supportCard_toLaurent, toLaurent_OmegaPoly, supportCard_Omega]
  refine ⟨OmegaPoly N, ?_, ?_, le_of_eq hcard⟩
  · rw [mem_polyReductionIdeal_iff, toLaurent_OmegaPoly]
    exact Omega_mem_reductionIdeal Q
  · intro h0
    rw [h0] at hcard
    simp at hcard

end Trinomial
