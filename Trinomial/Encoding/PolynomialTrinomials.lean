import Trinomial.Encoding.PolynomialSide

/-!
# Theorem 4.5, fourth bullet: the trinomials of `I_P`

[Theorem 4.5, fourth bullet, and the last paragraph of its proof].  Every
trinomial `f` of the contraction `I_P = J_P ∩ ℚ[S,T,D]` is a term times a cleared affine
trinomial: as a trinomial of `J_P` it has the form `f = c S^a T^b D^m τ_d` with a nonzero
scalar `c`; since all three exponent vectors of the *polynomial* `f` are nonnegative,
`a, b ≥ 0` and `m ≥ |d|` componentwise, hence `f = c S^a T^b D^{m−|d|} τ̃_d`.

* `nonneg_of_mem_support_toLaurent` — the exponent vectors of an ordinary polynomial are
  nonnegative;
* `support_smul_mono_mul_tau` — the three exponents of a term times `τ_d`;
* `expEmb_S_T_add_dMonExp` — the exponent of a polynomial monomial `S^a T^b D^f`;
* `trinomial_in_polyReductionIdeal` — **Theorem 4.5, fourth bullet**;
* `reductionIdeal_ne_top`, `polyReductionIdeal_ne_top` — `J_P` and `I_P` are proper ideals.
-/

set_option autoImplicit false

namespace Trinomial

variable {N : ℕ}

/-! ### Exponents of ordinary polynomials are nonnegative -/

/-- The exponent vectors of an ordinary polynomial, viewed in `L_N`, are nonnegative
componentwise  [proof of Theorem 4.5: "all three exponent vectors of the
polynomial `f` are nonnegative"]. -/
theorem nonneg_of_mem_support_toLaurent {p : MvPolynomial (Var N) ℚ} {x : Exponent N}
    (hx : x ∈ (toLaurent N p).support) :
    0 ≤ x.s ∧ 0 ≤ x.t ∧ ∀ j, 0 ≤ x.d j := by
  rw [support_toLaurent, Finset.mem_image] at hx
  obtain ⟨m, -, rfl⟩ := hx
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, fun j => Int.natCast_nonneg _⟩

/-- The support of a term times `τ_d`: the three exponents `z`, `z + (1, 0, d)` and
`z + (0, 1, −d)` of `c S^z τ_d`. -/
theorem support_smul_mono_mul_tau {c : ℚ} (hc : c ≠ 0) (z : Exponent N) (d : Fin N → ℤ) :
    (c • (mono z * tau d)).support = {z, z + ⟨1, 0, d⟩, z + ⟨0, 1, -d⟩} := by
  rw [smul_mono_mul_tau, sub_eq_add_neg, sub_eq_add_neg, ← singleNeg_eq, ← singleNeg_eq]
  refine support_three ?_ ?_ ?_ hc (neg_ne_zero.mpr hc) (neg_ne_zero.mpr hc)
  · intro h
    have := congrArg Exponent.s h
    simp only [Exponent.add_s] at this
    omega
  · intro h
    have := congrArg Exponent.t h
    simp only [Exponent.add_t] at this
    omega
  · intro h
    have := congrArg Exponent.s h
    simp only [Exponent.add_s] at this
    omega

/-! ### Polynomial monomials and their exponents -/

/-- The exponent of the polynomial monomial `S^a T^b D^f`. -/
theorem expEmb_S_T_add_dMonExp (a b : ℕ) (f : Fin N → ℕ) :
    expEmb N (Finsupp.single Var.S a + Finsupp.single Var.T b + dMonExp f)
      = ⟨a, b, fun i => (f i : ℤ)⟩ := by
  rw [map_add, map_add, expEmb_dMonExp]
  ext <;> simp [expEmb]

/-- `toLaurent` sends the polynomial monomial `X^m` to the Laurent monomial with the same
exponent. -/
theorem toLaurent_monomial_one (m : Var N →₀ ℕ) :
    toLaurent N (MvPolynomial.monomial m 1) = mono (expEmb N m) :=
  toLaurent_single m 1

/-- The exponent identity behind the clearing `S^a T^b D^m τ_d = S^a T^b D^{m−|d|} τ̃_d`:
if `z = (a, b, m)` is nonnegative in `a`, `b` and satisfies `m ≥ |d|` componentwise
(equivalently `m + d ≥ 0` and `m − d ≥ 0`), then `z` is the exponent of the polynomial
monomial `S^a T^b D^{m−|d|}` plus `|d|`  [proof of Theorem 4.5]. -/
theorem expEmb_clearing_monomial (z : Exponent N) (d : Fin N → ℤ) (hs : 0 ≤ z.s)
    (ht : 0 ≤ z.t) (hd₁ : ∀ j, 0 ≤ z.d j + d j) (hd₂ : ∀ j, 0 ≤ z.d j - d j) :
    expEmb N (Finsupp.single Var.S z.s.toNat + Finsupp.single Var.T z.t.toNat
        + dMonExp fun j => (z.d j - ((d j).toNat + (-d j).toNat)).toNat)
      + ⟨0, 0, fun i => ((d i).toNat + (-d i).toNat : ℤ)⟩ = z := by
  rw [expEmb_S_T_add_dMonExp]
  ext
  · simp only [Exponent.add_s, add_zero]
    omega
  · simp only [Exponent.add_t, add_zero]
    omega
  · rename_i j
    simp only [Exponent.add_d, Pi.add_apply]
    have h₁ := hd₁ j
    have h₂ := hd₂ j
    omega

/-! ### Theorem 4.5, fourth bullet -/

/-- **Theorem 4.5, fourth bullet**: every trinomial of `I_P` is a term (nonzero scalar
times a monomial of `ℚ[S,T,D]`) times the clearing `τ̃_d` of an affine trinomial whose
exponent `d` solves the affine system  [Theorem 4.5 and the last paragraph of its
proof]. -/
theorem trinomial_in_polyReductionIdeal {N M : ℕ}
    {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    (guard : NoIntegralSolutionAtInfinity Q) {f : MvPolynomial (Var N) ℚ}
    (hf : f ∈ polyReductionIdeal Q) (h3 : f.support.card = 3) :
    ∃ (c : ℚ) (m : Var N →₀ ℕ) (d : Fin N → ℤ), c ≠ 0 ∧
      f = c • (MvPolynomial.monomial m 1 * tauPoly d) ∧
      ∀ i, quadAt (Q i) (ratCast d) 1 = 0 := by
  -- `f` is a trinomial of `J_P`, hence `f = c S^z τ_d` with `d` solving the affine system
  have hfL : toLaurent N f ∈ reductionIdeal Q := mem_polyReductionIdeal_iff.mp hf
  have h3L : (toLaurent N f).support.card = 3 := by
    rw [supportCard_toLaurent]
    exact h3
  obtain ⟨c, z, d, hc, heq, hquad⟩ := trinomial_in_reductionIdeal guard hfL h3L
  -- the three exponents `z`, `z + (1,0,d)`, `z + (0,1,−d)` are exponents of the
  -- polynomial `f`, hence nonnegative
  have hsupp := support_smul_mono_mul_tau hc z d
  have h₀ : z ∈ (toLaurent N f).support := by
    rw [heq, hsupp]
    simp
  have h₁ : z + ⟨1, 0, d⟩ ∈ (toLaurent N f).support := by
    rw [heq, hsupp]
    simp
  have h₂ : z + ⟨0, 1, -d⟩ ∈ (toLaurent N f).support := by
    rw [heq, hsupp]
    simp
  obtain ⟨hs, ht, -⟩ := nonneg_of_mem_support_toLaurent h₀
  obtain ⟨-, -, hd₁⟩ := nonneg_of_mem_support_toLaurent h₁
  obtain ⟨-, -, hd₂⟩ := nonneg_of_mem_support_toLaurent h₂
  simp only [Exponent.add_d, Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg] at hd₁ hd₂
  -- the polynomial monomial `S^a T^b D^{m−|d|}`
  refine ⟨c, Finsupp.single Var.S z.s.toNat + Finsupp.single Var.T z.t.toNat
      + dMonExp fun j => (z.d j - ((d j).toNat + (-d j).toNat)).toNat, d, hc, ?_, hquad⟩
  apply toLaurent_injective
  rw [heq, map_smul, map_mul, toLaurent_tauPoly, toLaurent_monomial_one, ← mul_assoc,
    mono_mul, expEmb_clearing_monomial z d hs ht hd₁ hd₂]

/-- `J_P` is a proper ideal: it contains no monomial, in particular not `1`
[Theorem 4.5, second bullet]. -/
theorem reductionIdeal_ne_top {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    reductionIdeal Q ≠ ⊤ := by
  intro h
  apply not_hasShort_two Q
  refine ⟨1, (Ideal.eq_top_iff_one _).mp h, one_ne_zero, ?_⟩
  rw [AddMonoidAlgebra.one_def, Finsupp.support_single_ne_zero 0 one_ne_zero,
    Finset.card_singleton]
  norm_num

/-- `I_P` is a proper ideal: it contains no monomial, in particular not `1`
[Theorem 4.5, second bullet]. -/
theorem polyReductionIdeal_ne_top {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    polyReductionIdeal Q ≠ ⊤ :=
  Ideal.comap_ne_top _ (reductionIdeal_ne_top Q)

end Trinomial
