import Trinomial.Encoding.PolynomialSide
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# The coordinates `s, t, c` and the decomposition of a polynomial at the point
`(S, T, D) = (1/2, 1/2, 1, …, 1)`

[Section 2 (the radical `√J₀ = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`) and
Corollary 5.1 (the maximal ideal `m`)].  Put `s = 2S − 1`, `t = 2T − 1`,
`c_i = D_i − 1`.  These are affine coordinates of `ℚ[S, T, D]`: every polynomial is
uniquely a polynomial in `s, t, c`, and `m = ⟨s, t, c₁, …, c_N⟩` is the maximal ideal of
the point `(1/2, 1/2, 1, …, 1)`.  Splitting the `s,t,c`-expansion of `f` by degree gives

  `f = f_{≤4} + f_{≥5}`,   `f_{≤4} ∈ W₄`,   `f_{≥5} ∈ m⁵`,

where `W₄` is the span of the finitely many products `s^a t^b c^γ` with `a + b + |γ| ≤ 4`
(`exists_lowDegree_sub_mem_pow_five`).  Together with `m⁵ ⊆ I_P` (proved in
`Trinomial/Encoding/ZeroDimensional.lean`) this reduces the computation of generators of `I_P` to
linear algebra on `W₄` (the paper's `W`; proof of Theorem 4.5, eq. (7)).

* `pointGen N : Fin (2 + N) → ℚ[S,T,D]` — the generators `s, t, c₁, …, c_N` of `m`;
* `toPointCoords N` — the substitution `S ↦ (s+1)/2`, `T ↦ (t+1)/2`, `D_i ↦ c_i + 1`
  expressing `f` in the coordinates `s, t, c`, with `aeval_pointGen_toPointCoords`;
* `exponentsLE k d` — the executable list of exponent vectors `e : Fin k → ℕ` with
  `∑ e_i ≤ d`, and `pointMonomial N e = ∏ (pointGen N i)^{e i}`;
* `lowDegreeSpan N` — `W₄`;
* `exists_lowDegree_sub_mem_pow_five` — the decomposition.
-/

set_option autoImplicit false

namespace Trinomial

open MvPolynomial

variable {N : ℕ}

/-- The generators `s = 2S−1`, `t = 2T−1`, `c_i = D_i − 1` of the maximal ideal `m`
[Corollary 5.1], indexed by `Fin (2 + N)`: position `0` is `s`, position
`1` is `t`, position `2 + i` is `c_i`. -/
noncomputable def pointGen (N : ℕ) : Fin (2 + N) → MvPolynomial (Var N) ℚ :=
  Fin.append ![2 * X Var.S - 1, 2 * X Var.T - 1] (fun i => X (Var.D i) - 1)

@[simp] theorem pointGen_zero : pointGen N (Fin.castAdd N 0) = 2 * X Var.S - 1 := by
  simp [pointGen, Fin.append_left]

@[simp] theorem pointGen_one : pointGen N (Fin.castAdd N 1) = 2 * X Var.T - 1 := by
  simp [pointGen, Fin.append_left]

@[simp] theorem pointGen_natAdd (i : Fin N) : pointGen N (Fin.natAdd 2 i) = X (Var.D i) - 1 := by
  simp [pointGen, Fin.append_right]

/-- The substitution `S ↦ (s + 1)/2`, `T ↦ (t + 1)/2`, `D_i ↦ c_i + 1`, which writes a
polynomial in `S, T, D` as a polynomial in the coordinates `s, t, c`. -/
noncomputable def toPointCoords (N : ℕ) :
    MvPolynomial (Var N) ℚ →ₐ[ℚ] MvPolynomial (Fin (2 + N)) ℚ :=
  aeval fun v => match v with
    | Var.S => C (1 / 2 : ℚ) * (X (Fin.castAdd N 0) + 1)
    | Var.T => C (1 / 2 : ℚ) * (X (Fin.castAdd N 1) + 1)
    | Var.D i => X (Fin.natAdd 2 i) + 1

/-- Substituting `s = 2S − 1`, … back recovers `f`. -/
theorem aeval_pointGen_toPointCoords (f : MvPolynomial (Var N) ℚ) :
    aeval (pointGen N) (toPointCoords N f) = f := by
  have h : (aeval (pointGen N)).comp (toPointCoords N) = AlgHom.id ℚ (MvPolynomial (Var N) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro v
    cases v with
    | S =>
        simp only [AlgHom.comp_apply, toPointCoords, aeval_X, AlgHom.id_apply, map_mul,
          map_add, map_one, algHom_C, pointGen_zero]
        rw [show (algebraMap ℚ (MvPolynomial (Var N) ℚ)) (1 / 2) = C (1 / 2) from rfl]
        have h2 : (C (1 / 2 : ℚ) : MvPolynomial (Var N) ℚ) * 2 = 1 := by
          rw [show (2 : MvPolynomial (Var N) ℚ) = C 2 from rfl, ← C_mul]
          norm_num
        linear_combination X Var.S * h2
    | T =>
        simp only [AlgHom.comp_apply, toPointCoords, aeval_X, AlgHom.id_apply, map_mul,
          map_add, map_one, algHom_C, pointGen_one]
        rw [show (algebraMap ℚ (MvPolynomial (Var N) ℚ)) (1 / 2) = C (1 / 2) from rfl]
        have h2 : (C (1 / 2 : ℚ) : MvPolynomial (Var N) ℚ) * 2 = 1 := by
          rw [show (2 : MvPolynomial (Var N) ℚ) = C 2 from rfl, ← C_mul]
          norm_num
        linear_combination X Var.T * h2
    | D i =>
        simp [toPointCoords, pointGen_natAdd]
  exact DFunLike.congr_fun h f

/-! ### Exponent vectors of bounded degree, as an executable list -/

/-- The exponent vectors `e : Fin k → ℕ` with `∑ e_i ≤ d`, listed degree by degree. -/
def exponentsLE (k d : ℕ) : List (Fin k → ℕ) :=
  (List.range (d + 1)).flatMap (List.Nat.antidiagonalTuple k)

theorem mem_exponentsLE {k d : ℕ} {e : Fin k → ℕ} : e ∈ exponentsLE k d ↔ ∑ i, e i ≤ d := by
  simp only [exponentsLE, List.mem_flatMap, List.mem_range, List.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · intro h
    exact ⟨_, by omega, rfl⟩

/-- The exponent vectors `e : Fin k → ℕ` with `∑ e_i = d`. -/
def exponentsEQ (k d : ℕ) : List (Fin k → ℕ) :=
  List.Nat.antidiagonalTuple k d

theorem mem_exponentsEQ {k d : ℕ} {e : Fin k → ℕ} : e ∈ exponentsEQ k d ↔ ∑ i, e i = d :=
  List.Nat.mem_antidiagonalTuple

/-- The product `s^{e 0} t^{e 1} c₁^{e 2} ⋯ c_N^{e (N+1)}`. -/
noncomputable def pointMonomial (N : ℕ) (e : Fin (2 + N) → ℕ) : MvPolynomial (Var N) ℚ :=
  ∏ i, pointGen N i ^ e i

theorem aeval_pointGen_monomial (u : Fin (2 + N) →₀ ℕ) (a : ℚ) :
    aeval (pointGen N) (monomial u a) = a • pointMonomial N u := by
  rw [aeval_monomial, Algebra.smul_def]
  congr 1
  rw [pointMonomial, Finsupp.prod_fintype _ _ fun i => pow_zero _]

/-- A product of elements of an ideal lies in the corresponding power of the ideal. -/
theorem prod_pow_mem_pow_sum {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*}
    (s : Finset ι) (g : ι → R) (hg : ∀ i, g i ∈ I) (e : ι → ℕ) :
    ∏ i ∈ s, g i ^ e i ∈ I ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hg a) _) ih

theorem pointGen_mem_span (i : Fin (2 + N)) : pointGen N i ∈ Ideal.span (Set.range (pointGen N)) :=
  Ideal.subset_span ⟨i, rfl⟩

/-- A product of at least five of the generators of `m` lies in `m⁵`. -/
theorem pointMonomial_mem_pow_five (e : Fin (2 + N) → ℕ) (h : 5 ≤ ∑ i, e i) :
    pointMonomial N e ∈ Ideal.span (Set.range (pointGen N)) ^ 5 :=
  Ideal.pow_le_pow_right h (prod_pow_mem_pow_sum _ _ _ pointGen_mem_span e)

/-- The exponent vectors of the products `s^a t^b c^γ` with `a + b + |γ| ≤ 4`, listed. -/
def lowMonomials (N : ℕ) : List (Fin (2 + N) → ℕ) := exponentsLE (2 + N) 4

/-- The `j`-th exponent vector of degree `≤ 4`. -/
def lowMonomial (N : ℕ) (j : Fin (lowMonomials N).length) : Fin (2 + N) → ℕ :=
  (lowMonomials N).get j

theorem mem_lowMonomials {e : Fin (2 + N) → ℕ} : e ∈ lowMonomials N ↔ ∑ i, e i ≤ 4 :=
  mem_exponentsLE

/-- `W₄`: the span of the products `s^a t^b c^γ` with `a + b + |γ| ≤ 4`, indexed by the
list `lowMonomials N`. -/
noncomputable def lowDegreeSpan (N : ℕ) : Submodule ℚ (MvPolynomial (Var N) ℚ) :=
  Submodule.span ℚ (Set.range fun j => pointMonomial N (lowMonomial N j))

/-- **The decomposition** `f = f_{≤4} + f_{≥5}`: every polynomial is an element of `W₄`
plus an element of `m⁵`  [proof of Theorem 4.5]. -/
theorem exists_lowDegree_sub_mem_pow_five (f : MvPolynomial (Var N) ℚ) :
    ∃ g ∈ lowDegreeSpan N, f - g ∈ Ideal.span (Set.range (pointGen N)) ^ 5 := by
  suffices h : ∀ F : MvPolynomial (Fin (2 + N)) ℚ, ∃ g ∈ lowDegreeSpan N,
      aeval (pointGen N) F - g ∈ Ideal.span (Set.range (pointGen N)) ^ 5 by
    obtain ⟨g, hg, hmem⟩ := h (toPointCoords N f)
    rw [aeval_pointGen_toPointCoords] at hmem
    exact ⟨g, hg, hmem⟩
  intro F
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
      rw [aeval_pointGen_monomial]
      by_cases hu : ∑ i, u i ≤ 4
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp (mem_lowMonomials.mpr hu)
        refine ⟨a • pointMonomial N u, Submodule.smul_mem _ _
          (Submodule.subset_span ⟨j, by simp only [lowMonomial, hj]⟩), ?_⟩
        rw [sub_self]
        exact Submodule.zero_mem _
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [sub_zero, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (pointMonomial_mem_pow_five u (by omega))
  | add p q hp hq =>
      obtain ⟨g₁, hg₁, h₁⟩ := hp
      obtain ⟨g₂, hg₂, h₂⟩ := hq
      refine ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, ?_⟩
      rw [map_add, show aeval (pointGen N) p + aeval (pointGen N) q - (g₁ + g₂)
        = (aeval (pointGen N) p - g₁) + (aeval (pointGen N) q - g₂) by ring]
      exact Ideal.add_mem _ h₁ h₂

end Trinomial
