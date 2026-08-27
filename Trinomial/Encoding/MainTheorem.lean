import Trinomial.Encoding.StraightLineProgram
import Trinomial.Encoding.Counting

/-!
# Theorem 4.5, assembled

[Theorem 4.5].  For a polynomial `P ∈ ℤ[y₁, …, yₙ]` given by its sparse syntax
`p : IntPolynomialCode n`, the algorithm is the composite

  `p ↦ straight line program (Lemma 4.1) ↦ guarded system (Lemma 4.2)
     ↦ quadratic forms `Q₁, …, Q_M` ↦ generators of `I_P` (linear algebra on the residues)`,

every step of which is an executable definition: `StraightLineProgram.ofCode`,
`degreeTwoSystem`, `guarded`, `homogenizedSystem`, `generators`.  The theorem
`theorem_main` states, for the ideal `I_P = polyIdeal p` of `ℚ[S, T, D₁, …, D_N]`:

* `generatorsOf p` is a list of at most `C(N+7,5)` generators of `I_P`, each of total
  degree `≤ 5`;
* `I_P` has Krull dimension zero, and is primary to the maximal ideal
  `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`;
* `I_P` contains no monomial and no binomial;
* `I_P` contains the quadrinomial `S² − T² − S + T`;
* every trinomial in `I_P` is a term times a cleared affine trinomial `τ̃_d`;
* `I_P` contains some `τ̃_d` iff `P` has an integral zero.

The exact value `t(I_P) ∈ {3, 4}` is `tinv_polyIdeal` in `Trinomial/Encoding/StraightLineProgram.lean`.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntPolynomialCode evalPolynomial)

variable {n : ℕ}

/-- The number `N` of variables `D_i` attached to `p`: the `n` inputs, the auxiliary
variables of the straight line program, and the six variables `h, k, u₁, …, u₄` of the
guards. -/
abbrev numVars (p : IntPolynomialCode n) : ℕ := n + (StraightLineProgram.ofCode p).k + 6

/-- The quadratic forms `Q₁, …, Q_M` attached to `p`: the homogenizations of the guarded
system of Lemma 4.2 applied to the degree-two system of Lemma 4.1
[proof of Theorem 4.5]. -/
def quadraticForms (p : IntPolynomialCode n) :
    Fin (guarded (degreeTwoSystem p)).length → BilinearFormMatrix (Option (Fin (numVars p))) :=
  homogenizedSystem (guarded (degreeTwoSystem p))

theorem polyIdeal_eq (p : IntPolynomialCode n) :
    polyIdeal p = polyReductionIdeal (quadraticForms p) := rfl

/-- **The algorithm of Theorem 4.5**: the generators of `I_P`, computed from the syntax of
`P`.  Each generator is a polynomial in the coordinates `s = 2S−1`, `t = 2T−1`,
`c_i = D_i − 1` (see `PointPoly`). -/
def generatorsOf (p : IntPolynomialCode n) : List (PointPoly (numVars p)) :=
  generators (quadraticForms p)

/-- A printable form of a generator: the pairs (coefficient, exponent list). -/
def PointPoly.display {N : ℕ} (l : PointPoly N) : List (ℚ × List ℕ) :=
  l.map fun t => (t.1, List.ofFn t.2)

theorem span_generatorsOf (p : IntPolynomialCode n) :
    Ideal.span {g | ∃ l ∈ generatorsOf p, g = l.toPoly} = polyIdeal p :=
  generatedIdeal_eq (quadraticForms p)

/-- The cleared affine trinomial `τ̃_d` lies in `I_P` whenever `d` solves the affine
system  [proof of Theorem 4.5]. -/
theorem tauPoly_mem_of_quadAt {N M : ℕ} {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    {d : Fin N → ℤ} (hd : ∀ i, quadAt (Q i) (ratCast d) 1 = 0) :
    tauPoly d ∈ polyReductionIdeal Q := by
  rw [mem_polyReductionIdeal_iff, toLaurent_tauPoly]
  exact Ideal.mul_mem_left _ _ ((tau_mem_reductionIdeal_iff Q d).mpr hd)

theorem supportCard_tauPoly {N : ℕ} (d : Fin N → ℤ) : (tauPoly d).support.card = 3 := by
  rw [← supportCard_toLaurent, toLaurent_tauPoly, supportCard_mono_mul_tau]

/-- `I_P` contains a cleared affine trinomial iff `P` has an integral zero
[Theorem 4.5, last bullet]. -/
theorem exists_tauPoly_mem_iff (p : IntPolynomialCode n) :
    (∃ d : Fin (numVars p) → ℤ, tauPoly d ∈ polyIdeal p)
      ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0 := by
  constructor
  · rintro ⟨d, hd⟩
    refine (main_theorem_code p).2.1.mp ⟨tauPoly d, hd, ?_, le_of_eq (supportCard_tauPoly d)⟩
    intro h0
    have := supportCard_tauPoly d
    rw [h0] at this
    simp at this
  · intro hy
    rw [← degreeTwoSystem_solvable_iff, ← guarded_solvable_iff, ← homogenizedSystem_affine_iff] at hy
    obtain ⟨d, hd⟩ := hy
    exact ⟨d, tauPoly_mem_of_quadAt hd⟩

/-- **Theorem 4.5**  [Theorem 4.5].  For every `P ∈ ℤ[y₁, …, yₙ]` (given by its
syntax `p`), the computed list `generatorsOf p` generates an ideal `I_P = polyIdeal p` of
`ℚ[S, T, D₁, …, D_N]`, `N = numVars p`, such that

1. `I_P` has Krull dimension zero; it is primary to `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`;
2. `I_P` contains no monomial and no binomial;
3. `I_P` contains the quadrinomial `Ω = S² − T² − S + T`;
4. every trinomial in `I_P` is a term times a cleared affine trinomial `τ̃_d`;
5. `I_P` contains some `τ̃_d` if and only if `P` has an integral zero.

The list has at most `C(N+7,5)` entries (`generators_length_le`), every generator has total
degree at most five (`generators_degree_le`), and `t(I_P) = 3` or `4` according to whether
`P` has an integral zero (`tinv_polyIdeal`). -/
theorem theorem_main (p : IntPolynomialCode n) :
    Ideal.span {g | ∃ l ∈ generatorsOf p, g = l.toPoly} = polyIdeal p
    ∧ (generatorsOf p).length ≤ Nat.choose (numVars p + 7) 5
    ∧ ringKrullDim (MvPolynomial (Var (numVars p)) ℚ ⧸ polyIdeal p) = 0
    ∧ (polyIdeal p).IsPrimary ∧ (polyIdeal p).radical = pointIdeal (numVars p)
    ∧ ¬ HasShortPoly 2 (polyIdeal p)
    ∧ OmegaPoly (numVars p) ∈ polyIdeal p
    ∧ (∀ f ∈ polyIdeal p, f.support.card = 3 →
        ∃ (c : ℚ) (m : Var (numVars p) →₀ ℕ) (d : Fin (numVars p) → ℤ),
          c ≠ 0 ∧ f = c • (MvPolynomial.monomial m 1 * tauPoly d))
    ∧ ((∃ d : Fin (numVars p) → ℤ, tauPoly d ∈ polyIdeal p)
        ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0) := by
  refine ⟨span_generatorsOf p, generators_length_le _, ringKrullDim_quotient _,
    polyReductionIdeal_isPrimary _, radical_polyReductionIdeal _, (main_theorem_code p).1,
    ?_, ?_, exists_tauPoly_mem_iff p⟩
  · rw [polyIdeal_eq, mem_polyReductionIdeal_iff, toLaurent_OmegaPoly]
    exact Omega_mem_reductionIdeal _
  · intro f hf h3
    obtain ⟨c, m, d, hc, heq, -⟩ := trinomial_in_polyReductionIdeal
      (noIntegralSolutionAtInfinity_homogenizedSystem _) hf h3
    exact ⟨c, m, d, hc, heq⟩

end Trinomial
