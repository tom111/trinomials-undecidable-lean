import Trinomial.Universal.MRDP
import Trinomial.Encoding.MainTheorem
import Trinomial.Encoding.Counting
import TrinomialUndecidability.Computability.EffectiveDiophantineSingle

/-!
# Corollary 5.1 in one fixed polynomial ring

[§5, Corollary 5.1].  The corollary asks for *one* polynomial ring
`ℚ[S, T, D₁, …, D_N]` and a computable family of ideals `I_e`, indexed by program codes `e`,
with `t(I_e) = 3` if machine `e` halts on input `0` and `t(I_e) = 4` otherwise, each `I_e`
primary to `𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_N−1⟩`, with a presentation of uniformly bounded size.

The proof of the corollary reads: "Substituting the constant `e` for the variable `E` in
one fixed straight line program for `U`, without simplifying, gives programs of the same
shape for every `e`."  We follow this at the level of syntax, for an *arbitrary* effective
Diophantine relation `R` in one free variable (a finite list of integer polynomials in the
free variable `X₀` and `R.aux` auxiliary variables):

* `frozenCode R e` — the sparse syntax of `U(e, Y) = Σᵢ Rᵢ(Y)² + (X₀ − e)²` (the paper's
  `P_e`), built with the vendored syntactic addition, multiplication, and sum of squares
  **without simplification**, so that the list of exponent vectors is the same for every `e`
  (`frozenCode_shape`); only the coefficients depend on `e`.  The parameter `X₀` is kept as
  a variable and pinned to `e` by the extra square, a variant of the paper's substitution
  with the same zero set (`frozenCode_zero_iff`).
* `Universal.k₀ R`, `Universal.N₀ R`, `Universal.M₀ R` — the numbers of auxiliary
  variables, of variables `D_i`, and of quadratic forms; by `shape_ofCode` they are the same
  for every `e` (`Universal.k_eq`, `Universal.length_guarded_system`).
* `Universal.system R e` — the degree-two system of Lemma 4.1 for `frozenCode R e`,
  reindexed to the fixed variable set; `Universal.ideal R e ⊆ ℚ[S, T, D₁, …, D_{N₀ R}]` —
  the ideal `I_e` of the corollary; `Universal.generators R e` — its computed presentation.
* The properties of Corollary 5.1, for every `R` and `e`:
  `Universal.tinv_ideal` (`t(I_e) = 3` if `R` holds at `e`, `4` otherwise),
  `Universal.ideal_isPrimary`, `Universal.radical_ideal`, `Universal.ringKrullDim_ideal`,
  `Universal.ideal_ne_top`, `Universal.span_generators`,
  `Universal.generators_degree_le` (degree `≤ 5`), `Universal.generators_length_le`
  (at most `C(N₀+7, 5)` generators), `Universal.finrank_quotient_le` (colength
  `≤ (N₀+5) + M₀(N₀+3)`, the paper's `C`) and `Universal.finrank_quotient_le_choose`
  (colength `≤ C(N₀+6, 4)`).

**What is executable.**  Everything in the namespace `Universal` is an executable definition
of its inputs `R` and `e`: `Universal.generators : EffDiophRel 1 → ℕ → List (PointPoly _)` is
a plain `def`.  This is the formal content of "a computable sequence of ideals": the
presentation of `I_e` is computed from `e` by an algorithm, uniformly in the universal
polynomial.  The universal polynomial itself, `MRDP.haltingRel` (the paper's `U`, which the
paper also does not exhibit), is a fixed, classically chosen relation obtained from mathlib's
`Dioph` proof through the vendored bridge, so the instances `haltingIdeal`,
`haltingGenerators` below are `noncomputable` through that single input only.  Mathlib's
notion `Computable` is not applied to `e ↦ haltingGenerators e`; see `README.md`.

**The halting instance.**  `haltingIdeal e = Universal.ideal haltingRel e` in the fixed ring
`ℚ[S, T, D₁, …, D_{N₀}]`, with `haltingIdeal_tinv` (the two values of `t(I_e)`),
`haltingIdeal_isPrimary`, `radical_haltingIdeal`, `ringKrullDim_haltingIdeal`,
`haltingIdeal_ne_top`, the presentation `haltingGenerators e` with `span_haltingGenerators`,
`haltingGenerators_degree_le`, `haltingGenerators_length_le_choose`, the colength bounds
`finrank_haltingIdeal_le`, `finrank_haltingIdeal_le_choose`, and the undecidability of the
index predicate `e ↦ [t(I_e) = 3]` (`haltingIdeal_not_computable`).  The halting set is
mathlib's: machine `e` is the `e`-th partial recursive code `Denumerable.ofNat Code e`, and
"halts on input `0`" is `(Code.eval c 0).Dom` (`HaltsAtZero`).
-/

set_option autoImplicit false

namespace Trinomial

open Nat.Partrec (Code)
open TrinomialUndecidability.Computability (IntExponent IntPolynomialCode IntPolynomialSystem
  EffDiophRel Satisfies evalMonomial evalPolynomial)
open TrinomialUndecidability.Computability.EffDiophRel (variableExponent addExponent
  addPolynomial monomialMulPolynomial mulPolynomial squarePolynomial sumSquares
  eval_addPolynomial eval_squarePolynomial eval_sumSquares_nonneg
  eval_sumSquares_eq_zero_iff_satisfies)
open TrinomialUndecidability.Computability.HaltingEvalnBridge (HaltsAtZero)
open MRDP (haltingRel haltingRel_spec)

/-! ### The exponent vectors of the syntactic operations do not depend on the coefficients

The vendored sparse syntax keeps duplicate monomials and zero coefficients
(`TrinomialUndecidability/Computability/EffectiveDiophantineSingle.lean`); its addition is
list concatenation and its multiplication distributes term by term.  Consequently the list
of exponent vectors of a sum or product is determined by the lists of exponent vectors of
the factors: "without simplifying" [proof of Corollary 5.1]. -/

theorem map_fst_addPolynomial {n : ℕ} (p q : IntPolynomialCode n) :
    (addPolynomial p q).map Prod.fst = p.map Prod.fst ++ q.map Prod.fst :=
  List.map_append ..

theorem map_fst_monomialMulPolynomial {n : ℕ} (e : IntExponent n) (c : ℤ)
    (q : IntPolynomialCode n) :
    (monomialMulPolynomial e c q).map Prod.fst = (q.map Prod.fst).map (addExponent e) := by
  simp only [monomialMulPolynomial, List.map_map]
  rfl

/-- Two products of polynomials with the same exponent lists have the same exponent list. -/
theorem map_fst_mulPolynomial {n : ℕ} {p p' q q' : IntPolynomialCode n}
    (hp : p.map Prod.fst = p'.map Prod.fst) (hq : q.map Prod.fst = q'.map Prod.fst) :
    (mulPolynomial p q).map Prod.fst = (mulPolynomial p' q').map Prod.fst := by
  induction p generalizing p' with
  | nil =>
      cases p' with
      | nil => rfl
      | cons _ _ => simp at hp
  | cons t p ih =>
      cases p' with
      | nil => simp at hp
      | cons t' p' =>
          obtain ⟨e, c⟩ := t
          obtain ⟨e', c'⟩ := t'
          simp only [List.map_cons, List.cons.injEq] at hp
          obtain ⟨rfl, hpp'⟩ := hp
          rw [mulPolynomial, mulPolynomial, map_fst_addPolynomial, map_fst_addPolynomial,
            map_fst_monomialMulPolynomial, map_fst_monomialMulPolynomial, hq, ih hpp']

theorem map_fst_squarePolynomial {n : ℕ} {p p' : IntPolynomialCode n}
    (hp : p.map Prod.fst = p'.map Prod.fst) :
    (squarePolynomial p).map Prod.fst = (squarePolynomial p').map Prod.fst :=
  map_fst_mulPolynomial hp hp

/-! ### The syntax of `U(e, Y)`: the parameter frozen at `e` -/

/-- The linear syntax `X_i − e`, as a list of two terms: the monomial `X_i` with
coefficient `1` and the constant monomial with coefficient `−e`. -/
def freezeCode {n : ℕ} (i : Fin n) (e : ℕ) : IntPolynomialCode n :=
  [(variableExponent i, 1), (fun _ => 0, -(e : ℤ))]

theorem freezeCode_shape {n : ℕ} (i : Fin n) (e : ℕ) :
    (freezeCode i e).map Prod.fst = (freezeCode i 0).map Prod.fst := rfl

theorem eval_freezeCode {n : ℕ} (i : Fin n) (e : ℕ) (x : Fin n → ℤ) :
    evalPolynomial (freezeCode i e) x = x i - e := by
  simp only [freezeCode, evalPolynomial, EffDiophRel.evalMonomial_variableExponent]
  simp [evalMonomial, sub_eq_add_neg]

/-- The sparse syntax of `U(e, Y) = Σᵢ Rᵢ(Y)² + (X₀ − e)²` for an effective Diophantine
relation `R` in one free variable (the parameter `X₀`) and `R.aux` auxiliary variables
[§5, eq. (8)]: the syntactic sum of the squares of the equations
of `R` plus the syntactic square of `X₀ − e`, **without simplification**.  Executable; only
the coefficients depend on `e` (`frozenCode_shape`). -/
def frozenCode (R : EffDiophRel 1) (e : ℕ) : IntPolynomialCode (1 + R.aux) :=
  addPolynomial (sumSquares R.eqs) (squarePolynomial (freezeCode (Fin.castAdd R.aux 0) e))

/-- The list of exponent vectors of `frozenCode R e` does not depend on `e`
[proof of Corollary 5.1: "without simplifying, gives programs of the same
shape for every `e`"]. -/
theorem frozenCode_shape (R : EffDiophRel 1) (e : ℕ) :
    (frozenCode R e).map Prod.fst = (frozenCode R 0).map Prod.fst := by
  rw [frozenCode, frozenCode, map_fst_addPolynomial, map_fst_addPolynomial,
    map_fst_squarePolynomial (freezeCode_shape _ e)]

theorem eval_frozenCode (R : EffDiophRel 1) (e : ℕ) (x : Fin (1 + R.aux) → ℤ) :
    evalPolynomial (frozenCode R e) x
      = evalPolynomial (sumSquares R.eqs) x + (x (Fin.castAdd R.aux 0) - e) ^ 2 := by
  rw [frozenCode, eval_addPolynomial, eval_squarePolynomial, eval_freezeCode, sq]

/-- `U(e, Y)` has an integral zero iff the relation `R` holds at `e`
[§5, eq. (8): `e ∈ K₀ ⟺ ∃ y ∈ ℤ^r : U(e, y) = 0`]. -/
theorem frozenCode_zero_iff (R : EffDiophRel 1) (e : ℕ) :
    (∃ x : Fin (1 + R.aux) → ℤ, evalPolynomial (frozenCode R e) x = 0)
      ↔ R.Realizes (fun _ => (e : ℤ)) := by
  have heval : ∀ x : Fin (1 + R.aux) → ℤ,
      evalPolynomial (frozenCode R e) x = 0 ↔
        Satisfies R.eqs x ∧ x (Fin.castAdd R.aux 0) = (e : ℤ) := by
    intro x
    rw [eval_frozenCode, ← eval_sumSquares_eq_zero_iff_satisfies]
    have h1 := eval_sumSquares_nonneg x R.eqs
    have h2 := sq_nonneg (x (Fin.castAdd R.aux 0) - e)
    constructor
    · intro h
      refine ⟨by linarith, ?_⟩
      have hsq : (x (Fin.castAdd R.aux 0) - e) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff two_ne_zero |>.mp hsq
      linarith
    · rintro ⟨hs, hx⟩
      rw [hs, hx]
      ring
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hsat, hx0⟩ := (heval x).mp hx
    refine ⟨fun j => x (Fin.natAdd 1 j), ?_⟩
    have happ : Fin.append (fun _ : Fin 1 => (e : ℤ)) (fun j => x (Fin.natAdd 1 j)) = x := by
      funext i
      induction i using Fin.addCases with
      | left j =>
          rw [Fin.append_left,
            show Fin.castAdd R.aux j = Fin.castAdd R.aux (0 : Fin 1) by
              rw [Subsingleton.elim j (0 : Fin 1)], hx0]
      | right j => rw [Fin.append_right]
    rw [happ]
    exact hsat
  · rintro ⟨y, hy⟩
    exact ⟨Fin.append (fun _ : Fin 1 => (e : ℤ)) y, (heval _).mpr ⟨hy, Fin.append_left _ _ _⟩⟩

/-- Reindexing the `r` affine variables of a degree-two system along an equality `r = r'`
(`Fin.cast`) reindexes the `N = r + 6` variables `D_i` of the ideal of Theorem 4.5 along
the same equality: the ideals `idealOfSystem L` and
`idealOfSystem (L.map (rename (Fin.cast h)))` correspond under the variable renaming
`Var (r + 6) ≃ Var (r' + 6)`. -/
theorem map_idealOfSystem_cast {r r' : ℕ} (h : r = r') (L : List (DegreeTwoEquation r)) :
    Ideal.map
        (MvPolynomial.renameEquiv ℚ
          (Equiv.cast (congrArg Var (congrArg (· + 6) h)))).toRingEquiv.toRingHom
        (idealOfSystem L)
      = idealOfSystem (L.map (DegreeTwoEquation.rename (Fin.cast h))) := by
  subst h
  have hid : DegreeTwoEquation.rename (id : Fin r → Fin r) = id := by
    funext F
    cases F
    simp [DegreeTwoEquation.rename]
  simp [hid]

/-! ### The construction of Theorem 4.5 applied to the family `U(e, Y)`, for any `R` -/

namespace Universal

variable (R : EffDiophRel 1)

/-- The number of auxiliary variables of the straight line program of `frozenCode R 0`;
by `k_eq` it is the number for every `frozenCode R e`. -/
def k₀ : ℕ := (StraightLineProgram.ofCode (frozenCode R 0)).k

/-- The number `N` of variables `D_i` of Corollary 5.1: the `1 + R.aux` variables
of `U(e, Y)`, the `k₀ R` auxiliary variables of its straight line program, and the six
variables `h, k, u₁, …, u₄` of the guards of Lemma 4.2.  It does not depend on `e`. -/
def N₀ : ℕ := 1 + R.aux + k₀ R + 6

/-- The straight line programs of all `frozenCode R e` have the same number of auxiliary
variables [proof of Corollary 5.1: "programs of the same shape"]. -/
theorem k_eq (e : ℕ) : (StraightLineProgram.ofCode (frozenCode R e)).k = k₀ R :=
  (StraightLineProgram.shape_ofCode (frozenCode_shape R e)).1

theorem numVars_frozenCode (e : ℕ) : numVars (frozenCode R e) = N₀ R := by
  rw [numVars, k_eq R e]
  rfl

theorem dim_eq (e : ℕ) :
    1 + R.aux + (StraightLineProgram.ofCode (frozenCode R e)).k = 1 + R.aux + k₀ R := by
  rw [k_eq R e]

/-- **Lemma 4.1 for `U(e, Y)`, in the fixed variables**: the degree-two system of
`frozenCode R e`, reindexed along `k_eq R e` to the fixed variable set
`Fin (1 + R.aux + k₀ R)` [proof of Corollary 5.1: "the same number `M` of
homogeneous quadratic forms in the same `N + 1` coordinates.  Only their coefficients depend
on `e`"]. -/
def system (e : ℕ) : List (DegreeTwoEquation (1 + R.aux + k₀ R)) :=
  (degreeTwoSystem (frozenCode R e)).map (DegreeTwoEquation.rename (Fin.cast (dim_eq R e)))

/-- The reindexing does not change solvability. -/
theorem system_solvable_iff' (e : ℕ) :
    (∃ z : Fin (1 + R.aux + k₀ R) → ℤ, Solves z (system R e))
      ↔ ∃ z : Fin (1 + R.aux + (StraightLineProgram.ofCode (frozenCode R e)).k) → ℤ,
          Solves z (degreeTwoSystem (frozenCode R e)) :=
  solves_map_rename_iff _ (Fin.cast (dim_eq R e).symm) (fun _ => Fin.ext rfl) _

/-- `system R e` has an integral solution iff the relation `R` holds at `e`. -/
theorem system_solvable_iff (e : ℕ) :
    (∃ z : Fin (1 + R.aux + k₀ R) → ℤ, Solves z (system R e)) ↔ R.Realizes (fun _ => (e : ℤ)) :=
  (system_solvable_iff' R e).trans
    ((degreeTwoSystem_solvable_iff _).trans (frozenCode_zero_iff R e))

/-- All systems `system R e` have the same number of equations
[proof of Corollary 5.1: "programs of the same shape"]. -/
theorem length_system (e : ℕ) : (system R e).length = (system R 0).length := by
  simp only [system, List.length_map, degreeTwoSystem, List.length_append,
    List.length_singleton, (StraightLineProgram.shape_ofCode (frozenCode_shape R e)).2]

/-- The number `M` of quadratic forms of Corollary 5.1: the equations of
`system R 0` and the two guards of Lemma 4.2. -/
def M₀ : ℕ := (guarded (system R 0)).length

/-- Lemmas 4.1 and 4.2 "produce the same number `M` of homogeneous quadratic
forms in the same `N + 1` coordinates" for every `e` [proof of
Corollary 5.1]. -/
theorem length_guarded_system (e : ℕ) : (guarded (system R e)).length = M₀ R := by
  simp only [M₀, guarded, List.length_append, List.length_map, length_system R e]

/-- The quadratic forms `Q₁, …, Q_M` of `I_e`: the homogenized guarded system. -/
def forms (e : ℕ) :
    Fin (guarded (system R e)).length → BilinearFormMatrix (Option (Fin (N₀ R))) :=
  homogenizedSystem (guarded (system R e))

/-- **The ideal `I_e` of Corollary 5.1** [§5], in the fixed ring
`ℚ[S, T, D₁, …, D_{N₀ R}]`: the ideal of Theorem 4.5 attached to the degree-two system
`system R e` (guards of Lemma 4.2, homogenization, contraction of
`J₀ ∩ ⋂ ker φ_{Qᵢ}`). -/
noncomputable def ideal (e : ℕ) : Ideal (MvPolynomial (Var (N₀ R)) ℚ) :=
  idealOfSystem (system R e)

theorem ideal_eq (e : ℕ) : ideal R e = polyReductionIdeal (forms R e) := rfl

/-- `I_e` is the ideal `I_{P_e}` of Theorem 4.5 for the syntax `P_e = frozenCode R e`
(`polyIdeal`), transported to the fixed ring along the identification
`numVars (frozenCode R e) = N₀ R` of its variables (`numVars_frozenCode`). -/
theorem ideal_eq_map_polyIdeal (e : ℕ) :
    Ideal.map
        (MvPolynomial.renameEquiv ℚ
          (Equiv.cast (congrArg Var (numVars_frozenCode R e)))).toRingEquiv.toRingHom
        (polyIdeal (frozenCode R e))
      = ideal R e :=
  map_idealOfSystem_cast (dim_eq R e) (degreeTwoSystem (frozenCode R e))

/-- `I_e` contains a trinomial iff the relation `R` holds at `e`. -/
theorem hasShortPoly_three_iff (e : ℕ) :
    HasShortPoly 3 (ideal R e) ↔ R.Realizes (fun _ => (e : ℤ)) :=
  (main_theorem_system (system R e)).2.1.trans (system_solvable_iff R e)

/-- **Corollary 5.1, the values of `t(I_e)`** [§5]: in the fixed ring
`ℚ[S, T, D₁, …, D_{N₀ R}]`, `t(I_e) = 3` if the relation `R` holds at `e` and `t(I_e) = 4`
otherwise. -/
theorem tinv_ideal (e : ℕ) [Decidable (R.Realizes (fun _ => (e : ℤ)))] :
    tinv (ideal R e) = if R.Realizes (fun _ => (e : ℤ)) then 3 else 4 :=
  let h := main_theorem_system (system R e)
  tinv_eq_ite h.1 (hasShortPoly_three_iff R e) h.2.2

/-- **Corollary 5.1: `I_e` is `𝔪`-primary** [§5]. -/
theorem ideal_isPrimary (e : ℕ) : (ideal R e).IsPrimary :=
  polyReductionIdeal_isPrimary _

/-- `√I_e = 𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_{N₀}−1⟩` [§5]. -/
theorem radical_ideal (e : ℕ) : (ideal R e).radical = pointIdeal (N₀ R) :=
  radical_polyReductionIdeal _

/-- **Corollary 5.1: `I_e` is zero-dimensional** [§5]. -/
theorem ringKrullDim_ideal (e : ℕ) :
    ringKrullDim (MvPolynomial (Var (N₀ R)) ℚ ⧸ ideal R e) = 0 :=
  ringKrullDim_quotient _

/-- **Corollary 5.1: `I_e` is proper** [§5]. -/
theorem ideal_ne_top (e : ℕ) : ideal R e ≠ ⊤ :=
  polyReductionIdeal_ne_top _

/-- **The computed presentation of `I_e`** [§5]: the generator list of Theorem
4.5 (`generators`, "linear algebra on the residues") for the quadratic forms of
`system R e`.  Each generator is a polynomial in `s = 2S−1`, `t = 2T−1`, `c_i = D_i − 1`
(`PointPoly`).  An executable function of `R` and `e`. -/
def generators (e : ℕ) : List (PointPoly (N₀ R)) :=
  Trinomial.generators (forms R e)

/-- `generators R e` generates `I_e`. -/
theorem span_generators (e : ℕ) :
    Ideal.span {g | ∃ l ∈ generators R e, g = l.toPoly} = ideal R e :=
  generatedIdeal_eq _

/-- Every generator of the presentation has total degree at most `5`
[Corollary 5.1]. -/
theorem generators_degree_le (e : ℕ) {l : PointPoly (N₀ R)} (hl : l ∈ generators R e) :
    l.toPoly.totalDegree ≤ 5 :=
  Trinomial.generators_totalDegree_le _ hl

/-- **Uniform size of the presentation**: at most `C(N₀+7, 5)` generators, a bound
independent of `e` [Corollary 5.1]. -/
theorem generators_length_le (e : ℕ) :
    (generators R e).length ≤ Nat.choose (N₀ R + 7) 5 :=
  Trinomial.generators_length_le _

/-- `ℚ[S, T, D₁, …, D_{N₀ R}] / I_e` is a finite-dimensional `ℚ`-vector space. -/
instance (e : ℕ) : Module.Finite ℚ (MvPolynomial (Var (N₀ R)) ℚ ⧸ ideal R e) :=
  inferInstanceAs
    (Module.Finite ℚ (MvPolynomial (Var (N₀ R)) ℚ ⧸ polyReductionIdeal (forms R e)))

/-- **Corollary 5.1, the colength bound** [§5:
"`dim_ℚ(ℚ[S, T, D₁, …, D_N] / I_e) ≤ C`" with `C := (N+5) + M(N+3)`]: in the fixed ring, the
colength of every `I_e` is at most `(N₀+5) + M₀(N₀+3)`, where `N₀` and `M₀` do not depend
on `e` (`length_guarded_system`). -/
theorem finrank_quotient_le (e : ℕ) :
    Module.finrank ℚ (MvPolynomial (Var (N₀ R)) ℚ ⧸ ideal R e)
      ≤ (N₀ R + 5) + M₀ R * (N₀ R + 3) :=
  (Trinomial.finrank_quotient_le (forms R e)).trans_eq (by rw [length_guarded_system R e])

/-- **Corollary 5.1, the colength bound in closed form**: the colength of every `I_e`
is at most `C(N₀+6, 4)` [Corollary 5.1]. -/
theorem finrank_quotient_le_choose (e : ℕ) :
    Module.finrank ℚ (MvPolynomial (Var (N₀ R)) ℚ ⧸ ideal R e) ≤ Nat.choose (N₀ R + 6) 4 :=
  Trinomial.finrank_quotient_le_choose (forms R e)

end Universal

/-! ### The halting instance: `R = haltingRel` -/

/-- **The syntax of the paper's `U(e, Y)`** [§5]: `frozenCode` at the fixed,
classically chosen relation `haltingRel` (the paper's universal polynomial `U`, which the
paper also does not exhibit).  This is the only non-executable input of the construction. -/
noncomputable def haltingCode (e : ℕ) : IntPolynomialCode (1 + haltingRel.aux) :=
  frozenCode haltingRel e

/-- `haltingCode e` has an integral zero iff machine `e` halts on input `0`
[§5, eq. (8)]. -/
theorem haltingCode_zero_iff (e : ℕ) :
    (∃ x : Fin (1 + haltingRel.aux) → ℤ, evalPolynomial (haltingCode e) x = 0)
      ↔ HaltsAtZero (Denumerable.ofNat Code e) :=
  (frozenCode_zero_iff haltingRel e).trans (haltingRel_spec e)

/-- The number `N` of variables `D_i` of Corollary 5.1. -/
noncomputable def N₀ : ℕ := Universal.N₀ haltingRel

/-- The number `M` of quadratic forms of Corollary 5.1. -/
noncomputable def M₀ : ℕ := Universal.M₀ haltingRel

/-- **The ideal `I_e` of Corollary 5.1** [§5], in the fixed ring
`ℚ[S, T, D₁, …, D_{N₀}]`. -/
noncomputable def haltingIdeal (e : ℕ) : Ideal (MvPolynomial (Var N₀) ℚ) :=
  Universal.ideal haltingRel e

/-- `I_e` contains a trinomial iff machine `e` halts on input `0`. -/
theorem haltingIdeal_hasShortPoly_three_iff (e : ℕ) :
    HasShortPoly 3 (haltingIdeal e) ↔ HaltsAtZero (Denumerable.ofNat Code e) :=
  (Universal.hasShortPoly_three_iff haltingRel e).trans (haltingRel_spec e)

open Classical in
/-- **Corollary 5.1, the values of `t(I_e)`** [§5]: in the fixed ring
`ℚ[S, T, D₁, …, D_{N₀}]`, `t(I_e) = 3` if machine `e` halts on input `0` and `t(I_e) = 4`
otherwise. -/
theorem haltingIdeal_tinv (e : ℕ) :
    tinv (haltingIdeal e) = if HaltsAtZero (Denumerable.ofNat Code e) then 3 else 4 :=
  let h := main_theorem_system (Universal.system haltingRel e)
  tinv_eq_ite h.1 (haltingIdeal_hasShortPoly_three_iff e) h.2.2

/-- **Corollary 5.1: `I_e` is `𝔪`-primary** [§5]. -/
theorem haltingIdeal_isPrimary (e : ℕ) : (haltingIdeal e).IsPrimary :=
  Universal.ideal_isPrimary haltingRel e

/-- `√I_e = 𝔪 = ⟨2S−1, 2T−1, D₁−1, …, D_{N₀}−1⟩` [§5]. -/
theorem radical_haltingIdeal (e : ℕ) : (haltingIdeal e).radical = pointIdeal N₀ :=
  Universal.radical_ideal haltingRel e

/-- **Corollary 5.1: `I_e` is zero-dimensional** [§5]. -/
theorem ringKrullDim_haltingIdeal (e : ℕ) :
    ringKrullDim (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) = 0 :=
  Universal.ringKrullDim_ideal haltingRel e

/-- **Corollary 5.1: `I_e` is proper** [§5]. -/
theorem haltingIdeal_ne_top (e : ℕ) : haltingIdeal e ≠ ⊤ :=
  Universal.ideal_ne_top haltingRel e

/-- **The computed presentation of `I_e`** [§5]: `Universal.generators` at
`haltingRel`; noncomputable only through that input. -/
noncomputable def haltingGenerators (e : ℕ) : List (PointPoly N₀) :=
  Universal.generators haltingRel e

/-- `haltingGenerators e` generates `I_e`. -/
theorem span_haltingGenerators (e : ℕ) :
    Ideal.span {g | ∃ l ∈ haltingGenerators e, g = l.toPoly} = haltingIdeal e :=
  Universal.span_generators haltingRel e

/-- Every generator of the presentation has total degree at most `5`. -/
theorem haltingGenerators_degree_le (e : ℕ) {l : PointPoly N₀}
    (hl : l ∈ haltingGenerators e) : l.toPoly.totalDegree ≤ 5 :=
  Universal.generators_degree_le haltingRel e hl

/-- **Corollary 5.1, the generator count**: at most `C(N₀+7, 5)` generators, a bound
independent of `e`. -/
theorem haltingGenerators_length_le_choose (e : ℕ) :
    (haltingGenerators e).length ≤ Nat.choose (N₀ + 7) 5 :=
  Universal.generators_length_le haltingRel e

instance (e : ℕ) : Module.Finite ℚ (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) :=
  inferInstanceAs (Module.Finite ℚ (MvPolynomial (Var (Universal.N₀ haltingRel)) ℚ
    ⧸ Universal.ideal haltingRel e))

/-- **Corollary 5.1, the colength bound** `≤ C = (N₀+5) + M₀(N₀+3)`. -/
theorem finrank_haltingIdeal_le (e : ℕ) :
    Module.finrank ℚ (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) ≤ (N₀ + 5) + M₀ * (N₀ + 3) :=
  Universal.finrank_quotient_le haltingRel e

/-- **Corollary 5.1, the colength bound in closed form** `≤ C(N₀+6, 4)`. -/
theorem finrank_haltingIdeal_le_choose (e : ℕ) :
    Module.finrank ℚ (MvPolynomial (Var N₀) ℚ ⧸ haltingIdeal e) ≤ Nat.choose (N₀ + 6) 4 :=
  Universal.finrank_quotient_le_choose haltingRel e

/-! ### Undecidability -/

/-- **The index predicate `e ↦ [t(I_e) = 3]` is undecidable**: no algorithm decides, given
`e`, whether `t(I_e) = 3`, because by `haltingIdeal_tinv` this predicate is extensionally
the halting problem, which mathlib proves undecidable (`ComputablePred.halting_problem`).
This is the consequence of Corollary 5.1 that the paper draws ("`e ↦ I_e` is a
computable many-one reduction from the halting set `K₀`"); the computability of the map
`e ↦ I_e` in mathlib's sense is not part of this statement. -/
theorem haltingIdeal_not_computable :
    ¬ ComputablePred (fun e : ℕ => tinv (haltingIdeal e) = 3) := by
  intro hcomp
  have hiff : ∀ e : ℕ, tinv (haltingIdeal e) = 3 ↔ HaltsAtZero (Denumerable.ofNat Code e) := by
    intro e
    rw [haltingIdeal_tinv]
    split_ifs with h
    · simp [h]
    · simp [h]
  have hhalt : ComputablePred (fun e : ℕ => HaltsAtZero (Denumerable.ofNat Code e)) :=
    ComputablePred.of_eq hcomp hiff
  obtain ⟨f, hf, hfp⟩ := ComputablePred.computable_iff.mp hhalt
  have hcode : ComputablePred (fun c : Code => (Code.eval c 0).Dom) := by
    refine ComputablePred.computable_iff.mpr
      ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, ?_⟩
    funext c
    have := congrFun hfp (Encodable.encode c)
    simpa [HaltsAtZero, Denumerable.ofNat_encode] using this
  exact ComputablePred.halting_problem 0 hcode

end Trinomial
