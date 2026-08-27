import Trinomial.Encoding.PolynomialSide
import TrinomialUndecidability.Computability.EffectiveDiophantine

/-!
# Lemma 4.1 as an algorithm, and the ideal `I_P` as a function of `P`

[§4, Lemma 4.1 and Theorem 4.5].  The paper encodes the evaluation of
`P(y₁, …, yₙ)` as a *straight line program*: a sequence of additions and
multiplications, each intermediate result stored in a new variable, followed by the
equation `x_r = 0`.  This module implements that encoding as an executable function on
the sparse syntax `IntPolynomialCode n` (a list of pairs (exponent vector, integer
coefficient), with semantics `evalPolynomial`), proves that the program computes `P`,
and uses it to attach to every `P` a *definite* ideal `I_P`.

* `StraightLineProgram n` — `k` auxiliary variables, a list of equations of degree at
  most two over the variables `Fin (n + k)` (inputs first), and an output variable.
* `StraightLineProgram.Computes Γ f` — the program `Γ` computes the function `f`: every
  input extends to a solution of the equations with output `f y`, and every solution's
  output is `f` of its input part.
* `ofCode p` — the straight line program of the polynomial `p`; `ofCode_computes`.
* `degreeTwoSystem p` — **Lemma 4.1**, the system of equations of degree at most
  two attached to `p`, with `degreeTwoSystem_solvable_iff`.
* `idealOfSystem L` — the ideal `I ⊆ ℚ[S, T, D]` attached to any system `L` of degree-two
  equations: homogenize the guarded system of Lemma 4.2, intersect `J₀` with the
  kernels of the maps `φ_Q` (Section 3), and contract to the polynomial ring.
  `main_theorem_system` is the universally quantified content of Theorem 4.5.
* `polyIdeal p = idealOfSystem (degreeTwoSystem p)` — the ideal `I_P`, a function of
  the syntax of `P`, with `main_theorem_code` and `tinv_polyIdeal`: no monomial or
  binomial, a trinomial iff `P` has an integral zero, always the quadrinomial `Ω`, and
  `t(I_P) ∈ {3, 4}` accordingly.

All constructions in this file are executable (`Trinomial/Examples.lean` runs the program
compiler on the paper's example `3y₁² + y₁y₂ + 1`); only the ideals themselves are
noncomputable objects.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntExponent IntPolynomialCode evalMonomial
  evalPolynomial)

/-! ### Straight line programs -/

/-- A straight line program with `n` input variables [§4]: `k` auxiliary
variables, a list of equations of degree at most two over the variables `Fin (n + k)`
(the inputs are the first `n` variables), and the variable holding the result. -/
structure StraightLineProgram (n : ℕ) where
  /-- The number of auxiliary variables. -/
  k : ℕ
  /-- The equations, one per step of the program. -/
  gates : List (DegreeTwoEquation (n + k))
  /-- The variable holding the result. -/
  out : Fin (n + k)

namespace StraightLineProgram

variable {n : ℕ}

/-- The program `Γ` computes `f`: every input `y` extends to a solution of the equations
whose output is `f y`, and every solution has output `f` of its input part
[§4: "an auxiliary variable `x_r` which is forced to equal `P(y)`"]. -/
def Computes (Γ : StraightLineProgram n) (f : (Fin n → ℤ) → ℤ) : Prop :=
  (∀ y : Fin n → ℤ, ∃ z : Fin (n + Γ.k) → ℤ,
      (∀ i : Fin n, z (Fin.castAdd Γ.k i) = y i) ∧ Solves z Γ.gates ∧ z Γ.out = f y) ∧
  (∀ z : Fin (n + Γ.k) → ℤ, Solves z Γ.gates → z Γ.out = f (fun i => z (Fin.castAdd Γ.k i)))

theorem Computes.congr {Γ : StraightLineProgram n} {f g : (Fin n → ℤ) → ℤ}
    (h : Γ.Computes f) (hfg : f = g) : Γ.Computes g :=
  hfg ▸ h

/-- The program with the single step `x_out = a`. -/
def const (a : ℤ) : StraightLineProgram n :=
  ⟨1, [.eqConst (Fin.last n) a], Fin.last n⟩

theorem const_computes (a : ℤ) : (const (n := n) a).Computes (fun _ => a) := by
  dsimp only [const, Computes]
  constructor
  · intro y
    refine ⟨fun idx => if h : (idx : ℕ) < n then y ⟨idx, h⟩ else a, ?_, ?_, ?_⟩
    · intro i
      simp only [Fin.val_castAdd, dif_pos i.isLt, Fin.eta]
    · intro F hF
      rw [List.mem_singleton] at hF
      subst hF
      rw [DegreeTwoEquation.eqConst_eval]
      simp [Fin.last]
    · simp [Fin.last]
  · intro z hz
    have h := hz _ (List.mem_singleton_self _)
    rw [DegreeTwoEquation.eqConst_eval] at h
    omega

/-- The equation `x_o = x_i`. -/
def eqCopy {r : ℕ} (o i : Fin r) : DegreeTwoEquation r := ⟨[], [(1, o), (-1, i)], 0⟩

@[simp] theorem eqCopy_eval {r : ℕ} (o i : Fin r) (z : Fin r → ℤ) :
    (eqCopy o i).eval z = z o - z i := by
  simp [DegreeTwoEquation.eval, eqCopy]
  ring

/-- The program with the single step `x_out = y_i`. -/
def var (i : Fin n) : StraightLineProgram n :=
  ⟨1, [eqCopy (Fin.last n) (Fin.castAdd 1 i)], Fin.last n⟩

theorem var_computes (i : Fin n) : (var i).Computes (fun y => y i) := by
  dsimp only [var, Computes]
  constructor
  · intro y
    refine ⟨fun idx => if h : (idx : ℕ) < n then y ⟨idx, h⟩ else y i, ?_, ?_, ?_⟩
    · intro j
      simp only [Fin.val_castAdd, dif_pos j.isLt, Fin.eta]
    · intro F hF
      rw [List.mem_singleton] at hF
      subst hF
      rw [eqCopy_eval]
      simp [i.isLt]
    · simp [Fin.last]
  · intro z hz
    have h := hz _ (List.mem_singleton_self _)
    rw [eqCopy_eval, sub_eq_zero] at h
    exact h

/-- A binary step: the two programs are placed in disjoint blocks of auxiliary variables
(via `incl₁`, `incl₂` of `Trinomial.Quadratization`) and one new equation
`G out (out₁) (out₂)` defines the result. -/
def binary (G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r)
    (Γ₁ Γ₂ : StraightLineProgram n) : StraightLineProgram n :=
  ⟨Γ₁.k + Γ₂.k + 1,
    Γ₁.gates.map (DegreeTwoEquation.rename (incl₁ n Γ₁.k Γ₂.k))
      ++ Γ₂.gates.map (DegreeTwoEquation.rename (incl₂ n Γ₁.k Γ₂.k))
      ++ [G (outPos n Γ₁.k Γ₂.k) (incl₁ n Γ₁.k Γ₂.k Γ₁.out) (incl₂ n Γ₁.k Γ₂.k Γ₂.out)],
    outPos n Γ₁.k Γ₂.k⟩

theorem binary_computes {G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r}
    {g : ℤ → ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o i j : Fin r) (z : Fin r → ℤ), (G o i j).eval z = z o - g (z i) (z j))
    {Γ₁ Γ₂ : StraightLineProgram n} {f₁ f₂ : (Fin n → ℤ) → ℤ}
    (h₁ : Γ₁.Computes f₁) (h₂ : Γ₂.Computes f₂) :
    (binary G Γ₁ Γ₂).Computes (fun y => g (f₁ y) (f₂ y)) := by
  obtain ⟨T₁, S₁⟩ := h₁
  obtain ⟨T₂, S₂⟩ := h₂
  dsimp only [binary, Computes]
  constructor
  · intro y
    obtain ⟨z₁, hz₁ext, hz₁sol, hz₁out⟩ := T₁ y
    obtain ⟨z₂, hz₂ext, hz₂sol, hz₂out⟩ := T₂ y
    have hagree : ∀ i : Fin n, z₁ (Fin.castAdd Γ₁.k i) = z₂ (Fin.castAdd Γ₂.k i) :=
      fun i => by rw [hz₁ext, hz₂ext]
    have hI₁ := combine_incl₁ z₁ z₂ (g (f₁ y) (f₂ y))
    have hI₂ := combine_incl₂ z₁ z₂ (g (f₁ y) (f₂ y)) hagree
    refine ⟨combine z₁ z₂ (g (f₁ y) (f₂ y)), ?_, ?_, ?_⟩
    · intro i
      have h := congrFun hI₁ (Fin.castAdd Γ₁.k i)
      rw [Function.comp_apply, incl₁_castAdd] at h
      rw [h, hz₁ext]
    · intro F hF
      rcases List.mem_append.mp hF with hF' | hgate
      · rcases List.mem_append.mp hF' with h1 | h2
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h1
          rw [DegreeTwoEquation.eval_rename, hI₁]
          exact hz₁sol E hE
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h2
          rw [DegreeTwoEquation.eval_rename, hI₂]
          exact hz₂sol E hE
      · rw [List.mem_singleton] at hgate
        subst hgate
        rw [hG, combine_outPos]
        have e1 := congrFun hI₁ Γ₁.out
        have e2 := congrFun hI₂ Γ₂.out
        rw [Function.comp_apply] at e1 e2
        rw [e1, e2, hz₁out, hz₂out, sub_self]
    · exact combine_outPos _ _ _
  · intro z hz
    rw [solves_append, solves_append] at hz
    obtain ⟨⟨hA, hB⟩, hg⟩ := hz
    have h₁ := S₁ (z ∘ incl₁ n Γ₁.k Γ₂.k) (solves_map_rename _ _ _ hA)
    have h₂ := S₂ (z ∘ incl₂ n Γ₁.k Γ₂.k) (solves_map_rename _ _ _ hB)
    have r₁ : (fun i => (z ∘ incl₁ n Γ₁.k Γ₂.k) (Fin.castAdd Γ₁.k i))
        = fun i => z (Fin.castAdd (Γ₁.k + Γ₂.k + 1) i) := by
      funext i
      simp only [Function.comp_apply, incl₁_castAdd]
    have r₂ : (fun i => (z ∘ incl₂ n Γ₁.k Γ₂.k) (Fin.castAdd Γ₂.k i))
        = fun i => z (Fin.castAdd (Γ₁.k + Γ₂.k + 1) i) := by
      funext i
      simp only [Function.comp_apply, incl₂_castAdd]
    rw [r₁] at h₁
    rw [r₂] at h₂
    have hgate := hg _ (List.mem_singleton_self _)
    rw [hG, sub_eq_zero] at hgate
    rw [hgate, ← h₁, ← h₂]
    rfl

/-- The step `x_out = x_{out₁} + x_{out₂}`. -/
def add (Γ₁ Γ₂ : StraightLineProgram n) : StraightLineProgram n :=
  binary DegreeTwoEquation.eqAdd Γ₁ Γ₂

/-- The step `x_out = x_{out₁} · x_{out₂}`. -/
def mul (Γ₁ Γ₂ : StraightLineProgram n) : StraightLineProgram n :=
  binary DegreeTwoEquation.eqMul Γ₁ Γ₂

theorem add_computes {Γ₁ Γ₂ : StraightLineProgram n} {f₁ f₂ : (Fin n → ℤ) → ℤ}
    (h₁ : Γ₁.Computes f₁) (h₂ : Γ₂.Computes f₂) :
    (add Γ₁ Γ₂).Computes (fun y => f₁ y + f₂ y) :=
  binary_computes (fun o i j z => by rw [DegreeTwoEquation.eqAdd_eval]; ring) h₁ h₂

theorem mul_computes {Γ₁ Γ₂ : StraightLineProgram n} {f₁ f₂ : (Fin n → ℤ) → ℤ}
    (h₁ : Γ₁.Computes f₁) (h₂ : Γ₂.Computes f₂) :
    (mul Γ₁ Γ₂).Computes (fun y => f₁ y * f₂ y) :=
  binary_computes (fun o i j z => DegreeTwoEquation.eqMul_eval o i j z) h₁ h₂

/-- A unary step: the program `Γ` keeps its block of auxiliary variables and one new
equation `G out (out_Γ)` defines the result. -/
def unary (G : ∀ {r : ℕ}, Fin r → Fin r → DegreeTwoEquation r) (Γ : StraightLineProgram n) :
    StraightLineProgram n :=
  ⟨Γ.k + 0 + 1,
    Γ.gates.map (DegreeTwoEquation.rename (incl₁ n Γ.k 0))
      ++ [G (outPos n Γ.k 0) (incl₁ n Γ.k 0 Γ.out)],
    outPos n Γ.k 0⟩

/-- A unary step using an input variable: one new equation `G out (out_Γ) (y_i)`. -/
def unaryInput (G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r)
    (Γ : StraightLineProgram n) (i : Fin n) : StraightLineProgram n :=
  ⟨Γ.k + 0 + 1,
    Γ.gates.map (DegreeTwoEquation.rename (incl₁ n Γ.k 0))
      ++ [G (outPos n Γ.k 0) (incl₁ n Γ.k 0 Γ.out) (Fin.castAdd (Γ.k + 0 + 1) i)],
    outPos n Γ.k 0⟩

theorem unary_computes {G : ∀ {r : ℕ}, Fin r → Fin r → DegreeTwoEquation r} {g : ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o a : Fin r) (z : Fin r → ℤ), (G o a).eval z = z o - g (z a))
    {Γ : StraightLineProgram n} {f : (Fin n → ℤ) → ℤ} (h : Γ.Computes f) :
    (unary G Γ).Computes (fun y => g (f y)) := by
  obtain ⟨T, S⟩ := h
  dsimp only [unary, Computes]
  constructor
  · intro y
    obtain ⟨z₁, hz₁ext, hz₁sol, hz₁out⟩ := T y
    have hI₁ := combine_incl₁ z₁ (fun j : Fin (n + 0) => y ⟨j, j.isLt⟩) (g (f y))
    refine ⟨combine z₁ (fun j : Fin (n + 0) => y ⟨j, j.isLt⟩) (g (f y)), ?_, ?_, ?_⟩
    · intro j
      have h := congrFun hI₁ (Fin.castAdd Γ.k j)
      rw [Function.comp_apply, incl₁_castAdd] at h
      rw [h, hz₁ext]
    · intro F hF
      rcases List.mem_append.mp hF with h1 | hgate
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h1
        rw [DegreeTwoEquation.eval_rename, hI₁]
        exact hz₁sol E hE
      · rw [List.mem_singleton] at hgate
        subst hgate
        rw [hG, combine_outPos]
        have e1 := congrFun hI₁ Γ.out
        rw [Function.comp_apply] at e1
        rw [e1, hz₁out, sub_self]
    · exact combine_outPos _ _ _
  · intro z hz
    rw [solves_append] at hz
    obtain ⟨hA, hg⟩ := hz
    have h₁ := S (z ∘ incl₁ n Γ.k 0) (solves_map_rename _ _ _ hA)
    have r₁ : (fun j => (z ∘ incl₁ n Γ.k 0) (Fin.castAdd Γ.k j))
        = fun j => z (Fin.castAdd (Γ.k + 0 + 1) j) := by
      funext j
      simp only [Function.comp_apply, incl₁_castAdd]
    rw [r₁] at h₁
    have hgate := hg _ (List.mem_singleton_self _)
    rw [hG, sub_eq_zero] at hgate
    rw [hgate, ← h₁]
    rfl

theorem unaryInput_computes {G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r}
    {g : ℤ → ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o a b : Fin r) (z : Fin r → ℤ), (G o a b).eval z = z o - g (z a) (z b))
    {Γ : StraightLineProgram n} {f : (Fin n → ℤ) → ℤ} (h : Γ.Computes f) (i : Fin n) :
    (unaryInput G Γ i).Computes (fun y => g (f y) (y i)) := by
  obtain ⟨T, S⟩ := h
  dsimp only [unaryInput, Computes]
  constructor
  · intro y
    obtain ⟨z₁, hz₁ext, hz₁sol, hz₁out⟩ := T y
    have hI₁ := combine_incl₁ z₁ (fun j : Fin (n + 0) => y ⟨j, j.isLt⟩) (g (f y) (y i))
    refine ⟨combine z₁ (fun j : Fin (n + 0) => y ⟨j, j.isLt⟩) (g (f y) (y i)), ?_, ?_, ?_⟩
    · intro j
      have h := congrFun hI₁ (Fin.castAdd Γ.k j)
      rw [Function.comp_apply, incl₁_castAdd] at h
      rw [h, hz₁ext]
    · intro F hF
      rcases List.mem_append.mp hF with h1 | hgate
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h1
        rw [DegreeTwoEquation.eval_rename, hI₁]
        exact hz₁sol E hE
      · rw [List.mem_singleton] at hgate
        subst hgate
        rw [hG, combine_outPos]
        have e1 := congrFun hI₁ Γ.out
        rw [Function.comp_apply] at e1
        have e2 : combine z₁ (fun j : Fin (n + 0) => y ⟨j, j.isLt⟩) (g (f y) (y i))
            (Fin.castAdd (Γ.k + 0 + 1) i) = z₁ (Fin.castAdd Γ.k i) := by
          have h := congrFun hI₁ (Fin.castAdd Γ.k i)
          rw [Function.comp_apply, incl₁_castAdd] at h
          exact h
        rw [e1, e2, hz₁out, hz₁ext, sub_self]
    · exact combine_outPos _ _ _
  · intro z hz
    rw [solves_append] at hz
    obtain ⟨hA, hg⟩ := hz
    have h₁ := S (z ∘ incl₁ n Γ.k 0) (solves_map_rename _ _ _ hA)
    have r₁ : (fun j => (z ∘ incl₁ n Γ.k 0) (Fin.castAdd Γ.k j))
        = fun j => z (Fin.castAdd (Γ.k + 0 + 1) j) := by
      funext j
      simp only [Function.comp_apply, incl₁_castAdd]
    rw [r₁] at h₁
    have hgate := hg _ (List.mem_singleton_self _)
    rw [hG, sub_eq_zero] at hgate
    rw [hgate, ← h₁]
    rfl

/-- The equation `x_o = c · x_i` (degree one). -/
def eqScale {r : ℕ} (o : Fin r) (c : ℤ) (i : Fin r) : DegreeTwoEquation r :=
  ⟨[], [(1, o), (-c, i)], 0⟩

@[simp] theorem eqScale_eval {r : ℕ} (o : Fin r) (c : ℤ) (i : Fin r) (z : Fin r → ℤ) :
    (eqScale o c i).eval z = z o - c * z i := by
  simp [DegreeTwoEquation.eval, eqScale]
  ring

/-- The step `x_out = x_Γ · y_i`  [§4: "`x₃ = y₁ · y₂`"]. -/
def mulVar (Γ : StraightLineProgram n) (i : Fin n) : StraightLineProgram n :=
  unaryInput DegreeTwoEquation.eqMul Γ i

/-- The step `x_out = c · x_Γ`  [§4: "`x₂ = 3 · x₁`"]. -/
def scale (c : ℤ) (Γ : StraightLineProgram n) : StraightLineProgram n :=
  unary (fun o a => eqScale o c a) Γ

theorem mulVar_computes {Γ : StraightLineProgram n} {f : (Fin n → ℤ) → ℤ}
    (h : Γ.Computes f) (i : Fin n) : (mulVar Γ i).Computes (fun y => f y * y i) :=
  unaryInput_computes (fun o a b z => DegreeTwoEquation.eqMul_eval o a b z) h i

theorem scale_computes (c : ℤ) {Γ : StraightLineProgram n} {f : (Fin n → ℤ) → ℤ}
    (h : Γ.Computes f) : (scale c Γ).Computes (fun y => c * f y) :=
  unary_computes (fun o a z => eqScale_eval o c a z) h

/-- `y_i ^ m` by repeated multiplication with the input `y_i` (`m` steps for `m ≥ 1`). -/
def pow (i : Fin n) : ℕ → StraightLineProgram n
  | 0 => const 1
  | 1 => var i
  | m + 2 => mulVar (pow i (m + 1)) i

theorem pow_computes (i : Fin n) : ∀ m : ℕ, (pow i m).Computes (fun y => y i ^ m)
  | 0 => (const_computes 1).congr (funext fun y => by simp)
  | 1 => (var_computes i).congr (funext fun y => by simp)
  | m + 2 => (mulVar_computes (pow_computes i (m + 1)) i).congr (funext fun y => by ring)

theorem iterate_mulVar_computes {Γ : StraightLineProgram n} {f : (Fin n → ℤ) → ℤ}
    (h : Γ.Computes f) (i : Fin n) (m : ℕ) :
    ((fun Δ => mulVar Δ i)^[m] Γ).Computes (fun y => f y * y i ^ m) := by
  induction m with
  | zero => exact h.congr (funext fun y => by simp)
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (mulVar_computes ih i).congr (funext fun y => by rw [pow_succ, mul_assoc])

/-- The product `∏_{i ∈ l} y_i^{e_i}`, or `none` when all exponents in `l` vanish (the empty
product needs no step). -/
def monomialAux (e : IntExponent n) : List (Fin n) → Option (StraightLineProgram n)
  | [] => none
  | i :: l =>
    match monomialAux e l with
    | none => if e i = 0 then none else some (pow i (e i))
    | some Γ => some ((fun Δ => mulVar Δ i)^[e i] Γ)

theorem monomialAux_spec (e : IntExponent n) :
    ∀ l : List (Fin n),
      (monomialAux e l = none → ∀ i ∈ l, e i = 0) ∧
      (∀ Γ, monomialAux e l = some Γ → Γ.Computes (fun y => (l.map fun i => y i ^ e i).prod))
  | [] => ⟨fun _ i hi => absurd hi (List.not_mem_nil), fun Γ h => by simp [monomialAux] at h⟩
  | i :: l => by
      obtain ⟨hnone, hsome⟩ := monomialAux_spec e l
      refine ⟨fun h j hj => ?_, fun Γ h => ?_⟩
      · simp only [monomialAux] at h
        split at h
        · rename_i hl
          split at h
          · rename_i hi
            rcases List.mem_cons.mp hj with rfl | hj'
            · exact hi
            · exact hnone hl j hj'
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · simp only [monomialAux] at h
        split at h
        · rename_i hl
          split at h
          · exact absurd h (by simp)
          · rename_i hi
            obtain rfl := Option.some.inj h
            refine (pow_computes i (e i)).congr (funext fun y => ?_)
            have hprod : (l.map fun j => y j ^ e j).prod = 1 :=
              List.prod_eq_one fun x hx => by
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
                rw [hnone hl j hj, pow_zero]
            simp [hprod]
        · rename_i Δ hl
          obtain rfl := Option.some.inj h
          refine (iterate_mulVar_computes (hsome Δ hl) i (e i)).congr (funext fun y => ?_)
          simp [mul_comm]

/-- The program computing the monomial `y^e` (no step at all for the empty monomial, which is
represented by `const 1`). -/
def monomial (e : IntExponent n) : StraightLineProgram n :=
  (monomialAux e (List.finRange n)).getD (const 1)

theorem monomial_computes (e : IntExponent n) : (monomial e).Computes (evalMonomial e) := by
  obtain ⟨hnone, hsome⟩ := monomialAux_spec e (List.finRange n)
  have hev : evalMonomial e = fun y => ((List.finRange n).map fun i => y i ^ e i).prod :=
    funext fun y => by simp only [evalMonomial, Fin.prod_univ_def]
  rw [hev]
  unfold monomial
  cases h : monomialAux e (List.finRange n) with
  | none =>
      refine (const_computes 1).congr (funext fun y => ?_)
      symm
      exact List.prod_eq_one fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        rw [hnone h j hj, pow_zero]
  | some Γ => exact hsome Γ h

/-- The straight line program of a polynomial given by its sparse syntax: for each term
`c·y^e` the monomial program followed by the scaling step `x = c · x'`, accumulated by
additions  [§4, the example `x₁ = y₁·y₁, x₂ = 3·x₁, …`].  The scaling step is
always present, so the shape of the program depends on the exponents only. -/
def ofCode : IntPolynomialCode n → StraightLineProgram n
  | [] => const 0
  | [(e, c)] => scale c (monomial e)
  | (e, c) :: t :: p => add (scale c (monomial e)) (ofCode (t :: p))

/-- The program `ofCode p` computes the polynomial `p`. -/
theorem ofCode_computes : ∀ p : IntPolynomialCode n, (ofCode p).Computes (evalPolynomial p)
  | [] => (const_computes 0).congr (funext fun y => rfl)
  | [(e, c)] => (scale_computes c (monomial_computes e)).congr
      (funext fun y => by simp [evalPolynomial])
  | (e, c) :: t :: p =>
      (add_computes (scale_computes c (monomial_computes e)) (ofCode_computes (t :: p))).congr
        (funext fun y => rfl)

/-! ### The shape of the program depends only on the exponents

Only the constants `c` in the scaling steps depend on the coefficients of `p`; the number
of auxiliary variables and the number of equations are determined by the exponent vectors
alone.  This is what makes the universal family of Corollary 5.1 live in one
fixed polynomial ring [proof of Corollary 5.1: "Substituting the constant
`e` … without simplifying, gives programs of the same shape for every `e`"]. -/

theorem k_binary (G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r)
    (Γ₁ Γ₂ : StraightLineProgram n) : (binary G Γ₁ Γ₂).k = Γ₁.k + Γ₂.k + 1 := rfl

theorem length_gates_binary (G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r)
    (Γ₁ Γ₂ : StraightLineProgram n) :
    (binary G Γ₁ Γ₂).gates.length = Γ₁.gates.length + Γ₂.gates.length + 1 := by
  simp only [binary, List.length_append, List.length_map, List.length_singleton]

theorem k_scale (c : ℤ) (Γ : StraightLineProgram n) : (scale c Γ).k = Γ.k + 0 + 1 := rfl

theorem length_gates_scale (c : ℤ) (Γ : StraightLineProgram n) :
    (scale c Γ).gates.length = Γ.gates.length + 1 := by
  simp only [scale, unary, List.length_append, List.length_map, List.length_singleton]

/-- Two polynomials with the same list of exponent vectors have programs of the same
shape: the same number of auxiliary variables and the same number of equations. -/
theorem shape_ofCode : ∀ {p q : IntPolynomialCode n}, p.map Prod.fst = q.map Prod.fst →
    (ofCode p).k = (ofCode q).k ∧ (ofCode p).gates.length = (ofCode q).gates.length
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [(e, c)], [(e', c')], h => by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      subst h
      refine ⟨rfl, ?_⟩
      show (scale c (monomial e)).gates.length = (scale c' (monomial e)).gates.length
      rw [length_gates_scale, length_gates_scale]
  | [(e, c)], (e', c') :: u :: q, h => by simp at h
  | (e, c) :: t :: p, [(e', c')], h => by simp at h
  | (e, c) :: t :: p, (e', c') :: u :: q, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨hk, hl⟩ := shape_ofCode (p := t :: p) (q := u :: q) (by simpa using h')
      refine ⟨?_, ?_⟩
      · show (binary _ (scale c (monomial e)) (ofCode (t :: p))).k
          = (binary _ (scale c' (monomial e)) (ofCode (u :: q))).k
        rw [k_binary, k_binary, hk]
        rfl
      · show (binary _ (scale c (monomial e)) (ofCode (t :: p))).gates.length
          = (binary _ (scale c' (monomial e)) (ofCode (u :: q))).gates.length
        rw [length_gates_binary, length_gates_binary, hl, length_gates_scale,
          length_gates_scale]

end StraightLineProgram

/-! ### Lemma 4.1 -/

open StraightLineProgram in
/-- **Lemma 4.1**, as an algorithm: the system of equations of degree at most two
attached to `p`, namely the steps of its straight line program and the equation
`x_out = 0`  [Lemma 4.1]. -/
def degreeTwoSystem {n : ℕ} (p : IntPolynomialCode n) :
    List (DegreeTwoEquation (n + (ofCode p).k)) :=
  (ofCode p).gates ++ [.eqZero (ofCode p).out]

/-- The system `degreeTwoSystem p` has an integral solution iff `p` has an integral zero
[Lemma 4.1]. -/
theorem degreeTwoSystem_solvable_iff {n : ℕ} (p : IntPolynomialCode n) :
    (∃ z : Fin (n + (StraightLineProgram.ofCode p).k) → ℤ, Solves z (degreeTwoSystem p))
      ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0 := by
  obtain ⟨T, S⟩ := StraightLineProgram.ofCode_computes p
  constructor
  · rintro ⟨z, hz⟩
    unfold degreeTwoSystem at hz
    rw [solves_append] at hz
    obtain ⟨hL, hzero⟩ := hz
    refine ⟨fun i => z (Fin.castAdd _ i), ?_⟩
    rw [← S z hL]
    have := hzero _ (List.mem_singleton_self _)
    rwa [DegreeTwoEquation.eqZero_eval] at this
  · rintro ⟨y, hy⟩
    obtain ⟨z, -, hsol, hout⟩ := T y
    refine ⟨z, ?_⟩
    unfold degreeTwoSystem
    rw [solves_append]
    refine ⟨hsol, ?_⟩
    intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    rw [DegreeTwoEquation.eqZero_eval, hout, hy]

/-! ### The ideal attached to a system, and to a polynomial -/

/-- The ideal `I ⊆ ℚ[S, T, D₁, …, D_{r+6}]` attached to a system `L` of degree-two
equations in `r` variables: adjoin the two guards of Lemma 4.2, homogenize, and
contract `J₀ ∩ ⋂ ker φ_{Q_i}` to the polynomial ring  [proof of Theorem 4.5]. -/
noncomputable def idealOfSystem {r : ℕ} (L : List (DegreeTwoEquation r)) :
    Ideal (MvPolynomial (Var (r + 6)) ℚ) :=
  polyReductionIdeal (homogenizedSystem (guarded L))

/-- **Theorem 4.5**, for every system of degree-two equations: the ideal
`idealOfSystem L` contains no monomial and no binomial, a trinomial iff `L` has an
integral solution, and always a quadrinomial. -/
theorem main_theorem_system {r : ℕ} (L : List (DegreeTwoEquation r)) :
    ¬ HasShortPoly 2 (idealOfSystem L)
    ∧ (HasShortPoly 3 (idealOfSystem L) ↔ ∃ z : Fin r → ℤ, Solves z L)
    ∧ HasShortPoly 4 (idealOfSystem L) := by
  have guard := noIntegralSolutionAtInfinity_homogenizedSystem L
  refine ⟨fun h => not_hasShort_two _ (hasShort_of_hasShortPoly h), ?_, hasShortPoly_four _⟩
  rw [← guarded_solvable_iff, ← homogenizedSystem_affine_iff]
  constructor
  · intro h
    exact (hasShort_three_iff guard).mp (hasShort_of_hasShortPoly h)
  · rintro ⟨d, hd⟩
    exact hasShortPoly_three_of_tau ((tau_mem_reductionIdeal_iff _ d).mpr hd)

/-- The ideal `I_P` of Theorem 4.5, as a function of the syntax `p` of `P`
[Theorem 4.5]. -/
noncomputable def polyIdeal {n : ℕ} (p : IntPolynomialCode n) :
    Ideal (MvPolynomial (Var (n + (StraightLineProgram.ofCode p).k + 6)) ℚ) :=
  idealOfSystem (degreeTwoSystem p)

/-- **Theorem 4.5** (short-support part), for the definite ideal `I_P = polyIdeal p`:
no monomial and no binomial, a trinomial iff `P` has an integral zero, always the
quadrinomial `Ω`  [Theorem 4.5]. -/
theorem main_theorem_code {n : ℕ} (p : IntPolynomialCode n) :
    ¬ HasShortPoly 2 (polyIdeal p)
    ∧ (HasShortPoly 3 (polyIdeal p) ↔ ∃ y : Fin n → ℤ, evalPolynomial p y = 0)
    ∧ HasShortPoly 4 (polyIdeal p) :=
  let h := main_theorem_system (degreeTwoSystem p)
  ⟨h.1, h.2.1.trans (degreeTwoSystem_solvable_iff p), h.2.2⟩

open Classical in
/-- The exact gap for the definite ideal [the displayed formula of the
introduction]: `t(I_P) = 3` if `P` has an integral zero and `t(I_P) = 4` otherwise. -/
theorem tinv_polyIdeal {n : ℕ} (p : IntPolynomialCode n) :
    tinv (polyIdeal p) = if ∃ y : Fin n → ℤ, evalPolynomial p y = 0 then 3 else 4 :=
  let h := main_theorem_code p
  tinv_eq_ite h.1 h.2.1 h.2.2

/-! ### Sparse syntax as a multivariate polynomial -/

/-- The multivariate polynomial denoted by sparse syntax. -/
noncomputable def codeToMv {n : ℕ} (p : IntPolynomialCode n) : MvPolynomial (Fin n) ℤ :=
  (p.map fun t ↦ MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm t.1) t.2).sum

theorem eval_codeToMv {n : ℕ} (p : IntPolynomialCode n) (x : Fin n → ℤ) :
    MvPolynomial.eval x (codeToMv p) = evalPolynomial p x := by
  induction p with
  | nil => simp [codeToMv, evalPolynomial]
  | cons t p ih =>
      have hprod : (Finsupp.equivFunOnFinite.symm t.1).prod (fun n e ↦ x n ^ e)
          = evalMonomial t.1 x := by
        rw [Finsupp.prod_fintype _ _ fun i ↦ pow_zero (x i),
          show evalMonomial t.1 x = ∏ i, x i ^ t.1 i from rfl]
        exact Finset.prod_congr rfl fun i _ ↦
          congrArg (x i ^ ·) (congrFun (Finsupp.equivFunOnFinite.apply_symm_apply t.1) i)
      rw [codeToMv, List.map_cons, List.sum_cons, map_add, ← codeToMv, ih,
        MvPolynomial.eval_monomial, hprod]
      rfl

/-- `main_theorem_code` with the integral zero stated for the polynomial `codeToMv p`. -/
theorem main_theorem_code_mv {n : ℕ} (p : IntPolynomialCode n) :
    ¬ HasShortPoly 2 (polyIdeal p)
    ∧ (HasShortPoly 3 (polyIdeal p) ↔ ∃ y : Fin n → ℤ, MvPolynomial.eval y (codeToMv p) = 0)
    ∧ HasShortPoly 4 (polyIdeal p) := by
  have h := main_theorem_code p
  refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
  simp only [eval_codeToMv]

end Trinomial
