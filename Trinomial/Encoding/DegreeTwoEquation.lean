import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Equations of degree at most two, and their systems

[Lemmas 4.1 and 4.2].  The systems `f₁, …, f_m ∈ ℤ[x₁, …, x_r]`
of equations of degree at most two produced by Lemma 4.1 and consumed by Lemma
4.2 are represented syntactically:

* `DegreeTwoEquation r` — an affine-quadratic expression `Σ aₜ·xᵢxⱼ + Σ bₜ·xᵢ + c` in `r`
  variables, as formal lists of terms, with its value `eval` at an integer point.
  Renaming variables is `List.map` (`DegreeTwoEquation.rename`), so no matrix reindexing
  is ever needed.
* `eqConst`, `eqAdd`, `eqMul`, `eqZero` — the gates `x_o = a`, `x_o = x_i + x_j`,
  `x_o = x_i·x_j`, `x_o = 0` of a straight line program.
* `Solves z L` — `z` is a common integral zero of the system `L`; `solves_append`,
  `solves_map_rename`, `solves_map_rename_iff`.
* `incl₁`, `incl₂`, `outPos`, `combine` — the index plumbing used by
  `Trinomial/Encoding/StraightLineProgram.lean` to combine two programs.

The straight line program compiler itself (Lemma 4.1 as an algorithm) is
`StraightLineProgram.ofCode` in `Trinomial/Encoding/StraightLineProgram.lean`.
-/

set_option autoImplicit false

namespace Trinomial

/-- An affine-quadratic expression in `r` integer variables, as formal lists of
quadratic terms `a·xᵢxⱼ`, linear terms `b·xᵢ`, and a constant. -/
structure DegreeTwoEquation (r : ℕ) where
  /-- The quadratic terms, each `(a, i, j)` standing for `a·xᵢxⱼ`. -/
  quad : List (ℤ × Fin r × Fin r)
  /-- The linear terms, each `(b, i)` standing for `b·xᵢ`. -/
  lin : List (ℤ × Fin r)
  /-- The constant term. -/
  const : ℤ

namespace DegreeTwoEquation

variable {r r' : ℕ}

/-- The value of the expression at an integer point. -/
def eval (F : DegreeTwoEquation r) (z : Fin r → ℤ) : ℤ :=
  (F.quad.map fun t => t.1 * z t.2.1 * z t.2.2).sum
    + (F.lin.map fun t => t.1 * z t.2).sum + F.const

/-- Renaming of variables (any map of index sets; no injectivity needed). -/
def rename (f : Fin r → Fin r') (F : DegreeTwoEquation r) : DegreeTwoEquation r' :=
  ⟨F.quad.map fun t => (t.1, f t.2.1, f t.2.2), F.lin.map fun t => (t.1, f t.2), F.const⟩

theorem eval_rename (f : Fin r → Fin r') (F : DegreeTwoEquation r) (z : Fin r' → ℤ) :
    (F.rename f).eval z = F.eval (z ∘ f) := by
  simp only [eval, rename, List.map_map]
  rfl

/-- The gate `x_o = a`. -/
def eqConst (o : Fin r) (a : ℤ) : DegreeTwoEquation r := ⟨[], [(1, o)], -a⟩

/-- The gate `x_o = x_i + x_j`. -/
def eqAdd (o i j : Fin r) : DegreeTwoEquation r := ⟨[], [(1, o), (-1, i), (-1, j)], 0⟩

/-- The gate `x_o = x_i · x_j`. -/
def eqMul (o i j : Fin r) : DegreeTwoEquation r := ⟨[(-1, i, j)], [(1, o)], 0⟩

/-- The equation `x_o = 0`. -/
def eqZero (o : Fin r) : DegreeTwoEquation r := ⟨[], [(1, o)], 0⟩

@[simp] theorem eqConst_eval (o : Fin r) (a : ℤ) (z : Fin r → ℤ) :
    (eqConst o a).eval z = z o - a := by
  simp [eval, eqConst]
  ring

@[simp] theorem eqAdd_eval (o i j : Fin r) (z : Fin r → ℤ) :
    (eqAdd o i j).eval z = z o - z i - z j := by
  simp [eval, eqAdd]
  ring

@[simp] theorem eqMul_eval (o i j : Fin r) (z : Fin r → ℤ) :
    (eqMul o i j).eval z = z o - z i * z j := by
  simp [eval, eqMul]
  ring

@[simp] theorem eqZero_eval (o : Fin r) (z : Fin r → ℤ) :
    (eqZero o).eval z = z o := by
  simp [eval, eqZero]

end DegreeTwoEquation

/-- `z` solves every equation of the system `L`. -/
def Solves {r : ℕ} (z : Fin r → ℤ) (L : List (DegreeTwoEquation r)) : Prop :=
  ∀ F ∈ L, F.eval z = 0

theorem solves_append {r : ℕ} {z : Fin r → ℤ} {L₁ L₂ : List (DegreeTwoEquation r)} :
    Solves z (L₁ ++ L₂) ↔ Solves z L₁ ∧ Solves z L₂ :=
  List.forall_mem_append

theorem solves_map_rename {r r' : ℕ} (f : Fin r → Fin r') (L : List (DegreeTwoEquation r))
    (z : Fin r' → ℤ) (h : Solves z (L.map (DegreeTwoEquation.rename f))) : Solves (z ∘ f) L := by
  intro F hF
  have := h (F.rename f) (List.mem_map_of_mem hF)
  rwa [DegreeTwoEquation.eval_rename] at this

/-- Renaming the variables of a system along a map with a left inverse does not change
whether the system has an integral solution. -/
theorem solves_map_rename_iff {r r' : ℕ} (f : Fin r → Fin r') (g : Fin r' → Fin r)
    (hgf : ∀ i, g (f i) = i) (L : List (DegreeTwoEquation r)) :
    (∃ z : Fin r' → ℤ, Solves z (L.map (DegreeTwoEquation.rename f)))
      ↔ ∃ z : Fin r → ℤ, Solves z L := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z ∘ f, solves_map_rename f L z hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨z ∘ g, fun F hF => ?_⟩
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    rw [DegreeTwoEquation.eval_rename, show (z ∘ g) ∘ f = z from funext fun i =>
      congrArg z (hgf i)]
    exact hz G hG

/-! ### Index plumbing for combining straight-line programs

Variables are laid out as inputs first (`Fin n`, via `Fin.castAdd`), then auxiliary
blocks.  `incl₁`/`incl₂` embed the variable sets of two sub-programs into the combined
one (`k₁ + k₂ + 1` auxiliaries: block one, block two, output), and `combine` glues two
solutions and an output value. -/

section Plumbing

variable {n k₁ k₂ : ℕ}

/-- Inputs and the first auxiliary block stay in place. -/
def incl₁ (n k₁ k₂ : ℕ) : Fin (n + k₁) → Fin (n + (k₁ + k₂ + 1)) :=
  fun i => ⟨i, by have := i.isLt; omega⟩

/-- Inputs stay in place; the second auxiliary block is shifted past the first. -/
def incl₂ (n k₁ k₂ : ℕ) : Fin (n + k₂) → Fin (n + (k₁ + k₂ + 1)) :=
  fun i => if h : (i : ℕ) < n then ⟨i, by omega⟩
    else ⟨(i : ℕ) + k₁, by have := i.isLt; omega⟩

/-- The output position (the last variable). -/
def outPos (n k₁ k₂ : ℕ) : Fin (n + (k₁ + k₂ + 1)) := ⟨n + k₁ + k₂, by omega⟩

/-- Glue two assignments (agreeing on the inputs) and an output value. -/
def combine (z₁ : Fin (n + k₁) → ℤ) (z₂ : Fin (n + k₂) → ℤ) (v : ℤ) :
    Fin (n + (k₁ + k₂ + 1)) → ℤ :=
  fun idx =>
    if h1 : (idx : ℕ) < n + k₁ then z₁ ⟨idx, h1⟩
    else if h2 : (idx : ℕ) < n + k₁ + k₂ then z₂ ⟨(idx : ℕ) - k₁, by omega⟩
    else v

theorem incl₁_castAdd (i : Fin n) :
    incl₁ n k₁ k₂ (Fin.castAdd k₁ i) = Fin.castAdd (k₁ + k₂ + 1) i :=
  Fin.ext rfl

theorem incl₂_castAdd (i : Fin n) :
    incl₂ n k₁ k₂ (Fin.castAdd k₂ i) = Fin.castAdd (k₁ + k₂ + 1) i := by
  have hi : ((Fin.castAdd k₂ i : Fin (n + k₂)) : ℕ) < n := i.isLt
  simp only [incl₂, dif_pos hi]
  exact Fin.ext rfl

theorem combine_incl₁ (z₁ : Fin (n + k₁) → ℤ) (z₂ : Fin (n + k₂) → ℤ) (v : ℤ) :
    combine z₁ z₂ v ∘ incl₁ n k₁ k₂ = z₁ := by
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, combine, incl₁, dif_pos hi]

theorem combine_incl₂ (z₁ : Fin (n + k₁) → ℤ) (z₂ : Fin (n + k₂) → ℤ) (v : ℤ)
    (hagree : ∀ i : Fin n, z₁ (Fin.castAdd k₁ i) = z₂ (Fin.castAdd k₂ i)) :
    combine z₁ z₂ v ∘ incl₂ n k₁ k₂ = z₂ := by
  funext i
  by_cases hi : (i : ℕ) < n
  · simp only [Function.comp_apply, incl₂, dif_pos hi, combine,
      dif_pos (show (i : ℕ) < n + k₁ by omega)]
    calc z₁ ⟨(i : ℕ), by omega⟩ = z₁ (Fin.castAdd k₁ ⟨(i : ℕ), hi⟩) :=
          congrArg z₁ (Fin.ext rfl)
    _ = z₂ (Fin.castAdd k₂ ⟨(i : ℕ), hi⟩) := hagree _
    _ = z₂ i := congrArg z₂ (Fin.ext rfl)
  · have hi2 := i.isLt
    simp only [Function.comp_apply, incl₂, dif_neg hi, combine,
      dif_neg (show ¬ ((i : ℕ) + k₁ < n + k₁) by omega),
      dif_pos (show (i : ℕ) + k₁ < n + k₁ + k₂ by omega)]
    exact congrArg z₂ (Fin.ext (by simp))

theorem combine_outPos (z₁ : Fin (n + k₁) → ℤ) (z₂ : Fin (n + k₂) → ℤ) (v : ℤ) :
    combine z₁ z₂ v (outPos n k₁ k₂) = v := by
  simp only [combine, outPos, dif_neg (show ¬ (n + k₁ + k₂ < n + k₁) by omega),
    dif_neg (show ¬ (n + k₁ + k₂ < n + k₁ + k₂) by omega)]

end Plumbing

end Trinomial
