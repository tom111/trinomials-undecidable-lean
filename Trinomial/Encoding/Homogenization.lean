import Trinomial.Encoding.DegreeTwoEquation
import Trinomial.Quadrics.KernelEvaluation

/-!
# Homogenization: from degree-two equations to matrices `(b_ij)` of the bilinear forms

[Lemma 4.2 and proof of Theorem 4.5].  A degree-≤2 equation `F` in `r`
integer variables homogenizes to the quadratic form `g(x,t) = t²·F(x/t)` on
`ℚ^r × ℚ v₀`.  This module builds the symmetric matrix `(b_ij)` of the bilinear form of `g` on the index type
`Option (Fin r)` (`some i ↦ xᵢ`, `none ↦ t`) and proves the two evaluation bridges:

* `quadAt_homogenize_one` — `g(x, 1) = F(x)` (the affine chart), over `ℚ` via `ratCast`;
* `quadAt_homogenize_zero` — `g(e, 0)` is the quadratic part of `F` at `e` (the hyperplane at
  infinity).

The matrix `(b_ij)` of the bilinear form is assembled as a list-sum of elementary symmetric matrices `symG`, so
all evaluation lemmas reduce to one computation for `symG` plus additivity.
-/

set_option autoImplicit false

namespace Trinomial

open scoped BigOperators

variable {r : ℕ}

/-- The quadratic-form value of a raw coefficient matrix `g` at `v`. -/
def quadFun (g : Option (Fin r) → Option (Fin r) → ℚ) (v : Option (Fin r) → ℚ) : ℚ :=
  ∑ o, ∑ o', v o * g o o' * v o'

/-- The elementary symmetric matrix with total weight `a` spread over the positions
`(o₁, o₂)` and `(o₂, o₁)`. -/
def symG (a : ℚ) (o₁ o₂ : Option (Fin r)) : Option (Fin r) → Option (Fin r) → ℚ :=
  fun o o' => (if o = o₁ ∧ o' = o₂ then a / 2 else 0)
    + (if o = o₂ ∧ o' = o₁ then a / 2 else 0)

theorem symG_symm (a : ℚ) (o₁ o₂ o o' : Option (Fin r)) :
    symG a o₁ o₂ o o' = symG a o₁ o₂ o' o := by
  simp only [symG]
  rw [add_comm]
  exact congrArg₂ (· + ·) (if_congr and_comm rfl rfl) (if_congr and_comm rfl rfl)

theorem quadFun_symG (a : ℚ) (o₁ o₂ : Option (Fin r)) (v : Option (Fin r) → ℚ) :
    quadFun (symG a o₁ o₂) v = a * v o₁ * v o₂ := by
  simp only [quadFun, symG, mul_add, add_mul, Finset.sum_add_distrib]
  have key : ∀ (p₁ p₂ : Option (Fin r)),
      (∑ o : Option (Fin r), ∑ o' : Option (Fin r),
        v o * (if o = p₁ ∧ o' = p₂ then a / 2 else 0) * v o') = a / 2 * v p₁ * v p₂ := by
    intro p₁ p₂
    rw [Finset.sum_eq_single p₁ ?_ ?_]
    · rw [Finset.sum_eq_single p₂ ?_ ?_]
      · rw [if_pos ⟨rfl, rfl⟩]
        ring
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro o' _
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [key o₁ o₂, key o₂ o₁]
  ring

theorem quadFun_add (g₁ g₂ : Option (Fin r) → Option (Fin r) → ℚ)
    (v : Option (Fin r) → ℚ) :
    quadFun (g₁ + g₂) v = quadFun g₁ v + quadFun g₂ v := by
  simp only [quadFun, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem quadFun_zero (v : Option (Fin r) → ℚ) :
    quadFun (0 : Option (Fin r) → Option (Fin r) → ℚ) v = 0 := by
  simp [quadFun]

theorem quadFun_list_sum (l : List (Option (Fin r) → Option (Fin r) → ℚ))
    (v : Option (Fin r) → ℚ) :
    quadFun l.sum v = (l.map fun g => quadFun g v).sum := by
  induction l with
  | nil => simpa using quadFun_zero v
  | cons g l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons, quadFun_add, ih]

namespace DegreeTwoEquation

/-- The raw coefficient matrix `(b_ij)` of the homogenization `t²·F(x/t)` of `F`. -/
def homogenizeFun (F : DegreeTwoEquation r) : Option (Fin r) → Option (Fin r) → ℚ :=
  (F.quad.map fun u => symG (u.1 : ℚ) (some u.2.1) (some u.2.2)).sum
    + (F.lin.map fun u => symG (u.1 : ℚ) (some u.2) none).sum
    + symG (F.const : ℚ) none none

theorem homogenizeFun_symm (F : DegreeTwoEquation r) (o o' : Option (Fin r)) :
    F.homogenizeFun o o' = F.homogenizeFun o' o := by
  have hsum : ∀ (l : List (Option (Fin r) → Option (Fin r) → ℚ)),
      (∀ g ∈ l, ∀ p q, g p q = g q p) → l.sum o o' = l.sum o' o := by
    intro l hl
    induction l with
    | nil => rfl
    | cons g t ih =>
        simp only [List.sum_cons, Pi.add_apply]
        rw [hl g (by simp) o o',
          ih fun g' hg' => hl g' (by simp [hg'])]
  have h1 := hsum (F.quad.map fun u => symG (u.1 : ℚ) (some u.2.1) (some u.2.2)) ?_
  · have h2 := hsum (F.lin.map fun u => symG (u.1 : ℚ) (some u.2) none) ?_
    · simp only [homogenizeFun, Pi.add_apply]
      rw [h1, h2, symG_symm]
    · rintro g hg p q
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg
      exact symG_symm _ _ _ _ _
  · rintro g hg p q
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg
    exact symG_symm _ _ _ _ _

/-- The symmetric matrix `(b_ij)` of the bilinear form of the homogenization `t²·F(x/t)` of `F`
[§3: the identification of quadrics with the algebras `A_Q`]. -/
def homogenize (F : DegreeTwoEquation r) : BilinearFormMatrix (Option (Fin r)) :=
  ⟨F.homogenizeFun, F.homogenizeFun_symm⟩

/-- The value of the homogenized form at `(x, t)`: quadratic part, plus `t` times the
linear part, plus `t²` times the constant. -/
theorem quad_homogenize (F : DegreeTwoEquation r) (x : Fin r → ℚ) (t : ℚ) :
    F.homogenize.quad (homVec x t)
      = (F.quad.map fun u => (u.1 : ℚ) * x u.2.1 * x u.2.2).sum
        + (F.lin.map fun u => (u.1 : ℚ) * x u.2).sum * t + (F.const : ℚ) * t ^ 2 := by
  classical
  have hq : F.homogenize.quad (homVec x t) = quadFun F.homogenizeFun (homVec x t) := by
    rw [F.homogenize.quad_eq_toQuadraticMap, LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toBilin'_apply]
    rfl
  rw [hq, homogenizeFun, quadFun_add, quadFun_add, quadFun_list_sum, quadFun_list_sum,
    quadFun_symG, List.map_map, List.map_map]
  rw [show ((fun g => quadFun g (homVec x t))
        ∘ fun u : ℤ × Fin r × Fin r => symG (u.1 : ℚ) (some u.2.1) (some u.2.2))
      = fun u : ℤ × Fin r × Fin r => (u.1 : ℚ) * x u.2.1 * x u.2.2 from
    funext fun u => by simp only [Function.comp_apply, quadFun_symG, homVec_some]]
  rw [show ((fun g => quadFun g (homVec x t))
        ∘ fun u : ℤ × Fin r => symG (u.1 : ℚ) (some u.2) none)
      = fun u : ℤ × Fin r => (u.1 : ℚ) * x u.2 * t from
    funext fun u => by simp only [Function.comp_apply, quadFun_symG, homVec_some,
      homVec_none]]
  rw [List.sum_map_mul_right, homVec_none]
  ring

/-- The quadratic part of `F` over `ℤ` (its value on the hyperplane at infinity). -/
def quadPart (F : DegreeTwoEquation r) (e : Fin r → ℤ) : ℤ :=
  (F.quad.map fun u => u.1 * e u.2.1 * e u.2.2).sum

theorem cast_list_sum_map {α : Type*} (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℚ) = (l.map fun a => (f a : ℚ)).sum := by
  rw [Int.cast_list_sum, List.map_map]
  rfl

/-- Affine chart `t = 1`: the homogenized form evaluates to `F` itself
[Lemma 4.2]. -/
theorem quadAt_homogenize_one (F : DegreeTwoEquation r) (z : Fin r → ℤ) :
    quadAt F.homogenize (ratCast z) 1 = (F.eval z : ℚ) := by
  rw [quadAt, quad_homogenize, eval, Int.cast_add, Int.cast_add, cast_list_sum_map,
    cast_list_sum_map,
    show (fun u : ℤ × Fin r × Fin r => ((u.1 * z u.2.1 * z u.2.2 : ℤ) : ℚ))
      = fun u : ℤ × Fin r × Fin r => (u.1 : ℚ) * ratCast z u.2.1 * ratCast z u.2.2 from
      funext fun u => by push_cast; simp [ratCast_apply],
    show (fun u : ℤ × Fin r => ((u.1 * z u.2 : ℤ) : ℚ))
      = fun u : ℤ × Fin r => (u.1 : ℚ) * ratCast z u.2 from
      funext fun u => by push_cast; simp [ratCast_apply]]
  ring

/-- Hyperplane at infinity `t = 0`: only the quadratic part survives
[Lemma 4.2]. -/
theorem quadAt_homogenize_zero (F : DegreeTwoEquation r) (e : Fin r → ℤ) :
    quadAt F.homogenize (ratCast e) 0 = (F.quadPart e : ℚ) := by
  rw [quadAt, quad_homogenize, quadPart, cast_list_sum_map,
    show (fun u : ℤ × Fin r × Fin r => ((u.1 * e u.2.1 * e u.2.2 : ℤ) : ℚ))
      = fun u : ℤ × Fin r × Fin r => (u.1 : ℚ) * ratCast e u.2.1 * ratCast e u.2.2 from
      funext fun u => by push_cast; simp [ratCast_apply]]
  ring

end DegreeTwoEquation

end Trinomial
