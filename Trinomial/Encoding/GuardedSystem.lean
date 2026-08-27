import Trinomial.Encoding.Homogenization
import Trinomial.Encoding.PellGuard
import Trinomial.Encoding.MainLaurent

/-!
# Lemma 4.2: the guarded system and its homogenization

[Lemma 4.2].  Given a system `L` of equations of degree at most two in
`r` variables, adjoin six variables `h, k, u₁, …, u₄` and the two guard equations

  `g_{m+1} = h² − 3k² − t²`   and   `g_{m+2} = Σ xᵢ² + Σ uⱼ² − h·t`,

shown here in the affine chart `t = 1`.

* `gPell`, `gSq`, `guarded L` — the guards and the guarded system in `r + 6` variables;
* `guarded_solvable_iff` — the guards do not change integral solvability ("in particular,
  `X = ∅ ⟺ X̂₁ = ∅`"; the surjective projection and its computable section are in
  `Trinomial/Encoding/GuardSection.lean`);
* `homogenizedSystem L'` — the homogenized forms `g₁, …, g_{m+2}` as matrices `(b_ij)`;
* `noIntegralSolutionAtInfinity_homogenizedSystem` — the homogenized guarded system has no
  nonzero integral solution with `t = 0` (`3` is not a square, and positivity); the
  paper's rational form is `Trinomial/Encoding/RationalInfinity.lean`;
* `homogenizedSystem_affine_iff` — the affine solutions `Q_i(d, 1) = 0` of the homogenized
  system are the integral solutions of the guarded system.
-/

set_option autoImplicit false

namespace Trinomial

variable {r : ℕ}

/-- The position of the Pell variable `h`. -/
def vh (r : ℕ) : Fin (r + 6) := ⟨r, by omega⟩
/-- The position of the Pell variable `k`. -/
def vk (r : ℕ) : Fin (r + 6) := ⟨r + 1, by omega⟩
/-- The positions of the four-squares variables `u₁, …, u₄`. -/
def vu (r : ℕ) (j : Fin 4) : Fin (r + 6) := ⟨r + 2 + j, by have := j.isLt; omega⟩

/-- The Pell guard `h² − 3k² − 1 = 0`  [Lemma 4.2, `g_{m+1}`]. -/
def gPell (r : ℕ) : DegreeTwoEquation (r + 6) :=
  ⟨[(1, vh r, vh r), (-3, vk r, vk r)], [], -1⟩

/-- The four-squares guard `Σ xᵢ² + Σ uⱼ² − h = 0`  [`g_{m+2}`]. -/
def gSq (r : ℕ) : DegreeTwoEquation (r + 6) :=
  ⟨((List.finRange r).map fun i => (1, Fin.castAdd 6 i, Fin.castAdd 6 i))
      ++ ((List.finRange 4).map fun j => (1, vu r j, vu r j)),
    [(-1, vh r)], 0⟩

/-- The guarded system: the homogenizable copy of `L` plus the two guards. -/
def guarded (L : List (DegreeTwoEquation r)) : List (DegreeTwoEquation (r + 6)) :=
  L.map (DegreeTwoEquation.rename (Fin.castAdd 6)) ++ [gPell r, gSq r]

/-! ### Evaluation of the guards -/

theorem gPell_eval (w : Fin (r + 6) → ℤ) :
    (gPell r).eval w = w (vh r) * w (vh r) - 3 * (w (vk r) * w (vk r)) - 1 := by
  simp [DegreeTwoEquation.eval, gPell]
  ring

theorem gPell_quadPart (e : Fin (r + 6) → ℤ) :
    (gPell r).quadPart e = e (vh r) * e (vh r) - 3 * (e (vk r) * e (vk r)) := by
  simp [DegreeTwoEquation.quadPart, gPell]
  ring

theorem list_sum_squares (m : ℕ) (f : Fin m → ℤ) :
    (((List.finRange m).map fun i => (1 : ℤ) * f i * f i)).sum = ∑ i, f i * f i := by
  rw [Fin.sum_univ_def]
  exact congrArg (fun g => (List.map g (List.finRange m)).sum)
    (funext fun i => by ring)

theorem gSq_eval (w : Fin (r + 6) → ℤ) :
    (gSq r).eval w = (∑ i : Fin r, w (Fin.castAdd 6 i) * w (Fin.castAdd 6 i))
      + (∑ j : Fin 4, w (vu r j) * w (vu r j)) - w (vh r) := by
  simp only [DegreeTwoEquation.eval, gSq, List.map_append, List.sum_append, List.map_map]
  rw [show ((fun t : ℤ × Fin (r+6) × Fin (r+6) => t.1 * w t.2.1 * w t.2.2)
        ∘ fun i : Fin r => ((1 : ℤ), Fin.castAdd 6 i, Fin.castAdd 6 i))
      = fun i : Fin r => (1 : ℤ) * w (Fin.castAdd 6 i) * w (Fin.castAdd 6 i) from rfl,
    show ((fun t : ℤ × Fin (r+6) × Fin (r+6) => t.1 * w t.2.1 * w t.2.2)
        ∘ fun j : Fin 4 => ((1 : ℤ), vu r j, vu r j))
      = fun j : Fin 4 => (1 : ℤ) * w (vu r j) * w (vu r j) from rfl,
    list_sum_squares, list_sum_squares]
  simp
  ring

theorem gSq_quadPart (e : Fin (r + 6) → ℤ) :
    (gSq r).quadPart e = (∑ i : Fin r, e (Fin.castAdd 6 i) * e (Fin.castAdd 6 i))
      + (∑ j : Fin 4, e (vu r j) * e (vu r j)) := by
  simp only [DegreeTwoEquation.quadPart, gSq, List.map_append, List.sum_append, List.map_map]
  rw [show ((fun t : ℤ × Fin (r+6) × Fin (r+6) => t.1 * e t.2.1 * e t.2.2)
        ∘ fun i : Fin r => ((1 : ℤ), Fin.castAdd 6 i, Fin.castAdd 6 i))
      = fun i : Fin r => (1 : ℤ) * e (Fin.castAdd 6 i) * e (Fin.castAdd 6 i) from rfl,
    show ((fun t : ℤ × Fin (r+6) × Fin (r+6) => t.1 * e t.2.1 * e t.2.2)
        ∘ fun j : Fin 4 => ((1 : ℤ), vu r j, vu r j))
      = fun j : Fin 4 => (1 : ℤ) * e (vu r j) * e (vu r j) from rfl,
    list_sum_squares, list_sum_squares]

/-! ### The guards preserve solvability  [Lemma 4.2, items 2–3] -/

theorem guarded_solvable_iff (L : List (DegreeTwoEquation r)) :
    (∃ w : Fin (r + 6) → ℤ, Solves w (guarded L)) ↔ ∃ z : Fin r → ℤ, Solves z L := by
  constructor
  · rintro ⟨w, hw⟩
    rw [guarded, solves_append] at hw
    exact ⟨w ∘ Fin.castAdd 6, solves_map_rename _ _ _ hw.1⟩
  · rintro ⟨z, hz⟩
    obtain ⟨h, k, hpell, hB⟩ := pell_solution_large (∑ i : Fin r, z i * z i)
    have hΔ : 0 ≤ h - ∑ i : Fin r, z i * z i := by omega
    obtain ⟨u1, u2, u3, u4, hu⟩ := four_squares_int _ hΔ
    -- the guard values `h, k, u₁, …, u₄` sit behind the `r` coordinates of `z`, at the
    -- positions `vh r, vk r, vu r 0, …, vu r 3`
    refine ⟨Fin.append z ![h, k, u1, u2, u3, u4], ?_⟩
    rw [guarded, solves_append]
    refine ⟨fun F hF => ?_, fun F hF => ?_⟩
    · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      rw [DegreeTwoEquation.eval_rename,
        show Fin.append z ![h, k, u1, u2, u3, u4] ∘ Fin.castAdd 6 = z from
          funext fun i => Fin.append_left _ _ i]
      exact hz G hG
    · have hh : Fin.append z ![h, k, u1, u2, u3, u4] (vh r) = h := Fin.append_right z _ 0
      rcases List.mem_cons.mp hF with rfl | hF'
      · rw [gPell_eval, hh,
          show Fin.append z ![h, k, u1, u2, u3, u4] (vk r) = k from Fin.append_right z _ 1]
        linarith [hpell]
      · rw [List.mem_singleton] at hF'
        subst hF'
        rw [gSq_eval, hh, Fin.sum_univ_four,
          show Fin.append z ![h, k, u1, u2, u3, u4] (vu r 0) = u1 from Fin.append_right z _ 2,
          show Fin.append z ![h, k, u1, u2, u3, u4] (vu r 1) = u2 from Fin.append_right z _ 3,
          show Fin.append z ![h, k, u1, u2, u3, u4] (vu r 2) = u3 from Fin.append_right z _ 4,
          show Fin.append z ![h, k, u1, u2, u3, u4] (vu r 3) = u4 from Fin.append_right z _ 5]
        simp only [Fin.append_left]
        nlinarith [hu]

/-! ### No solutions at infinity  [Lemma 4.2, item 1] -/

/-- The family of matrices `(b_ij)` of the bilinear forms of a system, indexed by list position. -/
def homogenizedSystem {N : ℕ} (L' : List (DegreeTwoEquation N)) :
    Fin L'.length → BilinearFormMatrix (Option (Fin N)) :=
  fun i => (L'.get i).homogenize

theorem noIntegralSolutionAtInfinity_homogenizedSystem (L : List (DegreeTwoEquation r)) :
    NoIntegralSolutionAtInfinity (homogenizedSystem (guarded L)) := by
  intro e he
  by_contra hall
  push_neg at hall
  have hqp : ∀ F ∈ guarded L, F.quadPart e = 0 := by
    intro F hF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hF
    have := hall i
    rw [homogenizedSystem, hi, DegreeTwoEquation.quadAt_homogenize_zero] at this
    exact_mod_cast this
  have hpell : (gPell r).quadPart e = 0 :=
    hqp _ (by rw [guarded]; exact List.mem_append_right _ (by simp))
  have hsq : (gSq r).quadPart e = 0 :=
    hqp _ (by rw [guarded]; exact List.mem_append_right _ (by simp))
  rw [gPell_quadPart] at hpell
  rw [gSq_quadPart] at hsq
  have hhk := pell_guard_at_infinity (h := e (vh r)) (k := e (vk r)) (by linarith [hpell])
  have hx : ∀ i : Fin r, e (Fin.castAdd 6 i) = 0 := by
    intro i
    have h1 : (0 : ℤ) ≤ ∑ i : Fin r, e (Fin.castAdd 6 i) * e (Fin.castAdd 6 i) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : (0 : ℤ) ≤ ∑ j : Fin 4, e (vu r j) * e (vu r j) :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have h3 : (∑ i : Fin r, e (Fin.castAdd 6 i) * e (Fin.castAdd 6 i)) = 0 := by omega
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (e (Fin.castAdd 6 i)))).mp h3 i (Finset.mem_univ i)
    nlinarith [this]
  have hu : ∀ j : Fin 4, e (vu r j) = 0 := by
    intro j
    have h1 : (0 : ℤ) ≤ ∑ i : Fin r, e (Fin.castAdd 6 i) * e (Fin.castAdd 6 i) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : (0 : ℤ) ≤ ∑ j : Fin 4, e (vu r j) * e (vu r j) :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have h3 : (∑ j : Fin 4, e (vu r j) * e (vu r j)) = 0 := by omega
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (e (vu r j)))).mp h3 j (Finset.mem_univ j)
    nlinarith [this]
  apply he
  funext idx
  rcases lt_or_ge (idx : ℕ) r with hlt | hge
  · have : idx = Fin.castAdd 6 ⟨idx, hlt⟩ := Fin.ext rfl
    rw [this]
    exact hx _
  · have h6 := idx.isLt
    rcases (by omega : (idx : ℕ) = r ∨ (idx : ℕ) = r + 1 ∨ (idx : ℕ) = r + 2
      ∨ (idx : ℕ) = r + 3 ∨ (idx : ℕ) = r + 4 ∨ (idx : ℕ) = r + 5) with
      h | h | h | h | h | h
    · rw [show idx = vh r from Fin.ext h]
      exact hhk.1
    · rw [show idx = vk r from Fin.ext h]
      exact hhk.2
    · rw [show idx = vu r 0 from Fin.ext (by simpa using h)]
      exact hu 0
    · rw [show idx = vu r 1 from Fin.ext (by simpa using h)]
      exact hu 1
    · rw [show idx = vu r 2 from Fin.ext (by simpa using h)]
      exact hu 2
    · rw [show idx = vu r 3 from Fin.ext (by simpa using h)]
      exact hu 3

/-! ### Theorem 4.5, Laurent side, for an arbitrary integer polynomial -/

theorem homogenizedSystem_affine_iff {N : ℕ} (L' : List (DegreeTwoEquation N)) :
    (∃ d : Fin N → ℤ, ∀ i, quadAt (homogenizedSystem L' i) (ratCast d) 1 = 0)
      ↔ ∃ w : Fin N → ℤ, Solves w L' := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, fun F hF => ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hF
    have := hd i
    rw [homogenizedSystem, hi, DegreeTwoEquation.quadAt_homogenize_one] at this
    exact_mod_cast this
  · rintro ⟨w, hw⟩
    refine ⟨w, fun i => ?_⟩
    rw [homogenizedSystem, DegreeTwoEquation.quadAt_homogenize_one]
    exact_mod_cast hw _ (List.get_mem L' i)

end Trinomial
