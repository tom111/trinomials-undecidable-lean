import Trinomial.Encoding.MainTheorem
import Trinomial.Encoding.GuardSection
import Trinomial.Base.PrimitiveNormalization

/-!
# Geometry of the reduction

This module formalizes the chain in [Remark 4.7]

`𝒯(J_P) ≃ X̂₁ ↠ X ≃ {y ∈ ℤⁿ | P(y) = 0}`.

The type `NormalizedTauTrinomials p` uses the normalized representatives `τ_d` of the
unit classes of trinomials in the guarded Laurent ideal.  Proposition 2.4 and the
no-solution-at-infinity property show that every trinomial class has this form.  The left
equivalence identifies `τ_d` with the affine point `(d, 1)` of the homogenized guarded
system.  The middle map forgets the six guard coordinates and has the executable section
`guardSection`.  The right equivalence projects a straight-line-program solution to its
input coordinates.  Its inverse exists because every program gate defines one new
coordinate, formalized below by `StraightLineProgram.Determines`.
-/

set_option autoImplicit false

namespace Trinomial

open TrinomialUndecidability.Computability (IntExponent IntPolynomialCode evalPolynomial)

/-! ### Arithmetic progressions of affine trinomials -/

/-- In a guarded reduction ideal, three affine trinomials whose exponent vectors form
a nonconstant arithmetic progression cannot all occur.  This is the consequence of the
displayed identity in Remark 4.4 and the absence of solutions at infinity. -/
theorem not_all_tau_mem_of_arithmetic_progression
    {N M : ℕ} {Q : Fin M → BilinearFormMatrix (Option (Fin N))}
    (guard : NoIntegralSolutionAtInfinity Q) {d e : Fin N → ℤ} (he : e ≠ 0) :
    ¬ (tau (d - e) ∈ reductionIdeal Q ∧ tau d ∈ reductionIdeal Q ∧
        tau (d + e) ∈ reductionIdeal Q) := by
  rintro ⟨hminus, hzero, hplus⟩
  obtain ⟨g, e', hg, he', -, htheta⟩ :=
    infinite_trinomial_mem_of_tau_arithmetic_progression
      (reductionIdeal Q) he hminus hzero hplus
  obtain ⟨i, hi⟩ := guard e' he'.ne_zero
  have hk := (mem_reductionIdeal_iff.mp htheta).2 i
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hneg0 : -(g : ℤ) ≠ 0 := neg_ne_zero.mpr hg0
  have hdistinct : (g : ℤ) ≠ -(g : ℤ) := by omega
  exact hi ((theta_mem_ker_phi_iff (Q i) e' hg0 hneg0 hdistinct).mp hk)

/-! ### Multiplication by nonzero Laurent terms -/

/-- `TermRelated f g` means that `g` is obtained from `f` by multiplication by a
nonzero rational scalar and a Laurent monomial.  This is the equivalence relation used
for the paper's trinomials "up to multiplication by units." -/
def TermRelated {N : ℕ} (f g : Laurent N) : Prop :=
  ∃ (c : ℚ) (z : Exponent N), c ≠ 0 ∧ g = c • (mono z * f)

theorem termRelated_refl {N : ℕ} (f : Laurent N) : TermRelated f f := by
  refine ⟨1, 0, one_ne_zero, ?_⟩
  simp

theorem termRelated_symm {N : ℕ} {f g : Laurent N}
    (h : TermRelated f g) : TermRelated g f := by
  obtain ⟨c, z, hc, rfl⟩ := h
  refine ⟨c⁻¹, -z, inv_ne_zero hc, ?_⟩
  rw [mul_smul_comm, smul_smul, inv_mul_cancel₀ hc, one_smul, ← mul_assoc,
    mono_mul, neg_add_cancel, mono_zero, one_mul]

theorem termRelated_trans {N : ℕ} {f g h : Laurent N}
    (hfg : TermRelated f g) (hgh : TermRelated g h) : TermRelated f h := by
  obtain ⟨c, z, hc, rfl⟩ := hfg
  obtain ⟨c', z', hc', rfl⟩ := hgh
  refine ⟨c' * c, z' + z, mul_ne_zero hc' hc, ?_⟩
  rw [mul_smul_comm, smul_smul, ← mul_assoc, mono_mul]

def termSetoid (N : ℕ) : Setoid (Laurent N) where
  r := TermRelated
  iseqv := ⟨termRelated_refl, termRelated_symm, termRelated_trans⟩

/-- Distinct normalized affine trinomials are not related by multiplication by a
nonzero Laurent term. -/
theorem tau_termRelated_iff {N : ℕ} {d e : Fin N → ℤ} :
    TermRelated (tau d) (tau e) ↔ d = e := by
  constructor
  · rintro ⟨c, z, hc, h⟩
    have support_mem (x : Exponent N) (hx : x ∈ (tau d).support) :
        z + x ∈ (tau e).support := by
      rw [h, support_smul_mono_mul hc]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hz : z ∈ (tau e).support := by
      convert support_mem 0 (by rw [support_tau]; simp) using 1
      simp
    have support_s_le_one (x : Exponent N) (hx : x ∈ (tau e).support) : x.s ≤ 1 := by
      rw [support_tau] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp
    have support_t_le_one (x : Exponent N) (hx : x ∈ (tau e).support) : x.t ≤ 1 := by
      rw [support_tau] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp
    rw [support_tau] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have hz0 : z = 0 := by
      rcases hz with hz | hz | hz
      · exact hz
      · have hm := support_mem (⟨1, 0, d⟩ : Exponent N)
          (by rw [support_tau]; simp)
        have hle := support_s_le_one _ hm
        rw [hz] at hle
        simp at hle
      · have hm := support_mem (⟨0, 1, -d⟩ : Exponent N)
          (by rw [support_tau]; simp)
        have hle := support_t_le_one _ hm
        rw [hz] at hle
        simp at hle
    subst z
    have hm := support_mem (⟨1, 0, d⟩ : Exponent N) (by rw [support_tau]; simp)
    rw [support_tau] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton, zero_add] at hm
    rcases hm with hm | hm | hm
    · have hs := congrArg Exponent.s hm
      simp at hs
    · exact congrArg Exponent.d hm
    · have hs := congrArg Exponent.s hm
      simp at hs
  · rintro rfl
    exact termRelated_refl _

namespace StraightLineProgram

variable {n : ℕ}

/-- A straight line program determines all auxiliary coordinates from its input
coordinates. -/
def Determines (Γ : StraightLineProgram n) : Prop :=
  ∀ z z' : Fin (n + Γ.k) → ℤ, Solves z Γ.gates → Solves z' Γ.gates →
    (∀ i : Fin n, z (Fin.castAdd Γ.k i) = z' (Fin.castAdd Γ.k i)) → z = z'

theorem const_determines (a : ℤ) : (const (n := n) a).Determines := by
  intro z z' hz hz' hin
  dsimp only [const] at z z' hz hz' hin ⊢
  funext i
  by_cases hi : (i : ℕ) < n
  · have hii : i = Fin.castAdd 1 ⟨i, hi⟩ := Fin.ext rfl
    rw [hii]
    exact hin _
  · have hii : i = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    rw [hii]
    have h := hz _ (List.mem_singleton_self _)
    have h' := hz' _ (List.mem_singleton_self _)
    rw [DegreeTwoEquation.eqConst_eval] at h h'
    omega

theorem var_determines (j : Fin n) : (var j).Determines := by
  intro z z' hz hz' hin
  dsimp only [var] at z z' hz hz' hin ⊢
  funext i
  by_cases hi : (i : ℕ) < n
  · have hii : i = Fin.castAdd 1 ⟨i, hi⟩ := Fin.ext rfl
    rw [hii]
    exact hin _
  · have hii : i = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    rw [hii]
    have h := hz _ (List.mem_singleton_self _)
    have h' := hz' _ (List.mem_singleton_self _)
    rw [eqCopy_eval, sub_eq_zero] at h h'
    rw [h, h']
    exact hin j

theorem binary_determines
    {G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r}
    {g : ℤ → ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o i j : Fin r) (z : Fin r → ℤ),
      (G o i j).eval z = z o - g (z i) (z j))
    {Γ₁ Γ₂ : StraightLineProgram n} (h₁ : Γ₁.Determines) (h₂ : Γ₂.Determines) :
    (binary G Γ₁ Γ₂).Determines := by
  intro z z' hz hz' hin
  dsimp only [binary] at z z' hz hz' hin ⊢
  rw [solves_append, solves_append] at hz hz'
  obtain ⟨⟨hz₁, hz₂⟩, hzout⟩ := hz
  obtain ⟨⟨hz₁', hz₂'⟩, hzout'⟩ := hz'
  have heq₁ : z ∘ incl₁ n Γ₁.k Γ₂.k = z' ∘ incl₁ n Γ₁.k Γ₂.k := by
    apply h₁
    · exact solves_map_rename _ _ _ hz₁
    · exact solves_map_rename _ _ _ hz₁'
    · intro i
      simp only [Function.comp_apply, incl₁_castAdd]
      exact hin i
  have heq₂ : z ∘ incl₂ n Γ₁.k Γ₂.k = z' ∘ incl₂ n Γ₁.k Γ₂.k := by
    apply h₂
    · exact solves_map_rename _ _ _ hz₂
    · exact solves_map_rename _ _ _ hz₂'
    · intro i
      simp only [Function.comp_apply, incl₂_castAdd]
      exact hin i
  have hout : z (outPos n Γ₁.k Γ₂.k) = z' (outPos n Γ₁.k Γ₂.k) := by
    have h := hzout _ (List.mem_singleton_self _)
    have h' := hzout' _ (List.mem_singleton_self _)
    have he₁ := congrFun heq₁ Γ₁.out
    have he₂ := congrFun heq₂ Γ₂.out
    simp only [Function.comp_apply] at he₁ he₂
    rw [hG, sub_eq_zero] at h h'
    rw [h, h', he₁, he₂]
  funext i
  by_cases hi₁ : (i : ℕ) < n + Γ₁.k
  · let j : Fin (n + Γ₁.k) := ⟨i, hi₁⟩
    have hij : incl₁ n Γ₁.k Γ₂.k j = i := Fin.ext rfl
    rw [← hij]
    exact congrFun heq₁ j
  · by_cases hi₂ : (i : ℕ) < n + Γ₁.k + Γ₂.k
    · let j : Fin (n + Γ₂.k) := ⟨(i : ℕ) - Γ₁.k, by omega⟩
      have hj : ¬(j : ℕ) < n := by
        dsimp only [j]
        omega
      have hij : incl₂ n Γ₁.k Γ₂.k j = i := by
        apply Fin.ext
        simp only [incl₂, dif_neg hj, j]
        omega
      rw [← hij]
      exact congrFun heq₂ j
    · have hij : i = outPos n Γ₁.k Γ₂.k := by
        apply Fin.ext
        have := i.isLt
        simp only [outPos]
        omega
      rw [hij]
      exact hout

theorem unary_determines
    {G : ∀ {r : ℕ}, Fin r → Fin r → DegreeTwoEquation r} {g : ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o i : Fin r) (z : Fin r → ℤ), (G o i).eval z = z o - g (z i))
    {Γ : StraightLineProgram n} (h : Γ.Determines) : (unary G Γ).Determines := by
  intro z z' hz hz' hin
  dsimp only [unary] at z z' hz hz' hin ⊢
  rw [solves_append] at hz hz'
  obtain ⟨hzΓ, hzout⟩ := hz
  obtain ⟨hzΓ', hzout'⟩ := hz'
  have heq : z ∘ incl₁ n Γ.k 0 = z' ∘ incl₁ n Γ.k 0 := by
    apply h
    · exact solves_map_rename _ _ _ hzΓ
    · exact solves_map_rename _ _ _ hzΓ'
    · intro i
      simp only [Function.comp_apply, incl₁_castAdd]
      exact hin i
  have hout : z (outPos n Γ.k 0) = z' (outPos n Γ.k 0) := by
    have ho := hzout _ (List.mem_singleton_self _)
    have ho' := hzout' _ (List.mem_singleton_self _)
    have he := congrFun heq Γ.out
    simp only [Function.comp_apply] at he
    rw [hG, sub_eq_zero] at ho ho'
    rw [ho, ho', he]
  funext i
  by_cases hi : (i : ℕ) < n + Γ.k
  · let j : Fin (n + Γ.k) := ⟨i, hi⟩
    have hij : incl₁ n Γ.k 0 j = i := Fin.ext rfl
    rw [← hij]
    exact congrFun heq j
  · have hij : i = outPos n Γ.k 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [outPos]
      omega
    rw [hij]
    exact hout

theorem unaryInput_determines
    {G : ∀ {r : ℕ}, Fin r → Fin r → Fin r → DegreeTwoEquation r}
    {g : ℤ → ℤ → ℤ}
    (hG : ∀ {r : ℕ} (o a b : Fin r) (z : Fin r → ℤ),
      (G o a b).eval z = z o - g (z a) (z b))
    {Γ : StraightLineProgram n} (h : Γ.Determines) (j : Fin n) :
    (unaryInput G Γ j).Determines := by
  intro z z' hz hz' hin
  dsimp only [unaryInput] at z z' hz hz' hin ⊢
  rw [solves_append] at hz hz'
  obtain ⟨hzΓ, hzout⟩ := hz
  obtain ⟨hzΓ', hzout'⟩ := hz'
  have heq : z ∘ incl₁ n Γ.k 0 = z' ∘ incl₁ n Γ.k 0 := by
    apply h
    · exact solves_map_rename _ _ _ hzΓ
    · exact solves_map_rename _ _ _ hzΓ'
    · intro i
      simp only [Function.comp_apply, incl₁_castAdd]
      exact hin i
  have hout : z (outPos n Γ.k 0) = z' (outPos n Γ.k 0) := by
    have ho := hzout _ (List.mem_singleton_self _)
    have ho' := hzout' _ (List.mem_singleton_self _)
    have he := congrFun heq Γ.out
    simp only [Function.comp_apply] at he
    rw [hG, sub_eq_zero] at ho ho'
    rw [ho, ho', he, hin j]
  funext i
  by_cases hi : (i : ℕ) < n + Γ.k
  · let a : Fin (n + Γ.k) := ⟨i, hi⟩
    have hai : incl₁ n Γ.k 0 a = i := Fin.ext rfl
    rw [← hai]
    exact congrFun heq a
  · have hii : i = outPos n Γ.k 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [outPos]
      omega
    rw [hii]
    exact hout

theorem add_determines {Γ₁ Γ₂ : StraightLineProgram n}
    (h₁ : Γ₁.Determines) (h₂ : Γ₂.Determines) : (add Γ₁ Γ₂).Determines :=
  binary_determines (g := fun a b => a + b)
    (fun o i j z => by rw [DegreeTwoEquation.eqAdd_eval]; ring) h₁ h₂

theorem mul_determines {Γ₁ Γ₂ : StraightLineProgram n}
    (h₁ : Γ₁.Determines) (h₂ : Γ₂.Determines) : (mul Γ₁ Γ₂).Determines :=
  binary_determines (fun o i j z => DegreeTwoEquation.eqMul_eval o i j z) h₁ h₂

theorem scale_determines (c : ℤ) {Γ : StraightLineProgram n} (h : Γ.Determines) :
    (scale c Γ).Determines :=
  unary_determines (fun o i z => eqScale_eval o c i z) h

theorem mulVar_determines {Γ : StraightLineProgram n} (h : Γ.Determines) (i : Fin n) :
    (mulVar Γ i).Determines :=
  unaryInput_determines (fun o a b z => DegreeTwoEquation.eqMul_eval o a b z) h i

theorem pow_determines (i : Fin n) : ∀ m : ℕ, (pow i m).Determines
  | 0 => const_determines 1
  | 1 => var_determines i
  | m + 2 => mulVar_determines (pow_determines i (m + 1)) i

theorem iterate_mulVar_determines {Γ : StraightLineProgram n} (h : Γ.Determines)
    (i : Fin n) : ∀ m : ℕ, ((fun Δ => mulVar Δ i)^[m] Γ).Determines
  | 0 => h
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact mulVar_determines (iterate_mulVar_determines h i m) i

theorem monomialAux_determines (e : IntExponent n) :
    ∀ (l : List (Fin n)) (Γ : StraightLineProgram n),
      monomialAux e l = some Γ → Γ.Determines
  | [], Γ, h => by simp [monomialAux] at h
  | i :: l, Γ, h => by
      simp only [monomialAux] at h
      split at h
      · rename_i hl
        split at h
        · simp at h
        · obtain rfl := Option.some.inj h
          exact pow_determines i (e i)
      · rename_i Δ hΔ
        obtain rfl := Option.some.inj h
        exact iterate_mulVar_determines (monomialAux_determines e l Δ hΔ) i (e i)

theorem monomial_determines (e : IntExponent n) : (monomial e).Determines := by
  unfold monomial
  cases h : monomialAux e (List.finRange n) with
  | none => exact const_determines 1
  | some Γ => exact monomialAux_determines e _ Γ h

/-- Every program produced by the polynomial compiler determines all of its auxiliary
coordinates from the input coordinates. -/
theorem ofCode_determines : ∀ p : IntPolynomialCode n, (ofCode p).Determines
  | [] => const_determines 0
  | [(e, c)] => scale_determines c (monomial_determines e)
  | (e, c) :: t :: p =>
      add_determines (scale_determines c (monomial_determines e)) (ofCode_determines (t :: p))

end StraightLineProgram

/-- A solution of `degreeTwoSystem p` is uniquely determined by its first `n` input
coordinates. -/
theorem degreeTwoSystem_determines {n : ℕ} (p : IntPolynomialCode n) :
    ∀ z z' : Fin (n + (StraightLineProgram.ofCode p).k) → ℤ,
      Solves z (degreeTwoSystem p) → Solves z' (degreeTwoSystem p) →
      (∀ i : Fin n, z (Fin.castAdd _ i) = z' (Fin.castAdd _ i)) → z = z' := by
  intro z z' hz hz' hin
  unfold degreeTwoSystem at hz hz'
  rw [solves_append] at hz hz'
  exact StraightLineProgram.ofCode_determines p z z' hz.1 hz'.1 hin

/-! ### The three solution sets in Remark 4.7 -/

/-- The integral solution set of a list of degree-two equations. -/
def IntegralSolutions {r : ℕ} (L : List (DegreeTwoEquation r)) :=
  {z : Fin r → ℤ // Solves z L}

/-- Projection from the guarded solution set `X̂₁` to the original solution set `X`. -/
def guardProjection {r : ℕ} (L : List (DegreeTwoEquation r)) :
    IntegralSolutions (guarded L) → IntegralSolutions L := fun w =>
  ⟨w.1 ∘ Fin.castAdd 6, by
    have hw := w.2
    unfold guarded at hw
    rw [solves_append] at hw
    exact solves_map_rename _ _ _ hw.1⟩

/-- The executable section of `guardProjection`, restricted to solution sets. -/
def guardSolutionSection {r : ℕ} (L : List (DegreeTwoEquation r)) :
    IntegralSolutions L → IntegralSolutions (guarded L) := fun z =>
  ⟨guardSection z.1, guardSection_solves z.2⟩

theorem guardProjection_section {r : ℕ} (L : List (DegreeTwoEquation r)) :
    Function.LeftInverse (guardProjection L) (guardSolutionSection L) := by
  intro z
  apply Subtype.ext
  funext i
  exact guardSection_castAdd z.1 i

/-- The forgetful map `X̂₁ → X` is surjective. -/
theorem guardProjection_surjective {r : ℕ} (L : List (DegreeTwoEquation r)) :
    Function.Surjective (guardProjection L) :=
  (guardProjection_section L).surjective

/-- A family of completions of `z` indexed by the Pell solutions.  The first Pell
coordinate grows strictly with `m`, so these completions are pairwise distinct. -/
def guardFiberPoint {r : ℕ} (z : Fin r → ℤ) (m : ℕ) : Fin (r + 6) → ℤ :=
  let S := ∑ i, z i * z i
  let hk := pell3 (S.toNat + m)
  let u := fourSquares (hk.1 - S).toNat
  Fin.append z ![hk.1, hk.2, u.1, u.2.1, u.2.2.1, u.2.2.2]

@[simp] theorem guardFiberPoint_castAdd {r : ℕ} (z : Fin r → ℤ) (m : ℕ) (i : Fin r) :
    guardFiberPoint z m (Fin.castAdd 6 i) = z i :=
  Fin.append_left _ _ i

theorem guardFiberPoint_solves {r : ℕ} {L : List (DegreeTwoEquation r)}
    {z : Fin r → ℤ} (hz : Solves z L) (m : ℕ) :
    Solves (guardFiberPoint z m) (guarded L) := by
  let S : ℤ := ∑ i, z i * z i
  let hk := pell3 (S.toNat + m)
  let u := fourSquares (hk.1 - S).toNat
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have hDelta : 0 ≤ hk.1 - S := by
    have hgrowth := pell3_growth (S.toNat + m)
    have hcast : (S.toNat : ℤ) = S := Int.toNat_of_nonneg hS
    apply sub_nonneg.mpr
    dsimp only [hk]
    calc
      S = (S.toNat : ℤ) := hcast.symm
      _ ≤ ((S.toNat + m : ℕ) : ℤ) := by omega
      _ ≤ (pell3 (S.toNat + m)).1 := hgrowth
  have hu := congrArg (Nat.cast : ℕ → ℤ) (fourSquares_spec (hk.1 - S).toNat)
  push_cast at hu
  rw [Int.toNat_of_nonneg hDelta] at hu
  change Solves (Fin.append z ![hk.1, hk.2, u.1, u.2.1, u.2.2.1, u.2.2.2]) (guarded L)
  exact solves_guarded_append hz (pell3_eq _) (by linarith)

theorem guardFiberPoint_injective {r : ℕ} (z : Fin r → ℤ) :
    Function.Injective (guardFiberPoint z) := by
  intro a b hab
  have h := congrFun hab (vh r)
  simp only [guardFiberPoint, append_vh, Matrix.cons_val] at h
  simp only [pell3] at h
  have hnat :
      Pell.xn one_lt_two' ((∑ i, z i * z i).toNat + a) =
        Pell.xn one_lt_two' ((∑ i, z i * z i).toNat + b) := by
    exact_mod_cast h
  exact Nat.add_left_cancel ((Pell.strictMono_x one_lt_two').injective hnat)

/-- Every fiber of the forgetful map `X̂₁ → X` contains an injectively indexed copy of
`ℕ`, hence is infinite. -/
theorem guardProjection_infinite_fibers {r : ℕ} (L : List (DegreeTwoEquation r))
    (z : IntegralSolutions L) :
    ∃ w : ℕ → IntegralSolutions (guarded L), Function.Injective w ∧
      ∀ m, guardProjection L (w m) = z := by
  let w : ℕ → IntegralSolutions (guarded L) := fun m =>
    ⟨guardFiberPoint z.1 m, guardFiberPoint_solves z.2 m⟩
  refine ⟨w, ?_, ?_⟩
  · intro a b hab
    apply guardFiberPoint_injective z.1
    exact congrArg Subtype.val hab
  · intro m
    apply Subtype.ext
    funext i
    exact guardFiberPoint_castAdd z.1 m i

/-- Pointwise form of the affine-chart bridge: an integral assignment solves `L` exactly
when `(d, 1)` vanishes on every homogenized form. -/
theorem solves_iff_quadAt_homogenizedSystem {r : ℕ} (L : List (DegreeTwoEquation r))
    (d : Fin r → ℤ) :
    Solves d L ↔ ∀ i, quadAt (homogenizedSystem L i) (ratCast d) 1 = 0 := by
  constructor
  · intro hd i
    rw [homogenizedSystem, DegreeTwoEquation.quadAt_homogenize_one]
    exact_mod_cast hd _ (List.get_mem L i)
  · intro hd F hF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hF
    have h := hd i
    rw [homogenizedSystem, hi, DegreeTwoEquation.quadAt_homogenize_one] at h
    exact_mod_cast h

variable {n : ℕ}

/-- The normalized representatives `τ_d` of the unit classes of trinomials in `J_P`.
The subtype condition says that the representative belongs to the guarded Laurent ideal. -/
def NormalizedTauTrinomials (p : IntPolynomialCode n) :=
  {d : Fin (numVars p) → ℤ // tau d ∈ reductionIdeal (quadraticForms p)}

/-- The guarded affine solution set `X̂₁` associated with `p`. -/
abbrev GuardedSolutionSet (p : IntPolynomialCode n) :=
  IntegralSolutions (guarded (degreeTwoSystem p))

/-- The trinomials belonging to the guarded Laurent ideal attached to `p`. -/
def TrinomialsInReductionIdeal (p : IntPolynomialCode n) :=
  {f : Laurent (numVars p) //
    f ∈ reductionIdeal (quadraticForms p) ∧ f.support.card = 3}

/-- Two trinomials are identified when one is obtained from the other by multiplication
by a nonzero rational scalar and a Laurent monomial. -/
def trinomialAssociationSetoid (p : IntPolynomialCode n) :
    Setoid (TrinomialsInReductionIdeal p) where
  r f g := TermRelated f.1 g.1
  iseqv := ⟨fun f => termRelated_refl f.1,
    fun {_ _} h => termRelated_symm h,
    fun {_ _ _} h₁ h₂ => termRelated_trans h₁ h₂⟩

/-- The paper's set `𝒻(J_P)` of trinomials modulo multiplication by nonzero terms. -/
def TrinomialClasses (p : IntPolynomialCode n) :=
  Quotient (trinomialAssociationSetoid p)

/-- The class of the normalized representative `τ_d`. -/
noncomputable def normalizedTauClass (p : IntPolynomialCode n) :
    NormalizedTauTrinomials p → TrinomialClasses p := fun d =>
  Quotient.mk''
    (⟨tau d.1, d.2, supportCard_tau d.1⟩ : TrinomialsInReductionIdeal p)

theorem normalizedTauClass_injective (p : IntPolynomialCode n) :
    Function.Injective (normalizedTauClass p) := by
  intro d e h
  apply Subtype.ext
  exact tau_termRelated_iff.mp (Quotient.exact h)

theorem normalizedTauClass_surjective (p : IntPolynomialCode n) :
    Function.Surjective (normalizedTauClass p) := by
  intro q
  induction q using Quotient.inductionOn' with
  | _ f =>
      obtain ⟨c, z, d, hc, hf, hd⟩ := trinomial_in_reductionIdeal
        (noIntegralSolutionAtInfinity_homogenizedSystem (degreeTwoSystem p)) f.2.1 f.2.2
      let d' : NormalizedTauTrinomials p :=
        ⟨d, (tau_mem_reductionIdeal_iff (quadraticForms p) d).mpr hd⟩
      refine ⟨d', ?_⟩
      apply Quotient.sound
      exact ⟨c, z, hc, hf⟩

/-- Every class of trinomials in `J_P` has one and only one normalized representative
`τ_d`. -/
noncomputable def trinomialClassesEquivNormalized (p : IntPolynomialCode n) :
    TrinomialClasses p ≃ NormalizedTauTrinomials p :=
  (Equiv.ofBijective (normalizedTauClass p)
    ⟨normalizedTauClass_injective p, normalizedTauClass_surjective p⟩).symm

/-- The degree-two-system solution set `X` associated with `p`. -/
abbrev DegreeTwoSolutionSet (p : IntPolynomialCode n) :=
  IntegralSolutions (degreeTwoSystem p)

/-- The hypersurface `Y = {y ∈ ℤⁿ | P(y) = 0}`. -/
def PolynomialZeroSet (p : IntPolynomialCode n) :=
  {y : Fin n → ℤ // evalPolynomial p y = 0}

theorem tau_mem_reductionIdeal_iff_guarded (p : IntPolynomialCode n)
    (d : Fin (numVars p) → ℤ) :
    tau d ∈ reductionIdeal (quadraticForms p) ↔
      Solves d (guarded (degreeTwoSystem p)) :=
  (tau_mem_reductionIdeal_iff (quadraticForms p) d).trans
    (solves_iff_quadAt_homogenizedSystem (guarded (degreeTwoSystem p)) d).symm

/-- The left bijection of Remark 4.7.  It sends the normalized class represented by
`τ_d` to the affine guarded point `(d, 1)`.  The homogenizing coordinate `1` is implicit in
the definition of `GuardedSolutionSet`. -/
def normalizedTauEquivGuarded (p : IntPolynomialCode n) :
    NormalizedTauTrinomials p ≃ GuardedSolutionSet p where
  toFun d := ⟨d.1, (tau_mem_reductionIdeal_iff_guarded p d.1).mp d.2⟩
  invFun d := ⟨d.1, (tau_mem_reductionIdeal_iff_guarded p d.1).mpr d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The left bijection in Remark 4.7, from classes of trinomials modulo nonzero
terms to the guarded affine solution set. -/
noncomputable def trinomialClassesEquivGuarded (p : IntPolynomialCode n) :
    TrinomialClasses p ≃ GuardedSolutionSet p :=
  (trinomialClassesEquivNormalized p).trans (normalizedTauEquivGuarded p)

@[simp] theorem trinomialClassesEquivGuarded_normalizedTauClass
    (p : IntPolynomialCode n) (d : NormalizedTauTrinomials p) :
    trinomialClassesEquivGuarded p (normalizedTauClass p d) =
      normalizedTauEquivGuarded p d := by
  simp [trinomialClassesEquivGuarded, trinomialClassesEquivNormalized]

@[simp] theorem normalizedTauEquivGuarded_apply (p : IntPolynomialCode n)
    (d : NormalizedTauTrinomials p) :
    (normalizedTauEquivGuarded p d).1 = d.1 :=
  rfl

/-- Projection of a solution of the straight-line-program system to the input coordinates. -/
def degreeTwoInput (p : IntPolynomialCode n) :
    DegreeTwoSolutionSet p → PolynomialZeroSet p := fun z =>
  ⟨fun i => z.1 (Fin.castAdd _ i), by
    have hz := z.2
    unfold degreeTwoSystem at hz
    rw [solves_append] at hz
    have hout := hz.2 _ (List.mem_singleton_self _)
    rw [DegreeTwoEquation.eqZero_eval] at hout
    exact ((StraightLineProgram.ofCode_computes p).2 z.1 hz.1).symm.trans hout⟩

theorem exists_degreeTwoExtension (p : IntPolynomialCode n) (y : PolynomialZeroSet p) :
    ∃ z : Fin (n + (StraightLineProgram.ofCode p).k) → ℤ,
      Solves z (degreeTwoSystem p) ∧
      ∀ i : Fin n, z (Fin.castAdd _ i) = y.1 i := by
  obtain ⟨z, hinput, hgates, hout⟩ := (StraightLineProgram.ofCode_computes p).1 y.1
  refine ⟨z, ?_, hinput⟩
  unfold degreeTwoSystem
  rw [solves_append]
  refine ⟨hgates, fun F hF => ?_⟩
  rw [List.mem_singleton] at hF
  subst F
  rw [DegreeTwoEquation.eqZero_eval, hout, y.2]

theorem degreeTwoInput_injective (p : IntPolynomialCode n) :
    Function.Injective (degreeTwoInput p) := by
  intro z z' h
  apply Subtype.ext
  apply degreeTwoSystem_determines p z.1 z'.1 z.2 z'.2
  have hval := congrArg Subtype.val h
  exact fun i => congrFun hval i

theorem degreeTwoInput_surjective (p : IntPolynomialCode n) :
    Function.Surjective (degreeTwoInput p) := by
  intro y
  obtain ⟨z, hz, hinput⟩ := exists_degreeTwoExtension p y
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  funext i
  exact hinput i

/-- The right bijection `X ≃ Y` of Remark 4.7.  Its forward map is projection to the
original input coordinates. -/
noncomputable def degreeTwoSolutionsEquivZeros (p : IntPolynomialCode n) :
    DegreeTwoSolutionSet p ≃ PolynomialZeroSet p :=
  Equiv.ofBijective (degreeTwoInput p)
    ⟨degreeTwoInput_injective p, degreeTwoInput_surjective p⟩

@[simp] theorem degreeTwoSolutionsEquivZeros_apply (p : IntPolynomialCode n)
    (z : DegreeTwoSolutionSet p) :
    degreeTwoSolutionsEquivZeros p z = degreeTwoInput p z :=
  rfl

/-- The coordinate of the guarded exponent vector corresponding to the input variable
`y_i` of `p`. -/
def reductionInputCoordinate (p : IntPolynomialCode n) (i : Fin n) : Fin (numVars p) :=
  ⟨i, by
    have := i.isLt
    simp only [numVars]
    omega⟩

/-- Coordinate tracking through the chain of Remark 4.7: the input coordinate of the
image in `Y` is the corresponding exponent coordinate of the normalized `τ_d`. -/
theorem geometry_input_coordinate (p : IntPolynomialCode n)
    (d : NormalizedTauTrinomials p) (i : Fin n) :
    (degreeTwoSolutionsEquivZeros p
      (guardProjection (degreeTwoSystem p) (normalizedTauEquivGuarded p d))).1 i =
      d.1 (reductionInputCoordinate p i) := by
  rw [degreeTwoSolutionsEquivZeros_apply]
  change d.1 (Fin.castAdd 6 (Fin.castAdd (StraightLineProgram.ofCode p).k i)) =
    d.1 (reductionInputCoordinate p i)
  exact congrArg d.1 (Fin.ext rfl)

/-- A prescribed input value occurs on a zero of `P` exactly when it occurs in the
corresponding exponent coordinate of a normalized trinomial in `J_P`. -/
theorem exists_normalizedTau_input_iff (p : IntPolynomialCode n) (i : Fin n) (a : ℤ) :
    (∃ d : NormalizedTauTrinomials p, d.1 (reductionInputCoordinate p i) = a) ↔
      ∃ y : PolynomialZeroSet p, y.1 i = a := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨degreeTwoSolutionsEquivZeros p
      (guardProjection (degreeTwoSystem p) (normalizedTauEquivGuarded p d)), ?_⟩
    rw [geometry_input_coordinate, hd]
  · rintro ⟨y, hy⟩
    let z : DegreeTwoSolutionSet p := (degreeTwoSolutionsEquivZeros p).symm y
    let w : GuardedSolutionSet p := guardSolutionSection (degreeTwoSystem p) z
    let d : NormalizedTauTrinomials p := (normalizedTauEquivGuarded p).symm w
    refine ⟨d, ?_⟩
    have hzy : degreeTwoInput p z = y := by
      exact (degreeTwoSolutionsEquivZeros p).apply_symm_apply y
    have hzy' := congrArg Subtype.val hzy
    have hcoord : z.1 (Fin.castAdd (StraightLineProgram.ofCode p).k i) = y.1 i :=
      congrFun hzy' i
    calc
      d.1 (reductionInputCoordinate p i) =
          w.1 (reductionInputCoordinate p i) := rfl
      _ = w.1 (Fin.castAdd 6 (Fin.castAdd (StraightLineProgram.ofCode p).k i)) :=
        congrArg w.1 (Fin.ext rfl)
      _ = z.1 (Fin.castAdd (StraightLineProgram.ofCode p).k i) :=
        guardSection_castAdd z.1 _
      _ = y.1 i := hcoord
      _ = a := hy

end Trinomial
