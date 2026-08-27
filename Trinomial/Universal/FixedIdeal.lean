import Trinomial.Encoding.Geometry
import Trinomial.Universal.HaltingFamily

/-!
# The fixed-ideal observation

This module formalizes the fixed Laurent ideal of [§5].  For an effective
Diophantine relation `R` in the parameter `E`, `universalEquationCode R` is the single
sum-of-squares equation with `E` left free.  Applying Theorem 4.5 once gives
`fixedLaurentIdeal R`.  The fiber in which the exponent coordinate `d_E` equals `e`
contains a normalized trinomial exactly when `R(e)` holds.  For `MRDP.haltingRel`, these
fibers encode the halting set.
-/

set_option autoImplicit false

namespace Trinomial

open Nat.Partrec (Code)
open TrinomialUndecidability.Computability (EffDiophRel Satisfies evalPolynomial)
open TrinomialUndecidability.Computability.EffDiophRel
  (sumSquares eval_sumSquares_eq_zero_iff_satisfies)
open TrinomialUndecidability.Computability.HaltingEvalnBridge (HaltsAtZero)

/-- The single equation `Σ_j R_j(E,Y)^2 = 0`, with the parameter `E` left free. -/
def universalEquationCode (R : EffDiophRel 1) := sumSquares R.eqs

/-- The fixed Laurent ideal `J_U` obtained by applying Theorem 4.5 once to the universal
equation with `E` unspecialized. -/
noncomputable def fixedLaurentIdeal (R : EffDiophRel 1) :
    Ideal (Laurent (numVars (universalEquationCode R))) :=
  reductionIdeal (quadraticForms (universalEquationCode R))

/-- The exponent coordinate `d_E` corresponding to the free parameter `E`. -/
def fixedParameterCoordinate (R : EffDiophRel 1) :
    Fin (numVars (universalEquationCode R)) :=
  reductionInputCoordinate (universalEquationCode R) 0

theorem eval_universalEquationCode_zero_iff (R : EffDiophRel 1)
    (x : Fin (1 + R.aux) → ℤ) :
    evalPolynomial (universalEquationCode R) x = 0 ↔ Satisfies R.eqs x :=
  eval_sumSquares_eq_zero_iff_satisfies R.eqs x

/-- Zeros of the unspecialized universal equation in the fiber `E = e` are precisely the
witnesses that `R(e)` holds. -/
theorem exists_universalEquation_zero_with_parameter_iff (R : EffDiophRel 1) (e : ℤ) :
    (∃ y : PolynomialZeroSet (universalEquationCode R), y.1 0 = e) ↔
      R.Realizes (fun _ => e) := by
  constructor
  · rintro ⟨y, hyE⟩
    have hsat : Satisfies R.eqs y.1 :=
      (eval_universalEquationCode_zero_iff R y.1).mp y.2
    let aux : Fin R.aux → ℤ := fun j => y.1 (Fin.natAdd 1 j)
    refine ⟨aux, ?_⟩
    have happ : Fin.append (fun _ : Fin 1 => e) aux = y.1 := by
      funext i
      induction i using Fin.addCases with
      | left j =>
          rw [Fin.append_left]
          have hj : j = 0 := Fin.eq_zero j
          subst j
          simpa using hyE.symm
      | right j => rw [Fin.append_right]
    rw [happ]
    exact hsat
  · rintro ⟨aux, hsat⟩
    let x : Fin (1 + R.aux) → ℤ := Fin.append (fun _ : Fin 1 => e) aux
    refine ⟨⟨x, (eval_universalEquationCode_zero_iff R x).mpr hsat⟩, ?_⟩
    have h0 : (0 : Fin (1 + R.aux)) = Fin.castAdd R.aux (0 : Fin 1) := Fin.ext rfl
    change x 0 = e
    rw [h0]
    simp [x]

/-- The fixed-ideal fiber statement for any effective Diophantine relation. -/
theorem fixedLaurentIdeal_fiber_iff (R : EffDiophRel 1) (e : ℤ) :
    (∃ d : NormalizedTauTrinomials (universalEquationCode R),
      d.1 (fixedParameterCoordinate R) = e) ↔ R.Realizes (fun _ => e) := by
  rw [fixedParameterCoordinate, exists_normalizedTau_input_iff]
  exact exists_universalEquation_zero_with_parameter_iff R e

/-- The fixed-ideal fiber statement written directly in terms of membership of `τ_d` in
the one Laurent ideal `fixedLaurentIdeal R`. -/
theorem fixedLaurentIdeal_tau_fiber_iff (R : EffDiophRel 1) (e : ℤ) :
    (∃ d : Fin (numVars (universalEquationCode R)) → ℤ,
      tau d ∈ fixedLaurentIdeal R ∧ d (fixedParameterCoordinate R) = e) ↔
      R.Realizes (fun _ => e) := by
  constructor
  · rintro ⟨d, hd, hcoord⟩
    apply (fixedLaurentIdeal_fiber_iff R e).mp
    exact ⟨⟨d, by simpa only [fixedLaurentIdeal] using hd⟩, hcoord⟩
  · intro h
    obtain ⟨d, hcoord⟩ := (fixedLaurentIdeal_fiber_iff R e).mpr h
    exact ⟨d.1, by simpa only [fixedLaurentIdeal] using d.2, hcoord⟩

/-- Specializing the exponent fiber at `e` recovers the trinomial-existence predicate for
the ideal `I_e` of the universal family. -/
theorem fixedLaurentIdeal_fiber_iff_ideal_has_trinomial (R : EffDiophRel 1) (e : ℕ) :
    (∃ d : NormalizedTauTrinomials (universalEquationCode R),
      d.1 (fixedParameterCoordinate R) = (e : ℤ)) ↔
      HasShortPoly 3 (Universal.ideal R e) :=
  (fixedLaurentIdeal_fiber_iff R e).trans (Universal.hasShortPoly_three_iff R e).symm

/-- The fixed Laurent ideal whose exponent fibers encode the halting set. -/
noncomputable def fixedHaltingLaurentIdeal :
    Ideal (Laurent (numVars (universalEquationCode MRDP.haltingRel))) :=
  fixedLaurentIdeal MRDP.haltingRel

/-- The parameter exponent coordinate in `fixedHaltingLaurentIdeal`. -/
noncomputable def fixedHaltingParameterCoordinate :
    Fin (numVars (universalEquationCode MRDP.haltingRel)) :=
  fixedParameterCoordinate MRDP.haltingRel

/-- **A fixed ideal.**  The fiber `d_E = e` of normalized trinomials in one fixed Laurent
ideal is nonempty exactly when the `e`-th machine halts on input zero. -/
theorem fixedHaltingLaurentIdeal_fiber_iff (e : ℕ) :
    (∃ d : NormalizedTauTrinomials (universalEquationCode MRDP.haltingRel),
      d.1 fixedHaltingParameterCoordinate = (e : ℤ)) ↔
      HaltsAtZero (Denumerable.ofNat Code e) := by
  rw [fixedHaltingParameterCoordinate, fixedLaurentIdeal_fiber_iff]
  exact MRDP.haltingRel_spec e

/-- **A fixed ideal.**  Written without the normalized-trinomial subtype, the condition is
`τ_d ∈ J_U` together with the single exponent constraint `d_E = e`. -/
theorem fixedHaltingLaurentIdeal_tau_fiber_iff (e : ℕ) :
    (∃ d : Fin (numVars (universalEquationCode MRDP.haltingRel)) → ℤ,
      tau d ∈ fixedHaltingLaurentIdeal ∧
        d fixedHaltingParameterCoordinate = (e : ℤ)) ↔
      HaltsAtZero (Denumerable.ofNat Code e) := by
  rw [fixedHaltingLaurentIdeal, fixedHaltingParameterCoordinate,
    fixedLaurentIdeal_tau_fiber_iff]
  exact MRDP.haltingRel_spec e

end Trinomial
