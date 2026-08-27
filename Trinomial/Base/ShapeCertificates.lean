import Trinomial.Base.ShapeCert.Cert1
import Trinomial.Base.ShapeCert.Cert2
import Trinomial.Base.ShapeCert.Cert3
import Trinomial.Base.ShapeCert.Cert4
import Trinomial.Base.ShapeCert.Cert5
import Trinomial.Base.ShapeCert.Cert6

/-!
# Certificates for the trinomial classification (Proposition 2.4 (ii), Case 2)

**Auto-generated** by `certificates/gen_lean_certificates.py` from the Macaulay2
computation `certificates/shape_certificates_v3.m2`; do not edit by hand.

The paper's proof of Proposition 2.4 decomposes the saturation of the ideal of the
equations `(k=0) … (k=4)` at `λ₁λ₂` into two primes.  The per-file lemmas
`ShapeCert.cert1 … cert6` witness the containment corresponding to the affine prime
`P₂`: with `u* = r₁²+s₁²+r₂²+s₂²` (nonzero exactly in Case 2), each generator `v` of
the elimination ideal `P₂ ∩ ℚ[r₁,s₁,r₂,s₂]` satisfies an identity

  `u*^k · v · (λ₁λ₂)^m = Σᵢ hᵢ·gᵢ`

with explicit cofactors `hᵢ` (verified by `linear_combination`), so `v` vanishes on
every solution with `λ₁λ₂ ≠ 0 ≠ u*`.  The wrapper `elimination_of_ne_zero` packages
this for the classification proof.
-/

set_option autoImplicit false

namespace Trinomial.ShapeCert

/-- The five defining equations, as hypotheses shared by all certificates. -/
def eqs (l1 l2 r1 s1 r2 s2 : ℚ) : Prop :=
  l1 + l2 - 1 = 0 ∧
  l1*r1 + l2*r2 = 0 ∧
  l1*(r1^2 - s1) + l2*(r2^2 - s2) = 0 ∧
  l1*r1*(r1^2 - 3*s1 + 2) + l2*r2*(r2^2 - 3*s2 + 2) = 0 ∧
  l1*(r1^4 - 6*r1^2*s1 + 8*r1^2 + 3*s1^2 - 6*s1)
    + l2*(r2^4 - 6*r2^2*s2 + 8*r2^2 + 3*s2^2 - 6*s2) = 0

/-- Cancel the two nonzero saturation factors surrounding an elimination polynomial. -/
theorem middle_eq_zero_of_mul_eq_zero {a b c : ℚ}
    (ha : a ≠ 0) (hc : c ≠ 0) (habc : a * b * c = 0) : b = 0 := by
  have hab : a * b = 0 := (mul_eq_zero.mp habc).resolve_right hc
  exact (mul_eq_zero.mp hab).resolve_left ha

/-- **Case-2 elimination**: on a solution of the equations with `λ₁λ₂ ≠ 0` on which
not all of `r₁, s₁, r₂, s₂` vanish, the six generators of the elimination ideal of the
affine prime `P₂` vanish  [proof of Proposition 2.4, Case 2]. -/
theorem elimination_of_ne_zero (l1 l2 r1 s1 r2 s2 : ℚ) (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hne : ¬(r1 = 0 ∧ s1 = 0 ∧ r2 = 0 ∧ s2 = 0)) (h : eqs l1 l2 r1 s1 r2 s2) :
    r2^2+2*s1-s2-2 = 0 ∧
    s1*r2+r1*s2-r2*s2+r2 = 0 ∧
    r1*r2+s1+s2-1 = 0 ∧
    s1^2-s1*s2+s2^2-1 = 0 ∧
    r1*s1-r2*s2-r1+r2 = 0 ∧
    r1^2-s1+2*s2-2 = 0 := by
  obtain ⟨g0, g1, g2, g3, g4⟩ := h
  have hu : r1^2 + s1^2 + r2^2 + s2^2 ≠ 0 := by
    intro hzero
    exact hne ⟨by nlinarith [sq_nonneg r1, sq_nonneg s1, sq_nonneg r2, sq_nonneg s2],
      by nlinarith [sq_nonneg r1, sq_nonneg s1, sq_nonneg r2, sq_nonneg s2],
      by nlinarith [sq_nonneg r1, sq_nonneg s1, sq_nonneg r2, sq_nonneg s2],
      by nlinarith [sq_nonneg r1, sq_nonneg s1, sq_nonneg r2, sq_nonneg s2]⟩
  have hll : l1 * l2 ≠ 0 := mul_ne_zero hl1 hl2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert1 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert2 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert3 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert4 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert5 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)
  · exact middle_eq_zero_of_mul_eq_zero (pow_ne_zero _ hu) (pow_ne_zero _ hll)
      (cert6 l1 l2 r1 s1 r2 s2 g0 g1 g2 g3 g4)

end Trinomial.ShapeCert
