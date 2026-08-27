import Trinomial.Base.Trinomials
import Trinomial.Quadrics.QuadraticAlgebra
import Trinomial.Base.RatAlgebra

/-!
# The homomorphism `φ_Q` and Proposition 3.5

[§3].  For a quadratic form `Q` on `V = ℚ^N × ℚ v₀` (represented by a symmetric
matrix `(b_ij)` of the bilinear form on the index type `Option (Fin N)`, where `some i ↦ vᵢ` and `none ↦ v₀`),
the ring homomorphism `φ_Q : L_N → A_Q` is defined on the variables by

  `S ↦ ½ Exp(v₀)`, `T ↦ ½ Exp(−v₀)`, `Dᵢ ↦ Exp(vᵢ)`,

so that on a general monomial `φ_Q(S^a T^b D^d) = 2^{−a−b} Exp(d + (a−b) v₀)`.
Formally we *define* `φ_Q` by the monomial formula (which is manifestly multiplicative)
and *prove* the variable images as `phi_S`, `phi_T`, `phi_D`.

Proposition 3.5 becomes:

* `phi_tau`:   `φ_Q(τ_d) = −½ Q(d,1) ζ`
* `phi_theta`: `φ_Q(θ_e^{p,q}) = ½ pq(p−q) Q(e,0) ζ`

with the membership criteria `tau_mem_ker_phi_iff` and `theta_mem_ker_phi_iff`.
The quadrinomial `Ω` lies in every kernel: `Omega_mem_ker_phi`.
-/

set_option autoImplicit false

namespace Trinomial

variable {N : ℕ}

/-- The vector `(d, t) ∈ V = ℚ^N × ℚ v₀`: value `d i` on the direction of `Dᵢ` and `t` on
the homogenization coordinate `v₀`. -/
def homVec (d : Fin N → ℚ) (t : ℚ) : Option (Fin N) → ℚ := fun o => o.elim t d

@[simp] lemma homVec_none (d : Fin N → ℚ) (t : ℚ) : homVec d t none = t := rfl
@[simp] lemma homVec_some (d : Fin N → ℚ) (t : ℚ) (i : Fin N) :
    homVec d t (some i) = d i := rfl

lemma homVec_add (d d' : Fin N → ℚ) (t t' : ℚ) :
    homVec d t + homVec d' t' = homVec (d + d') (t + t') := by
  funext o; cases o <;> rfl

lemma homVec_neg (d : Fin N → ℚ) (t : ℚ) : -homVec d t = homVec (-d) (-t) := by
  funext o; cases o <;> rfl

lemma homVec_smul (c : ℚ) (d : Fin N → ℚ) (t : ℚ) :
    c • homVec d t = homVec (c • d) (c * t) := by
  funext o; cases o <;> rfl

@[simp] lemma homVec_zero : homVec (0 : Fin N → ℚ) 0 = 0 := by
  funext o; cases o <;> rfl

/-- The rational-cast image of an integer vector. -/
def ratCast (d : Fin N → ℤ) : Fin N → ℚ := fun i => (d i : ℚ)

@[simp] lemma ratCast_apply (d : Fin N → ℤ) (i : Fin N) : ratCast d i = (d i : ℚ) := rfl

@[simp] lemma ratCast_zero : ratCast (0 : Fin N → ℤ) = 0 := by
  funext i; simp [ratCast]

lemma ratCast_add (d d' : Fin N → ℤ) : ratCast (d + d') = ratCast d + ratCast d' := by
  funext i; simp [ratCast]

lemma ratCast_neg (d : Fin N → ℤ) : ratCast (-d) = -ratCast d := by
  funext i; simp [ratCast]

lemma ratCast_zsmul (p : ℤ) (d : Fin N → ℤ) : ratCast (p • d) = (p : ℚ) • ratCast d := by
  funext i; simp [ratCast]

variable (G : BilinearFormMatrix (Option (Fin N)))

/-- The value `Q(d, t)` of the quadratic form at the (rational) point `(d, t)`. -/
def quadAt (d : Fin N → ℚ) (t : ℚ) : ℚ := G.quad (homVec d t)

/-- The homogenized exponent vector of a Laurent monomial: `S^a T^b D^d` contributes the
point `d + (a−b) v₀`  [proof of Proposition 3.5]. -/
def expVec (x : Exponent N) : Option (Fin N) → ℚ := homVec (ratCast x.d) ((x.s : ℚ) - x.t)

/-- The image of the monomial with exponent `x` under `φ_Q`, as a unit:
`2^{−(a+b)} Exp(d + (a−b) v₀)`. -/
noncomputable def phiMonoUnit (x : Exponent N) : (CubeAlgebra G)ˣ :=
  (twoUnit (CubeAlgebra G))⁻¹ ^ (x.s + x.t) * CubeAlgebra.expUnit G (expVec x)

theorem expVec_zero : expVec (0 : Exponent N) = 0 := by
  funext o; cases o <;> simp [expVec]

theorem phiMonoUnit_zero : phiMonoUnit G 0 = 1 := by
  rw [phiMonoUnit, expVec_zero]
  simp only [Exponent.zero_s, Exponent.zero_t, add_zero, zpow_zero, one_mul]
  exact CubeAlgebra.expUnit_zero

theorem expVec_add (x y : Exponent N) : expVec (x + y) = expVec x + expVec y := by
  rw [expVec, expVec, expVec, homVec_add]
  congr 1
  · rw [Exponent.add_d, ratCast_add]
  · rw [Exponent.add_s, Exponent.add_t]
    push_cast
    ring

theorem phiMonoUnit_add (x y : Exponent N) :
    phiMonoUnit G (x + y) = phiMonoUnit G x * phiMonoUnit G y := by
  rw [phiMonoUnit, phiMonoUnit, phiMonoUnit, expVec_add, CubeAlgebra.expUnit_add,
    Exponent.add_s, Exponent.add_t,
    show x.s + y.s + (x.t + y.t) = (x.s + x.t) + (y.s + y.t) by ring, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

/-- `φ_Q : L_N → A_Q` as a `ℚ`-algebra homomorphism, defined on monomials by
`S^a T^b D^d ↦ 2^{−a−b} Exp(d + (a−b) v₀)`. -/
noncomputable def phi : Laurent N →ₐ[ℚ] CubeAlgebra G :=
  AddMonoidAlgebra.lift ℚ (CubeAlgebra G) (Exponent N)
    { toFun := fun x => (phiMonoUnit G (Multiplicative.toAdd x) : CubeAlgebra G)
      map_one' := by
        rw [show Multiplicative.toAdd (1 : Multiplicative (Exponent N)) = 0 from rfl,
          phiMonoUnit_zero]
        rfl
      map_mul' := fun x y => by
        rw [show Multiplicative.toAdd (x * y) =
          Multiplicative.toAdd x + Multiplicative.toAdd y from rfl, phiMonoUnit_add]
        rfl }

theorem phi_single (x : Exponent N) (c : ℚ) :
    phi G (AddMonoidAlgebra.single x c) = c • (phiMonoUnit G x : CubeAlgebra G) := by
  rw [phi, AddMonoidAlgebra.lift_single]
  rfl

/-- The image of a monomial, in closed form: `2^{−(a+b)} • Exp(d + (a−b)v₀)`
[first display in the proof of Proposition 3.5]. -/
theorem phi_mono (x : Exponent N) :
    phi G (mono x) = ((1 / 2 : ℚ) ^ (x.s + x.t) : ℚ) • CubeAlgebra.exp G (expVec x) := by
  rw [mono, phi_single, one_smul, phiMonoUnit, Units.val_mul, twoUnit_inv_zpow_val,
    CubeAlgebra.expUnit_val, Algebra.smul_def]

/-- The paper's defining image of `S` under `φ_Q`:  `S ↦ ½ Exp(v₀)`. -/
theorem phi_S : phi G (S N) = (1 / 2 : ℚ) • CubeAlgebra.exp G (homVec 0 1) := by
  have h : expVec (Exponent.gS : Exponent N) = homVec 0 1 := by
    funext o; cases o <;> simp [expVec, Exponent.gS]
  rw [S, phi_mono, h, show (Exponent.gS : Exponent N).s + Exponent.gS.t = 1 from rfl,
    zpow_one]

/-- `T ↦ ½ Exp(−v₀)`. -/
theorem phi_T : phi G (T N) = (1 / 2 : ℚ) • CubeAlgebra.exp G (homVec 0 (-1)) := by
  have h : expVec (Exponent.gT : Exponent N) = homVec 0 (-1) := by
    funext o; cases o <;> simp [expVec, Exponent.gT]
  rw [T, phi_mono, h, show (Exponent.gT : Exponent N).s + Exponent.gT.t = 1 from rfl,
    zpow_one]

/-- `Dᵢ ↦ Exp(vᵢ)`. -/
theorem phi_D (i : Fin N) :
    phi G (D i) = CubeAlgebra.exp G (homVec (Pi.single i 1) 0) := by
  have h : expVec (Exponent.gD i : Exponent N) = homVec (Pi.single i 1) 0 := by
    funext o
    cases o with
    | none => simp [expVec, Exponent.gD]
    | some j =>
        simp [expVec, Exponent.gD, ratCast, Pi.single_apply, apply_ite (Int.cast : ℤ → ℚ)]
  rw [D, phi_mono, h,
    show (Exponent.gD i : Exponent N).s + (Exponent.gD i).t = 0 from rfl, zpow_zero,
    one_smul]

/-! ### Proposition 3.5 -/

/-- `φ_Q(τ_d) = −½ Q(d, 1) ζ`  [Proposition 3.5, affine case]. -/
theorem phi_tau (d : Fin N → ℤ) :
    phi G (tau d) = (-(quadAt G (ratCast d) 1 / 2)) • CubeAlgebra.zeta G := by
  have h1 : phi G (mono (⟨1, 0, d⟩ : Exponent N)) =
      (1 / 2 : ℚ) • CubeAlgebra.exp G (homVec (ratCast d) 1) := by
    have h : expVec (⟨1, 0, d⟩ : Exponent N) = homVec (ratCast d) 1 := by
      funext o; cases o <;> simp [expVec]
    rw [phi_mono, h, show (⟨1, 0, d⟩ : Exponent N).s + (⟨1, 0, d⟩ : Exponent N).t = 1
      from rfl, zpow_one]
  have h2 : phi G (mono (⟨0, 1, -d⟩ : Exponent N)) =
      (1 / 2 : ℚ) • CubeAlgebra.exp G (-homVec (ratCast d) 1) := by
    have h : expVec (⟨0, 1, -d⟩ : Exponent N) = -homVec (ratCast d) 1 := by
      rw [homVec_neg]
      funext o; cases o <;> simp [expVec, ratCast]
    rw [phi_mono, h, show (⟨0, 1, -d⟩ : Exponent N).s + (⟨0, 1, -d⟩ : Exponent N).t = 1
      from rfl, zpow_one]
  have hquad : G.quad (-homVec (ratCast d) 1) = quadAt G (ratCast d) 1 := G.quad_neg _
  rw [tau, map_sub, map_sub, map_one, h1, h2]
  ext <;> simp [sub_eq_add_neg, hquad, quadAt] <;> try ring

/-- `τ_d ∈ ker φ_Q ⟺ Q(d, 1) = 0`  [Proposition 3.5]. -/
theorem tau_mem_ker_phi_iff (d : Fin N → ℤ) :
    tau d ∈ RingHom.ker (phi G) ↔ quadAt G (ratCast d) 1 = 0 := by
  rw [RingHom.mem_ker, phi_tau, CubeAlgebra.smul_zeta_eq_zero_iff, neg_eq_zero,
    div_eq_zero_iff]
  simp

/-- `φ_Q(θ_e^{p,q}) = ½ pq(p−q) Q(e, 0) ζ`  [Proposition 3.5, infinite case].
The formula holds for all `e, p, q`; no primitivity is needed. -/
theorem phi_theta (e : Fin N → ℤ) (p q : ℤ) :
    phi G (theta e p q) =
      ((p * q * (p - q) : ℚ) * quadAt G (ratCast e) 0 / 2) • CubeAlgebra.zeta G := by
  have key : ∀ r : ℤ, phi G (mono (⟨0, 0, r • e⟩ : Exponent N)) =
      CubeAlgebra.exp G ((r : ℚ) • homVec (ratCast e) 0) := by
    intro r
    have h : expVec (⟨0, 0, r • e⟩ : Exponent N) = (r : ℚ) • homVec (ratCast e) 0 := by
      rw [homVec_smul]
      funext o; cases o <;> simp [expVec, ratCast]
    rw [phi_mono, h,
      show ((⟨0, 0, r • e⟩ : Exponent N).s + (⟨0, 0, r • e⟩ : Exponent N).t) = 0 from rfl,
      zpow_zero, one_smul]
  have hp2 : G.quad ((p : ℚ) • homVec (ratCast e) 0) =
      (p : ℚ) ^ 2 * quadAt G (ratCast e) 0 := G.quad_smul _ _
  have hq2 : G.quad ((q : ℚ) • homVec (ratCast e) 0) =
      (q : ℚ) ^ 2 * quadAt G (ratCast e) 0 := G.quad_smul _ _
  rw [theta, map_sub, map_add, map_smul, map_smul, map_smul, map_one, key p, key q]
  ext <;> simp [sub_eq_add_neg, hp2, hq2, quadAt] <;> try ring

/-- `θ_e^{p,q} ∈ ker φ_Q ⟺ Q(e, 0) = 0` (for `p, q` distinct and nonzero)
[Proposition 3.5]. -/
theorem theta_mem_ker_phi_iff (e : Fin N → ℤ) {p q : ℤ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    theta e p q ∈ RingHom.ker (phi G) ↔ quadAt G (ratCast e) 0 = 0 := by
  rw [RingHom.mem_ker, phi_theta, CubeAlgebra.smul_zeta_eq_zero_iff, div_eq_zero_iff,
    mul_eq_zero]
  have hne : (p : ℚ) * q * ((p : ℚ) - q) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (sub_ne_zero.mpr ?_)
    · exact_mod_cast hp
    · exact_mod_cast hq
    · exact_mod_cast hpq
  simp [hne]

/-- The quadrinomial `Ω = (S+T−1)(S−T)` lies in the kernel of every `φ_Q`
[proof of Theorem 4.5]. -/
theorem Omega_mem_ker_phi : Omega N ∈ RingHom.ker (phi G) := by
  rw [RingHom.mem_ker, Omega, map_mul]
  have hV : homVec (0 : Fin N → ℚ) (-1) = -homVec 0 1 := by
    rw [homVec_neg, neg_zero]
  have h1 : phi G (S N + T N - 1) = (quadAt G 0 1 / 2) • CubeAlgebra.zeta G := by
    rw [map_sub, map_add, map_one, phi_S, phi_T, hV]
    ext <;> simp [sub_eq_add_neg, quadAt] <;> try ring
  have h2 : (phi G (S N) - phi G (T N)).scalar = 0 := by
    rw [phi_S, phi_T]
    simp [sub_eq_add_neg]
  rw [h1]
  ext <;> simp [h2]

end Trinomial
