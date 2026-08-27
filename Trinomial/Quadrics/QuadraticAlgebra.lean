import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# The cube-zero algebra `A_B` attached to a quadratic form

This module formalizes the local algebra of [§3]:
for a symmetric bilinear form `B : V × V → ℚ`, the algebra
`A_B = ℚ ⊕ V ⊕ ℚζ` with coordinatewise addition and multiplication

  `(r, v, s) · (r', v', s') = (r r', r v' + r' v, r s' + r' s + B(v, v'))`.

Its nilradical `V ⊕ ℚζ` cubes to zero, and the truncated exponential
`Exp(x) = 1 + x + ½ Q(x) ζ` (with `Q(x) = B(x,x)`) is multiplicative:
`Exp(v)·Exp(v') = Exp(v+v')`, `Exp(-v) = Exp(v)⁻¹`.

We represent `V = ℚ^ι` for a finite index type `ι` and the bilinear form by its symmetric
matrix `(b_ij) = (B(vᵢ, vⱼ))` with respect to the standard basis (`BilinearFormMatrix ι`;
`polar_eq_toBilin'` and `quad_eq_toQuadraticMap` identify `B` and `Q` with mathlib's
`Matrix.toBilin'` and `LinearMap.BilinMap.toQuadraticMap`).  In
`Trinomial/Quadrics/KernelEvaluation.lean` the index is specialized to `ι = Option (Fin N)`:
`some i ↦ vᵢ` and `none ↦ v₀`, the homogenization coordinate.

Paper correspondence:

* Definition 3.1 of `A_B`                       ↦ `Trinomial.CubeAlgebra B`
* the products `v·v' = B(v,v')ζ`, `ζ² = 0`  ↦ `ofVector_mul_ofVector`, `zeta_sq`;
  `cube_zero` (products of three nilpotents vanish) is the computation behind `𝔫³ = 0`
* `Exp(v) = 1 + v + ½Q(v)ζ` and its laws     ↦ `CubeAlgebra.exp`, `exp_mul_exp`, `exp_mul_exp_neg`

The structure statements of Lemma 3.2 (local, nilradical, `Exp`/`Log` on all of `𝔫`, the
presentation) are in `Trinomial/Quadrics/CubeAlgebraStructure.lean` and
`Trinomial/Quadrics/CubeAlgebraPresentation.lean`.
-/

set_option autoImplicit false

namespace Trinomial

open scoped BigOperators

variable {ι : Type*}

/-- The matrix `(b_ij) = (B(vᵢ, vⱼ))` of a symmetric bilinear form `B` on `V = ℚ^ι` with
respect to the standard basis `(vᵢ)`  [§3, Definition 3.1 and Lemma 3.2].
(In standard terminology: a symmetric Gram matrix over `ℚ`.) -/
structure BilinearFormMatrix (ι : Type*) where
  /-- The entries `b_ij = B(vᵢ, vⱼ)`. -/
  b : ι → ι → ℚ
  /-- The matrix is symmetric. -/
  symmetric : ∀ i j, b i j = b j i

namespace BilinearFormMatrix

variable [Fintype ι]

/-- The bilinear form `B(x, y)` represented by the matrix `(b_ij)` of the bilinear form. -/
def polar (B : BilinearFormMatrix ι) : LinearMap.BilinForm ℚ (ι → ℚ) :=
  Matrix.toBilin'Aux (Matrix.of B.b)

/-- The quadratic form `Q(x) = B(x, x)` of the matrix `(b_ij)` of the bilinear form. -/
def quad (B : BilinearFormMatrix ι) : QuadraticMap ℚ (ι → ℚ) ℚ :=
  B.polar.toQuadraticMap

/-- `B(x, y)` is the bilinear form `Matrix.toBilin'` of the matrix `(b_ij)`. -/
theorem polar_eq_toBilin' [DecidableEq ι] (B : BilinearFormMatrix ι) (x y : ι → ℚ) :
    B.polar x y = Matrix.toBilin' (Matrix.of B.b) x y := by
  rw [polar, Matrix.toBilin'Aux_eq]

/-- `Q(x)` is the quadratic map of the bilinear form `Matrix.toBilin'` of `(b_ij)`. -/
theorem quad_eq_toQuadraticMap [DecidableEq ι] (B : BilinearFormMatrix ι) (x : ι → ℚ) :
    B.quad x = (Matrix.toBilin' (Matrix.of B.b)).toQuadraticMap x := by
  rw [quad, polar, Matrix.toBilin'Aux_eq]

@[simp]
theorem polar_zero_left (B : BilinearFormMatrix ι) (x : ι → ℚ) : B.polar 0 x = 0 := by
  simp

@[simp]
theorem polar_zero_right (B : BilinearFormMatrix ι) (x : ι → ℚ) : B.polar x 0 = 0 := by
  simp

theorem polar_add_left (B : BilinearFormMatrix ι) (x y z : ι → ℚ) :
    B.polar (x + y) z = B.polar x z + B.polar y z := by
  simp

theorem polar_add_right (B : BilinearFormMatrix ι) (x y z : ι → ℚ) :
    B.polar x (y + z) = B.polar x y + B.polar x z := by
  simp

theorem polar_smul_left (B : BilinearFormMatrix ι) (c : ℚ) (x y : ι → ℚ) :
    B.polar (c • x) y = c * B.polar x y := by
  simp

theorem polar_smul_right (B : BilinearFormMatrix ι) (c : ℚ) (x y : ι → ℚ) :
    B.polar x (c • y) = c * B.polar x y := by
  simp

theorem polar_neg_left (B : BilinearFormMatrix ι) (x y : ι → ℚ) :
    B.polar (-x) y = -B.polar x y := by
  simp

theorem polar_neg_right (B : BilinearFormMatrix ι) (x y : ι → ℚ) :
    B.polar x (-y) = -B.polar x y := by
  simp

/-- Symmetry of the matrix `(b_ij)` of the bilinear form makes the bilinear form symmetric. -/
theorem polar_comm (B : BilinearFormMatrix ι) (x y : ι → ℚ) : B.polar x y = B.polar y x := by
  classical
  rw [B.polar_eq_toBilin', B.polar_eq_toBilin', Matrix.toBilin'_apply,
    Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    change x j * B.b j i * y i = y i * B.b i j * x j
    rw [B.symmetric j i]; ring

@[simp]
theorem quad_zero (B : BilinearFormMatrix ι) : B.quad 0 = 0 := by simp

@[simp]
theorem quad_neg (B : BilinearFormMatrix ι) (x : ι → ℚ) : B.quad (-x) = B.quad x := by
  simp

/-- The quadratic form is homogeneous of degree two. -/
theorem quad_smul (B : BilinearFormMatrix ι) (c : ℚ) (x : ι → ℚ) :
    B.quad (c • x) = c ^ 2 * B.quad x := by
  simpa [pow_two] using B.quad.map_smul c x

/-- Polarization: `Q(x + y) = Q(x) + 2B(x, y) + Q(y)`. -/
theorem quad_add (B : BilinearFormMatrix ι) (x y : ι → ℚ) :
    B.quad (x + y) = B.quad x + 2 * B.polar x y + B.quad y := by
  simp only [quad, LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  rw [B.polar_comm y x]
  ring

end BilinearFormMatrix

/-- The cube-zero algebra `A_B = ℚ ⊕ V ⊕ ℚζ` attached to a symmetric bilinear form
[§3].  `scalar` is the `ℚ`-coordinate, `vector` the `V`-coordinate, and
`socle` the coefficient of the socle generator `ζ`. -/
@[ext]
structure CubeAlgebra {ι : Type*} (B : BilinearFormMatrix ι) where
  /-- The `ℚ`-coordinate. -/
  scalar : ℚ
  /-- The `V`-coordinate. -/
  vector : ι → ℚ
  /-- The coefficient of the socle generator `ζ`. -/
  socle : ℚ

namespace CubeAlgebra

variable {B : BilinearFormMatrix ι}

instance : Zero (CubeAlgebra B) := ⟨⟨0, 0, 0⟩⟩
instance : One (CubeAlgebra B) := ⟨⟨1, 0, 0⟩⟩
instance : Add (CubeAlgebra B) :=
  ⟨fun x y => ⟨x.scalar + y.scalar, x.vector + y.vector, x.socle + y.socle⟩⟩
instance : Neg (CubeAlgebra B) := ⟨fun x => ⟨-x.scalar, -x.vector, -x.socle⟩⟩

/-- The copy of `V` inside `A_B` (the degree-one layer: a product of two of its elements
is not zero but lands in the socle `ℚζ`, see `ofVector_mul_ofVector`). -/
def ofVector (B : BilinearFormMatrix ι) (x : ι → ℚ) : CubeAlgebra B := ⟨0, x, 0⟩

/-- The socle generator `ζ`. -/
def zeta (B : BilinearFormMatrix ι) : CubeAlgebra B := ⟨0, 0, 1⟩

@[simp] theorem zero_scalar : (0 : CubeAlgebra B).scalar = 0 := rfl
@[simp] theorem zero_vector : (0 : CubeAlgebra B).vector = 0 := rfl
@[simp] theorem zero_socle : (0 : CubeAlgebra B).socle = 0 := rfl
@[simp] theorem one_scalar : (1 : CubeAlgebra B).scalar = 1 := rfl
@[simp] theorem one_vector : (1 : CubeAlgebra B).vector = 0 := rfl
@[simp] theorem one_socle : (1 : CubeAlgebra B).socle = 0 := rfl
@[simp] theorem add_scalar (x y : CubeAlgebra B) :
    (x + y).scalar = x.scalar + y.scalar := rfl
@[simp] theorem add_vector (x y : CubeAlgebra B) :
    (x + y).vector = x.vector + y.vector := rfl
@[simp] theorem add_socle (x y : CubeAlgebra B) :
    (x + y).socle = x.socle + y.socle := rfl
@[simp] theorem neg_scalar (x : CubeAlgebra B) : (-x).scalar = -x.scalar := rfl
@[simp] theorem neg_vector (x : CubeAlgebra B) : (-x).vector = -x.vector := rfl
@[simp] theorem neg_socle (x : CubeAlgebra B) : (-x).socle = -x.socle := rfl
@[simp] theorem ofVector_scalar (x : ι → ℚ) : (ofVector B x).scalar = 0 := rfl
@[simp] theorem ofVector_vector (x : ι → ℚ) : (ofVector B x).vector = x := rfl
@[simp] theorem ofVector_socle (x : ι → ℚ) : (ofVector B x).socle = 0 := rfl
@[simp] theorem zeta_scalar : (zeta B).scalar = 0 := rfl
@[simp] theorem zeta_vector : (zeta B).vector = 0 := rfl
@[simp] theorem zeta_socle : (zeta B).socle = 1 := rfl

/-- The socle generator is nonzero. -/
@[simp] theorem zeta_ne_zero : zeta B ≠ 0 := by
  intro h
  have := congrArg socle h
  norm_num at this

/-! From here on the bilinear form `B` enters, so `ι` must be a `Fintype`. -/

variable [Fintype ι]

/-- Multiplication of `A_B`: the defining formula of the paper. -/
instance : Mul (CubeAlgebra B) :=
  ⟨fun x y =>
    ⟨x.scalar * y.scalar,
      x.scalar • y.vector + y.scalar • x.vector,
      x.scalar * y.socle + y.scalar * x.socle + B.polar x.vector y.vector⟩⟩

@[simp] theorem mul_scalar (x y : CubeAlgebra B) :
    (x * y).scalar = x.scalar * y.scalar := rfl
@[simp] theorem mul_vector (x y : CubeAlgebra B) :
    (x * y).vector = x.scalar • y.vector + y.scalar • x.vector := rfl
@[simp] theorem mul_socle (x y : CubeAlgebra B) :
    (x * y).socle = x.scalar * y.socle + y.scalar * x.socle
      + B.polar x.vector y.vector := rfl

instance : CommRing (CubeAlgebra B) :=
  CommRing.ofMinimalAxioms
    (fun x y z => by ext <;> simp [add_assoc])
    (fun x => by ext <;> simp)
    (fun x => by ext <;> simp)
    (fun x y z => by
      ext
      · simp [mul_assoc]
      · simp only [mul_vector, mul_scalar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [mul_socle, mul_scalar, mul_vector]
        rw [B.polar_add_left, B.polar_smul_left, B.polar_smul_left,
          B.polar_add_right, B.polar_smul_right, B.polar_smul_right]
        ring)
    (fun x y => by
      ext
      · simp [mul_comm]
      · simp only [mul_vector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [mul_socle]
        rw [B.polar_comm y.vector x.vector]
        ring)
    (fun x => by ext <;> simp)
    (fun x y z => by
      ext
      · simp [mul_add]
      · simp only [mul_vector, add_scalar, add_vector, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      · simp only [mul_socle, add_scalar, add_vector, add_socle]
        rw [B.polar_add_right]
        ring)

/-- The embedding of `ℚ` as the scalar part of `A_B`. -/
def scalarRingHom (B : BilinearFormMatrix ι) : ℚ →+* CubeAlgebra B where
  toFun c := ⟨c, 0, 0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp [BilinearFormMatrix.polar]

instance : Algebra ℚ (CubeAlgebra B) := (scalarRingHom B).toAlgebra

@[simp] theorem algebraMap_scalar (c : ℚ) :
    (algebraMap ℚ (CubeAlgebra B) c).scalar = c := rfl
@[simp] theorem algebraMap_vector (c : ℚ) :
    (algebraMap ℚ (CubeAlgebra B) c).vector = 0 := rfl
@[simp] theorem algebraMap_socle (c : ℚ) :
    (algebraMap ℚ (CubeAlgebra B) c).socle = 0 := rfl

@[simp] theorem smul_scalar (c : ℚ) (x : CubeAlgebra B) :
    (c • x).scalar = c * x.scalar := by
  rw [Algebra.smul_def]; simp

@[simp] theorem smul_vector (c : ℚ) (x : CubeAlgebra B) :
    (c • x).vector = c • x.vector := by
  rw [Algebra.smul_def]; ext i; simp

@[simp] theorem smul_socle (c : ℚ) (x : CubeAlgebra B) :
    (c • x).socle = c * x.socle := by
  rw [Algebra.smul_def]; simp [BilinearFormMatrix.polar]

/-- `c • ζ` vanishes exactly when `c` does; this is how kernel membership reads off the
value of the quadratic form in Proposition 3.5.  (Not a `simp` lemma: `simp`
normalizes the left-hand side by `smul_eq_zero` and then discharges `ζ ≠ 0`.) -/
theorem smul_zeta_eq_zero_iff (c : ℚ) : c • zeta B = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg socle h
    simpa using this
  · rintro rfl
    simp

@[simp] theorem zeta_sq : zeta B * zeta B = 0 := by
  ext <;> simp [BilinearFormMatrix.polar]

/-- Products of tangent vectors land on the socle line via the bilinear form:
`v · v' = B(v, v') ζ`  [Lemma 3.2]. -/
theorem ofVector_mul_ofVector (x y : ι → ℚ) :
    ofVector B x * ofVector B y = B.polar x y • zeta B := by
  ext <;> simp

/-- The nilradical `V ⊕ ℚζ` of `A_B` cubes to zero: `A_B` is a "radical cube zero" ring. -/
theorem cube_zero (x y z : CubeAlgebra B) (hx : x.scalar = 0) (hy : y.scalar = 0)
    (hz : z.scalar = 0) : x * y * z = 0 := by
  ext <;> simp [hx, hy, hz, BilinearFormMatrix.polar]

/-- The truncated exponential `Exp(x) = 1 + x + ½ Q(x) ζ`  [§3]. -/
def exp (B : BilinearFormMatrix ι) (x : ι → ℚ) : CubeAlgebra B := ⟨1, x, B.quad x / 2⟩

@[simp] theorem exp_scalar (x : ι → ℚ) : (exp B x).scalar = 1 := rfl
@[simp] theorem exp_vector (x : ι → ℚ) : (exp B x).vector = x := rfl
@[simp] theorem exp_socle (x : ι → ℚ) : (exp B x).socle = B.quad x / 2 := rfl

@[simp] theorem exp_zero : exp B 0 = 1 := by
  ext <;> simp [exp]

/-- The exponential law: `Exp(x)·Exp(y) = Exp(x+y)`  [§3]. -/
theorem exp_mul_exp (x y : ι → ℚ) : exp B x * exp B y = exp B (x + y) := by
  ext
  · simp [exp]
  · simp [exp, add_comm]
  · simp only [exp, mul_socle]
    rw [B.quad_add]
    ring

@[simp] theorem exp_mul_exp_neg (x : ι → ℚ) : exp B x * exp B (-x) = 1 := by
  rw [exp_mul_exp]
  simp

/-- `Exp(x)` as a unit of `A_B`, with inverse `Exp(-x)`. -/
def expUnit (B : BilinearFormMatrix ι) (x : ι → ℚ) : (CubeAlgebra B)ˣ where
  val := exp B x
  inv := exp B (-x)
  val_inv := exp_mul_exp_neg x
  inv_val := by rw [mul_comm]; exact exp_mul_exp_neg x

@[simp] theorem expUnit_val (x : ι → ℚ) : (expUnit B x : CubeAlgebra B) = exp B x := rfl

theorem expUnit_add (x y : ι → ℚ) : expUnit B (x + y) = expUnit B x * expUnit B y :=
  Units.ext (by simp [exp_mul_exp])

theorem expUnit_zero : expUnit B 0 = 1 := Units.ext (by simp)

end CubeAlgebra

end Trinomial
