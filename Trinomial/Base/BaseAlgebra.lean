import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.RingTheory.Binomial
import Trinomial.Base.Laurent
import Trinomial.Base.RatAlgebra

/-!
# The algebra `A₀ = L_N/J₀` and the normal-form evaluation

[§2].  The base ideal `J₀` has the `(N+5)`-dimensional quotient `A₀` with
`ℚ`-basis `1, B, B², B³, B⁴, C₁, …, C_N` (Lemma 2.1), where `B = S − T` and
`Cᵢ = Dᵢ − 1`.  This module realizes `A₀` as an explicit algebra of coordinate vectors:

* `BaseAlgebra N` — coordinates `b0 … b4` (for `1, B, …, B⁴`) and `c : Fin N → ℚ`
  (for `C₁ … C_N`), with the multiplication induced by the relations
  `B⁵ = 0`, `B·Cᵢ = 0`, `Cᵢ·Cⱼ = 0`.
* `baseEval : L_N →ₐ[ℚ] BaseAlgebra N` — evaluation at
  `S ↦ (1+B)/2`, `T ↦ (1−B)/2`, `Dᵢ ↦ 1 + Cᵢ`, defined on monomials by the closed
  normal form of **Lemma 2.2**:

    `S^a T^b D^d ↦ 2^{−a−b} ((1+B)^a (1−B)^b + Σᵢ dᵢ Cᵢ)`,

  with `(1±B)^a = Σ_{k<5} (a choose k) (±B)^k` (truncated binomial series, `a ∈ ℤ`; the
  generalized binomial coefficient is mathlib's `Ring.choose`, see `zchoose`).
* `baseMonoUnit_val` — the closed form itself; the `B^k`-coefficients of
  `(1+B)^a (1−B)^b` are the polynomials `w1 … w4` in `r = a−b`, `s = a+b` that appear
  in the equations `(k=0) … (k=4)` of the proof of Proposition 2.4.

In `Trinomial/Base/BaseIdeal.lean` the base ideal is defined by the paper's generators and
proved equal to `RingHom.ker baseEval`; membership in `J₀` then reduces to the vanishing
of the `N+5` coordinates of `baseEval f`, which is how the paper argues.
-/

set_option autoImplicit false

namespace Trinomial

/-- Coordinates with respect to the basis `1, B, B², B³, B⁴, C₁, …, C_N` of `A₀`
[Lemma 2.1]. -/
@[ext]
structure BaseAlgebra (N : ℕ) where
  /-- The coefficient of `1`. -/
  b0 : ℚ
  /-- The coefficient of `B`. -/
  b1 : ℚ
  /-- The coefficient of `B²`. -/
  b2 : ℚ
  /-- The coefficient of `B³`. -/
  b3 : ℚ
  /-- The coefficient of `B⁴`. -/
  b4 : ℚ
  /-- The coefficients of `C₁, …, C_N`. -/
  c : Fin N → ℚ

namespace BaseAlgebra

variable {N : ℕ}

instance : Zero (BaseAlgebra N) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : One (BaseAlgebra N) := ⟨⟨1, 0, 0, 0, 0, 0⟩⟩
instance : Add (BaseAlgebra N) :=
  ⟨fun x y => ⟨x.b0 + y.b0, x.b1 + y.b1, x.b2 + y.b2, x.b3 + y.b3, x.b4 + y.b4,
    fun j => x.c j + y.c j⟩⟩
instance : Neg (BaseAlgebra N) :=
  ⟨fun x => ⟨-x.b0, -x.b1, -x.b2, -x.b3, -x.b4, fun j => -x.c j⟩⟩

/-- Multiplication of coordinate vectors: truncated convolution on the `B`-line
(`B⁵ = 0`) and scalar action on the `C`-hyperplane (`B·Cᵢ = Cᵢ·Cⱼ = 0`). -/
instance : Mul (BaseAlgebra N) :=
  ⟨fun x y =>
    ⟨x.b0 * y.b0,
     x.b0 * y.b1 + x.b1 * y.b0,
     x.b0 * y.b2 + x.b1 * y.b1 + x.b2 * y.b0,
     x.b0 * y.b3 + x.b1 * y.b2 + x.b2 * y.b1 + x.b3 * y.b0,
     x.b0 * y.b4 + x.b1 * y.b3 + x.b2 * y.b2 + x.b3 * y.b1 + x.b4 * y.b0,
     fun j => x.b0 * y.c j + y.b0 * x.c j⟩⟩

@[simp] lemma zero_b0 : (0 : BaseAlgebra N).b0 = 0 := rfl
@[simp] lemma zero_b1 : (0 : BaseAlgebra N).b1 = 0 := rfl
@[simp] lemma zero_b2 : (0 : BaseAlgebra N).b2 = 0 := rfl
@[simp] lemma zero_b3 : (0 : BaseAlgebra N).b3 = 0 := rfl
@[simp] lemma zero_b4 : (0 : BaseAlgebra N).b4 = 0 := rfl
@[simp] lemma zero_c (j : Fin N) : (0 : BaseAlgebra N).c j = 0 := rfl
@[simp] lemma one_b0 : (1 : BaseAlgebra N).b0 = 1 := rfl
@[simp] lemma one_b1 : (1 : BaseAlgebra N).b1 = 0 := rfl
@[simp] lemma one_b2 : (1 : BaseAlgebra N).b2 = 0 := rfl
@[simp] lemma one_b3 : (1 : BaseAlgebra N).b3 = 0 := rfl
@[simp] lemma one_b4 : (1 : BaseAlgebra N).b4 = 0 := rfl
@[simp] lemma one_c (j : Fin N) : (1 : BaseAlgebra N).c j = 0 := rfl
@[simp] lemma add_b0 (x y : BaseAlgebra N) : (x + y).b0 = x.b0 + y.b0 := rfl
@[simp] lemma add_b1 (x y : BaseAlgebra N) : (x + y).b1 = x.b1 + y.b1 := rfl
@[simp] lemma add_b2 (x y : BaseAlgebra N) : (x + y).b2 = x.b2 + y.b2 := rfl
@[simp] lemma add_b3 (x y : BaseAlgebra N) : (x + y).b3 = x.b3 + y.b3 := rfl
@[simp] lemma add_b4 (x y : BaseAlgebra N) : (x + y).b4 = x.b4 + y.b4 := rfl
@[simp] lemma add_c (x y : BaseAlgebra N) (j : Fin N) : (x + y).c j = x.c j + y.c j := rfl
@[simp] lemma neg_b0 (x : BaseAlgebra N) : (-x).b0 = -x.b0 := rfl
@[simp] lemma neg_b1 (x : BaseAlgebra N) : (-x).b1 = -x.b1 := rfl
@[simp] lemma neg_b2 (x : BaseAlgebra N) : (-x).b2 = -x.b2 := rfl
@[simp] lemma neg_b3 (x : BaseAlgebra N) : (-x).b3 = -x.b3 := rfl
@[simp] lemma neg_b4 (x : BaseAlgebra N) : (-x).b4 = -x.b4 := rfl
@[simp] lemma neg_c (x : BaseAlgebra N) (j : Fin N) : (-x).c j = -x.c j := rfl
@[simp] lemma mul_b0 (x y : BaseAlgebra N) : (x * y).b0 = x.b0 * y.b0 := rfl
@[simp] lemma mul_b1 (x y : BaseAlgebra N) :
    (x * y).b1 = x.b0 * y.b1 + x.b1 * y.b0 := rfl
@[simp] lemma mul_b2 (x y : BaseAlgebra N) :
    (x * y).b2 = x.b0 * y.b2 + x.b1 * y.b1 + x.b2 * y.b0 := rfl
@[simp] lemma mul_b3 (x y : BaseAlgebra N) :
    (x * y).b3 = x.b0 * y.b3 + x.b1 * y.b2 + x.b2 * y.b1 + x.b3 * y.b0 := rfl
@[simp] lemma mul_b4 (x y : BaseAlgebra N) :
    (x * y).b4 = x.b0 * y.b4 + x.b1 * y.b3 + x.b2 * y.b2 + x.b3 * y.b1 + x.b4 * y.b0 := rfl
@[simp] lemma mul_c (x y : BaseAlgebra N) (j : Fin N) :
    (x * y).c j = x.b0 * y.c j + y.b0 * x.c j := rfl

instance : CommRing (BaseAlgebra N) :=
  CommRing.ofMinimalAxioms
    (fun x y z => by ext <;> simp <;> ring)
    (fun x => by ext <;> simp)
    (fun x => by ext <;> simp)
    (fun x y z => by ext <;> simp <;> ring)
    (fun x y => by ext <;> simp <;> ring)
    (fun x => by ext <;> simp)
    (fun x y z => by ext <;> simp <;> ring)

/-- The embedding of `ℚ` as multiples of `1`. -/
def scalarRingHom (N : ℕ) : ℚ →+* BaseAlgebra N where
  toFun r := ⟨r, 0, 0, 0, 0, 0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

instance : Algebra ℚ (BaseAlgebra N) := (scalarRingHom N).toAlgebra

@[simp] lemma algebraMap_b0 (r : ℚ) : (algebraMap ℚ (BaseAlgebra N) r).b0 = r := rfl
@[simp] lemma algebraMap_b1 (r : ℚ) : (algebraMap ℚ (BaseAlgebra N) r).b1 = 0 := rfl
@[simp] lemma algebraMap_b2 (r : ℚ) : (algebraMap ℚ (BaseAlgebra N) r).b2 = 0 := rfl
@[simp] lemma algebraMap_b3 (r : ℚ) : (algebraMap ℚ (BaseAlgebra N) r).b3 = 0 := rfl
@[simp] lemma algebraMap_b4 (r : ℚ) : (algebraMap ℚ (BaseAlgebra N) r).b4 = 0 := rfl
@[simp] lemma algebraMap_c (r : ℚ) (j : Fin N) :
    (algebraMap ℚ (BaseAlgebra N) r).c j = 0 := rfl

@[simp] lemma smul_b0 (r : ℚ) (x : BaseAlgebra N) : (r • x).b0 = r * x.b0 := by
  rw [Algebra.smul_def]; simp
@[simp] lemma smul_b1 (r : ℚ) (x : BaseAlgebra N) : (r • x).b1 = r * x.b1 := by
  rw [Algebra.smul_def]; simp
@[simp] lemma smul_b2 (r : ℚ) (x : BaseAlgebra N) : (r • x).b2 = r * x.b2 := by
  rw [Algebra.smul_def]; simp
@[simp] lemma smul_b3 (r : ℚ) (x : BaseAlgebra N) : (r • x).b3 = r * x.b3 := by
  rw [Algebra.smul_def]; simp
@[simp] lemma smul_b4 (r : ℚ) (x : BaseAlgebra N) : (r • x).b4 = r * x.b4 := by
  rw [Algebra.smul_def]; simp
@[simp] lemma smul_c (r : ℚ) (x : BaseAlgebra N) (j : Fin N) :
    (r • x).c j = r * x.c j := by
  rw [Algebra.smul_def]; simp

/-! ### The distinguished elements `B` and `Cᵢ` and their relations -/

/-- The residue of `B = S − T`. -/
def B (N : ℕ) : BaseAlgebra N := ⟨0, 1, 0, 0, 0, 0⟩

/-- The residue of `Cᵢ = Dᵢ − 1`. -/
def C (i : Fin N) : BaseAlgebra N := ⟨0, 0, 0, 0, 0, Pi.single i 1⟩

@[simp] lemma B_pow2 : B N ^ 2 = ⟨0, 0, 1, 0, 0, 0⟩ := by
  rw [pow_two]; ext <;> simp [B]
@[simp] lemma B_pow3 : B N ^ 3 = ⟨0, 0, 0, 1, 0, 0⟩ := by
  rw [pow_succ, B_pow2]; ext <;> simp [B]
@[simp] lemma B_pow4 : B N ^ 4 = ⟨0, 0, 0, 0, 1, 0⟩ := by
  rw [pow_succ, B_pow3]; ext <;> simp [B]
@[simp] lemma B_pow5 : B N ^ 5 = 0 := by
  rw [pow_succ, B_pow4]; ext <;> simp [B]

@[simp] lemma B_mul_C (i : Fin N) : B N * C i = 0 := by
  ext <;> simp [B, C]

@[simp] lemma C_mul_C (i j : Fin N) : C i * C j = 0 := by
  ext <;> simp [C]

/-! ### The units `(1 ± B)`, `(1 + Cᵢ)` and the truncated binomial series -/

/-- The binomial coefficient `(a choose k) = a(a−1)⋯(a−k+1)/k!` of an integer `a`, which
"is well-defined even when `a` is negative" [proof of Lemma 2.2]: mathlib's
generalized binomial coefficient `Ring.choose`, read in `ℚ`. -/
noncomputable abbrev zchoose (a : ℤ) (k : ℕ) : ℚ := Ring.choose (a : ℚ) k

/-- `Ring.choose a k = a(a−1)⋯(a−k+1)/k!` in `ℚ`. -/
theorem zchoose_eq (a : ℤ) (k : ℕ) :
    zchoose a k = (∏ i ∈ Finset.range k, ((a : ℚ) - i)) / k.factorial := by
  have h : ∀ k : ℕ, (descPochhammer ℤ k).smeval (a : ℚ) = ∏ i ∈ Finset.range k, ((a : ℚ) - i) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ,
          Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
        simp
  rw [zchoose, Ring.choose_eq_smul, h, smul_eq_mul, div_eq_inv_mul]

@[simp] theorem zchoose_zero (a : ℤ) : zchoose a 0 = 1 := Ring.choose_zero_right _
@[simp] theorem zchoose_one (a : ℤ) : zchoose a 1 = a := Ring.choose_one_right _
@[simp] theorem zchoose_two (a : ℤ) : zchoose a 2 = a * (a - 1) / 2 := by
  rw [zchoose_eq]; simp [Finset.prod_range_succ, Nat.factorial]
@[simp] theorem zchoose_three (a : ℤ) : zchoose a 3 = a * (a - 1) * (a - 2) / 6 := by
  rw [zchoose_eq]; simp [Finset.prod_range_succ, Nat.factorial]
@[simp] theorem zchoose_four (a : ℤ) : zchoose a 4 = a * (a - 1) * (a - 2) * (a - 3) / 24 := by
  rw [zchoose_eq]; simp [Finset.prod_range_succ, Nat.factorial]

/-- The unit `1 + εB` for `ε = ±1`, with inverse `1 − εB + ε²B² − ε³B³ + ε⁴B⁴`. -/
def uBe (N : ℕ) (ε : ℚ) : (BaseAlgebra N)ˣ where
  val := ⟨1, ε, 0, 0, 0, 0⟩
  inv := ⟨1, -ε, ε ^ 2, -ε ^ 3, ε ^ 4, 0⟩
  val_inv := by ext <;> simp <;> ring
  inv_val := by ext <;> simp <;> ring

@[simp] lemma uBe_val (ε : ℚ) : (uBe N ε : BaseAlgebra N) = ⟨1, ε, 0, 0, 0, 0⟩ := rfl
@[simp] lemma uBe_inv_val (ε : ℚ) :
    ((uBe N ε)⁻¹ : (BaseAlgebra N)ˣ).val = ⟨1, -ε, ε ^ 2, -ε ^ 3, ε ^ 4, 0⟩ := rfl

/-- The unit `1 + Cᵢ` with inverse `1 − Cᵢ`. -/
def uD (i : Fin N) : (BaseAlgebra N)ˣ where
  val := ⟨1, 0, 0, 0, 0, Pi.single i 1⟩
  inv := ⟨1, 0, 0, 0, 0, -Pi.single i 1⟩
  val_inv := by
    refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
    funext j
    simp
  inv_val := by
    refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
    funext j
    simp

@[simp] lemma uD_val (i : Fin N) :
    (uD i : BaseAlgebra N) = ⟨1, 0, 0, 0, 0, Pi.single i 1⟩ := rfl
@[simp] lemma uD_inv_val (i : Fin N) :
    ((uD i)⁻¹ : (BaseAlgebra N)ˣ).val = ⟨1, 0, 0, 0, 0, -Pi.single i 1⟩ := rfl

/-- Truncated binomial series for integer powers of `1 + εB`
[proof of Lemma 2.2]:  `(1+εB)^a = Σ_{k<5} (a choose k) ε^k B^k`, the sum
being truncated because `B⁵ = 0`. -/
theorem uBe_zpow (ε : ℚ) (a : ℤ) :
    ((uBe N ε ^ a : (BaseAlgebra N)ˣ) : BaseAlgebra N) =
      ⟨1, zchoose a 1 * ε, zchoose a 2 * ε ^ 2, zchoose a 3 * ε ^ 3, zchoose a 4 * ε ^ 4, 0⟩ := by
  induction a using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      ext <;> simp
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, ih, uBe_val]
      ext <;> simp <;> ring
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, ih, uBe_inv_val]
      ext <;> simp <;> ring

/-- Integer powers of `1 + Cᵢ`:  `(1+Cᵢ)^m = 1 + m·Cᵢ`. -/
theorem uD_zpow (i : Fin N) (m : ℤ) :
    ((uD i ^ m : (BaseAlgebra N)ˣ) : BaseAlgebra N) =
      ⟨1, 0, 0, 0, 0, Pi.single i (m : ℚ)⟩ := by
  induction m using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      funext j
      simp
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, ih, uD_val]
      refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      funext j
      by_cases h : j = i <;> simp [h, Pi.single_apply]
      ring
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, ih, uD_inv_val]
      refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      funext j
      by_cases h : j = i <;> simp [h, Pi.single_apply]
      ring

/-- The product `Π_{i ∈ s} (1+Cᵢ)^{dᵢ} = 1 + Σ_{i ∈ s} dᵢCᵢ` over any index set. -/
theorem prod_uD_zpow_subset (d : Fin N → ℤ) (s : Finset (Fin N)) :
    ((∏ i ∈ s, uD i ^ d i : (BaseAlgebra N)ˣ) : BaseAlgebra N) =
      ⟨1, 0, 0, 0, 0, fun j => if j ∈ s then (d j : ℚ) else 0⟩ := by
  induction s using Finset.induction with
  | empty =>
      rw [Finset.prod_empty]
      refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      funext j
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul, ih, uD_zpow]
      refine BaseAlgebra.ext (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      funext j
      by_cases h : j = a
      · subst h
        simp [ha]
      · simp [h, Finset.mem_insert]

/-- `Π_i (1+Cᵢ)^{dᵢ} = 1 + Σ_i dᵢCᵢ`  [proof of Lemma 2.2]. -/
theorem prod_uD_zpow (d : Fin N → ℤ) :
    ((∏ i, uD i ^ d i : (BaseAlgebra N)ˣ) : BaseAlgebra N) =
      ⟨1, 0, 0, 0, 0, fun j => (d j : ℚ)⟩ := by
  rw [prod_uD_zpow_subset]
  refine BaseAlgebra.ext rfl rfl rfl rfl rfl ?_
  funext j
  simp

/-! ### The normal form of a monomial (Lemma 2.2) -/

/-! The `B^k`-coefficients of `(1+B)^a (1−B)^b` in the variables `r = a−b`, `s = a+b`.
These are exactly the left-hand sides of the equations `(k=1) … (k=4)` in the proof of
Proposition 2.4 (up to the factor `k!`).  All four take the same pair of arguments, so that
they can be applied uniformly; `w1` ignores `s`. -/

/-- The `B`-coefficient. -/
def w1 (r _s : ℚ) : ℚ := r
/-- The `B²`-coefficient. -/
def w2 (r s : ℚ) : ℚ := (r ^ 2 - s) / 2
/-- The `B³`-coefficient. -/
def w3 (r s : ℚ) : ℚ := r * (r ^ 2 - 3 * s + 2) / 6
/-- The `B⁴`-coefficient. -/
def w4 (r s : ℚ) : ℚ := (r ^ 4 - 6 * r ^ 2 * s + 8 * r ^ 2 + 3 * s ^ 2 - 6 * s) / 24

/-- The image of the Laurent monomial `S^{x.s} T^{x.t} D^{x.d}` in `A₀`, as a unit:
`2^{−a−b} (1+B)^a (1−B)^b Π_i (1+Cᵢ)^{dᵢ}`. -/
noncomputable def baseMonoUnit (x : Exponent N) : (BaseAlgebra N)ˣ :=
  (twoUnit (BaseAlgebra N))⁻¹ ^ (x.s + x.t) * uBe N 1 ^ x.s * uBe N (-1) ^ x.t
    * ∏ i, uD i ^ x.d i

/-- **Lemma 2.2** (closed normal form): the residue of `S^a T^b D^d` in `A₀` is
`2^{−a−b} (Σ_k w_k(a−b, a+b) B^k + Σ_i dᵢ Cᵢ)`. -/
theorem baseMonoUnit_val (x : Exponent N) :
    ((baseMonoUnit x : (BaseAlgebra N)ˣ) : BaseAlgebra N) =
      (1 / 2 : ℚ) ^ (x.s + x.t) •
        ⟨1, w1 ((x.s : ℚ) - x.t) ((x.s : ℚ) + x.t), w2 ((x.s : ℚ) - x.t) ((x.s : ℚ) + x.t),
          w3 ((x.s : ℚ) - x.t) ((x.s : ℚ) + x.t), w4 ((x.s : ℚ) - x.t) ((x.s : ℚ) + x.t),
          fun j => (x.d j : ℚ)⟩ := by
  rw [baseMonoUnit, Units.val_mul, Units.val_mul, Units.val_mul, twoUnit_inv_zpow_val,
    uBe_zpow, uBe_zpow, prod_uD_zpow, mul_assoc, mul_assoc, ← Algebra.smul_def]
  congr 1
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp [w1]; ring
  · simp [w2]; ring
  · simp [w3]; ring
  · simp [w4]; ring
  · funext j
    simp

theorem baseMonoUnit_zero : baseMonoUnit (0 : Exponent N) = 1 := by
  apply Units.ext
  rw [baseMonoUnit_val]
  ext <;> simp [w1, w2, w3, w4]

theorem baseMonoUnit_add (x y : Exponent N) :
    baseMonoUnit (x + y) = baseMonoUnit x * baseMonoUnit y := by
  rw [baseMonoUnit, baseMonoUnit, baseMonoUnit, Exponent.add_s, Exponent.add_t,
    show x.s + y.s + (x.t + y.t) = (x.s + x.t) + (y.s + y.t) by ring, zpow_add,
    zpow_add (uBe N 1) x.s y.s, zpow_add (uBe N (-1)) x.t y.t]
  have hprod : (∏ i, uD i ^ (x + y).d i : (BaseAlgebra N)ˣ)
      = (∏ i, uD i ^ x.d i) * ∏ i, uD i ^ y.d i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Exponent.add_d, Pi.add_apply, zpow_add]
  rw [hprod]
  simp only [mul_assoc, mul_left_comm]

end BaseAlgebra

open BaseAlgebra in
/-- The evaluation `L_N →ₐ A₀` at `S ↦ (1+B)/2`, `T ↦ (1−B)/2`, `Dᵢ ↦ 1+Cᵢ`.
Its kernel is the base ideal `J₀` (proved in `Trinomial/Base/BaseIdeal.lean`). -/
noncomputable def baseEval (N : ℕ) : Laurent N →ₐ[ℚ] BaseAlgebra N :=
  AddMonoidAlgebra.lift ℚ (BaseAlgebra N) (Exponent N)
    { toFun := fun x => (baseMonoUnit (Multiplicative.toAdd x) : BaseAlgebra N)
      map_one' := by
        rw [show Multiplicative.toAdd (1 : Multiplicative (Exponent N)) = 0 from rfl,
          baseMonoUnit_zero]
        rfl
      map_mul' := fun x y => by
        rw [show Multiplicative.toAdd (x * y) =
          Multiplicative.toAdd x + Multiplicative.toAdd y from rfl, baseMonoUnit_add]
        rfl }

namespace BaseAlgebra

variable {N : ℕ}

theorem baseEval_single (x : Exponent N) (r : ℚ) :
    baseEval N (AddMonoidAlgebra.single x r) = r • (baseMonoUnit x : BaseAlgebra N) := by
  rw [baseEval, AddMonoidAlgebra.lift_single]
  rfl

theorem baseEval_mono (x : Exponent N) :
    baseEval N (mono x) = (baseMonoUnit x : BaseAlgebra N) := by
  rw [mono, baseEval_single, one_smul]

/-- `S ↦ (1+B)/2`  [Lemma 2.2]. -/
theorem baseEval_S : baseEval N (S N) = ⟨1/2, 1/2, 0, 0, 0, 0⟩ := by
  rw [S, baseEval_mono, baseMonoUnit_val]
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · first
      | (funext j; simp [Exponent.gS])
      | norm_num [Exponent.gS, w1, w2, w3, w4]

/-- `T ↦ (1−B)/2`. -/
theorem baseEval_T : baseEval N (T N) = ⟨1/2, -1/2, 0, 0, 0, 0⟩ := by
  rw [T, baseEval_mono, baseMonoUnit_val]
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · first
      | (funext j; simp [Exponent.gT])
      | norm_num [Exponent.gT, w1, w2, w3, w4]

/-- `Dᵢ ↦ 1 + Cᵢ`. -/
theorem baseEval_D (i : Fin N) :
    baseEval N (D i) = ⟨1, 0, 0, 0, 0, Pi.single i 1⟩ := by
  rw [D, baseEval_mono, baseMonoUnit_val]
  refine BaseAlgebra.ext ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [Exponent.gD, w1, w2, w3, w4]
  · norm_num [Exponent.gD, w1, w2, w3, w4]
  · norm_num [Exponent.gD, w1, w2, w3, w4]
  · norm_num [Exponent.gD, w1, w2, w3, w4]
  · norm_num [Exponent.gD, w1, w2, w3, w4]
  · funext j
    simp [Exponent.gD, Pi.single_apply, apply_ite (Int.cast : ℤ → ℚ)]

end BaseAlgebra

end Trinomial
