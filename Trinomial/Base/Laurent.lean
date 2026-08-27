import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Order.Fin.Basic
import Mathlib.Order.PiLex
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic

/-!
# The Laurent polynomial ring `L_N`

This module sets up the ambient ring of the paper [§2]:
the Laurent polynomial ring `L_N = ℚ[S^{±1}, T^{±1}, D_1^{±1}, …, D_N^{±1}]`,
realized as the group algebra of its exponent lattice `ℤ × ℤ × ℤ^N`.

Main definitions:

* `Trinomial.Exponent N` — the exponent lattice, with named components `s`, `t`, `d`
  so that an exponent vector reads exactly like the paper's `S^a T^b D^d`.
* `Trinomial.Laurent N` — the ring `L_N`.
* `Trinomial.mono x` — the Laurent monomial `S^{x.s} T^{x.t} D^{x.d}`;
  `Trinomial.monoUnit x` — the same monomial as a unit.
* `Trinomial.S`, `Trinomial.T`, `Trinomial.D i` — the variables.
* `Trinomial.algHom_ext_laurent` — a `ℚ`-algebra homomorphism on `L_N` is determined by the
  images of the variables.  This is the formal counterpart of the paper's convention of
  specifying homomorphisms such as `φ_Q` by the images of `S`, `T`, `D_i`.
* `Trinomial.HasShort k I` — the decision problem `t(I) ≤ k` from the introduction:
  `I` contains a nonzero element with at most `k` (collected) terms.
* `Trinomial.isUnit_laurent_iff` — the units of `L_N` are exactly the elements
  `c · S^a T^b D^d` with `c ≠ 0`; this is the meaning of "up to units of `L_N`" in
  Proposition 2.4.

Support always means the `Finsupp` support of the group-algebra element, so equal
monomials are collected automatically and "accidental cancellation never counts as an
extra term".
-/

set_option autoImplicit false

namespace Trinomial

/-- An exponent vector of a Laurent monomial `S^a T^b D_1^{d_1} ⋯ D_N^{d_N}`:
`s` and `t` are the exponents of `S` and `T`, and `d` the vector of `D`-exponents. -/
@[ext]
structure Exponent (N : ℕ) where
  /-- The exponent of `S`. -/
  s : ℤ
  /-- The exponent of `T`. -/
  t : ℤ
  /-- The exponents of `D_1, …, D_N`. -/
  d : Fin N → ℤ
deriving DecidableEq

namespace Exponent

variable {N : ℕ}

instance : Zero (Exponent N) := ⟨⟨0, 0, 0⟩⟩
instance : Add (Exponent N) := ⟨fun x y => ⟨x.s + y.s, x.t + y.t, x.d + y.d⟩⟩
instance : Neg (Exponent N) := ⟨fun x => ⟨-x.s, -x.t, -x.d⟩⟩

@[simp] lemma zero_s : (0 : Exponent N).s = 0 := rfl
@[simp] lemma zero_t : (0 : Exponent N).t = 0 := rfl
@[simp] lemma zero_d : (0 : Exponent N).d = 0 := rfl
@[simp] lemma add_s (x y : Exponent N) : (x + y).s = x.s + y.s := rfl
@[simp] lemma add_t (x y : Exponent N) : (x + y).t = x.t + y.t := rfl
@[simp] lemma add_d (x y : Exponent N) : (x + y).d = x.d + y.d := rfl
@[simp] lemma neg_s (x : Exponent N) : (-x).s = -x.s := rfl
@[simp] lemma neg_t (x : Exponent N) : (-x).t = -x.t := rfl
@[simp] lemma neg_d (x : Exponent N) : (-x).d = -x.d := rfl

instance : AddCommGroup (Exponent N) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  neg_add_cancel x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Projection to the `s`-component, as an additive homomorphism. -/
def sHom (N : ℕ) : Exponent N →+ ℤ where
  toFun := s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection to the `t`-component, as an additive homomorphism. -/
def tHom (N : ℕ) : Exponent N →+ ℤ where
  toFun := t
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection to the `j`-th `d`-component, as an additive homomorphism. -/
def dHom (N : ℕ) (j : Fin N) : Exponent N →+ ℤ where
  toFun x := x.d j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma zsmul_s (n : ℤ) (x : Exponent N) : (n • x).s = n * x.s := by
  rw [show (n • x).s = sHom N (n • x) from rfl, map_zsmul, smul_eq_mul]
  rfl

@[simp] lemma zsmul_t (n : ℤ) (x : Exponent N) : (n • x).t = n * x.t := by
  rw [show (n • x).t = tHom N (n • x) from rfl, map_zsmul, smul_eq_mul]
  rfl

@[simp] lemma zsmul_d_apply (n : ℤ) (x : Exponent N) (j : Fin N) :
    (n • x).d j = n * x.d j := by
  rw [show (n • x).d j = dHom N j (n • x) from rfl, map_zsmul, smul_eq_mul]
  rfl

/-- The exponent of the variable `S`. -/
def gS : Exponent N := ⟨1, 0, 0⟩
/-- The exponent of the variable `T`. -/
def gT : Exponent N := ⟨0, 1, 0⟩
/-- The exponent of the variable `D i`. -/
def gD (i : Fin N) : Exponent N := ⟨0, 0, Pi.single i 1⟩

@[simp] lemma gS_s : (gS : Exponent N).s = 1 := rfl
@[simp] lemma gS_t : (gS : Exponent N).t = 0 := rfl
@[simp] lemma gS_d : (gS : Exponent N).d = 0 := rfl
@[simp] lemma gT_s : (gT : Exponent N).s = 0 := rfl
@[simp] lemma gT_t : (gT : Exponent N).t = 1 := rfl
@[simp] lemma gT_d : (gT : Exponent N).d = 0 := rfl
@[simp] lemma gD_s (i : Fin N) : (gD i).s = 0 := rfl
@[simp] lemma gD_t (i : Fin N) : (gD i).t = 0 := rfl
@[simp] lemma gD_d (i : Fin N) : (gD i).d = Pi.single i 1 := rfl

/-- Every exponent vector decomposes over the variable exponents.  This is what makes a
multiplicative map on monomials determined by its values on the variables. -/
theorem eq_sum_generators (x : Exponent N) :
    x = x.s • gS + x.t • gT + ∑ i, x.d i • gD i := by
  have hs : (∑ i, x.d i • gD i).s = 0 := by
    rw [show (∑ i, x.d i • gD i).s = sHom N (∑ i, x.d i • gD i) from rfl, map_sum]
    simp [sHom]
  have ht : (∑ i, x.d i • gD i).t = 0 := by
    rw [show (∑ i, x.d i • gD i).t = tHom N (∑ i, x.d i • gD i) from rfl, map_sum]
    simp [tHom]
  have hd : ∀ j, (∑ i, x.d i • gD i).d j = x.d j := by
    intro j
    rw [show (∑ i, x.d i • gD i).d j = dHom N j (∑ i, x.d i • gD i) from rfl, map_sum]
    simp [dHom, Pi.single_apply]
  ext
  case s => simp [hs]
  case t => simp [ht]
  case d j => simp [hd j]

end Exponent

/-- The Laurent polynomial ring `L_N = ℚ[S^{±1}, T^{±1}, D_1^{±1}, …, D_N^{±1}]`,
as the group algebra of the exponent lattice over `ℚ`  [§2]. -/
abbrev Laurent (N : ℕ) : Type := AddMonoidAlgebra ℚ (Exponent N)

variable {N : ℕ}

/-- The Laurent monomial `S^{x.s} T^{x.t} D^{x.d}` (with coefficient `1`). -/
noncomputable def mono (x : Exponent N) : Laurent N := AddMonoidAlgebra.single x 1

@[simp] theorem mono_zero : mono (0 : Exponent N) = 1 :=
  rfl

theorem mono_mul (x y : Exponent N) : mono x * mono y = mono (x + y) := by
  simp [mono, AddMonoidAlgebra.single_mul_single]

theorem mono_ne_zero (x : Exponent N) : mono x ≠ 0 :=
  Finsupp.single_ne_zero.mpr one_ne_zero

@[simp] theorem support_mono (x : Exponent N) : (mono x).support = {x} :=
  Finsupp.support_single_ne_zero x one_ne_zero

/-- The monomial `mono x` as a unit of `L_N`: "monomials in `L_N` are units". -/
noncomputable def monoUnit (x : Exponent N) : (Laurent N)ˣ where
  val := mono x
  inv := mono (-x)
  val_inv := by rw [mono_mul, add_neg_cancel, mono_zero]
  inv_val := by rw [mono_mul, neg_add_cancel, mono_zero]

@[simp] theorem monoUnit_val (x : Exponent N) : (monoUnit x : Laurent N) = mono x := rfl

theorem monoUnit_zero : monoUnit (0 : Exponent N) = 1 :=
  Units.ext (by simp)

theorem monoUnit_neg (x : Exponent N) : monoUnit (-x) = (monoUnit x)⁻¹ :=
  Units.ext rfl

theorem monoUnit_add (x y : Exponent N) : monoUnit (x + y) = monoUnit x * monoUnit y :=
  Units.ext (by simp [mono_mul])

theorem monoUnit_zsmul (n : ℤ) (x : Exponent N) : monoUnit (n • x) = monoUnit x ^ n := by
  induction n using Int.induction_on with
  | zero => simpa using monoUnit_zero
  | succ k ih => rw [add_smul, one_smul, monoUnit_add, ih, zpow_add_one]
  | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, monoUnit_add, ih, monoUnit_neg,
        zpow_sub_one]

/-- The variable `S`. -/
noncomputable def S (N : ℕ) : Laurent N := mono Exponent.gS
/-- The variable `T`. -/
noncomputable def T (N : ℕ) : Laurent N := mono Exponent.gT
/-- The variable `D i`. -/
noncomputable def D (i : Fin N) : Laurent N := mono (Exponent.gD i)

/-- `S` as a unit of `L_N`. -/
noncomputable def SU (N : ℕ) : (Laurent N)ˣ := monoUnit Exponent.gS
/-- `T` as a unit of `L_N`. -/
noncomputable def TU (N : ℕ) : (Laurent N)ˣ := monoUnit Exponent.gT
/-- `D i` as a unit of `L_N`. -/
noncomputable def DU (i : Fin N) : (Laurent N)ˣ := monoUnit (Exponent.gD i)

@[simp] theorem SU_val : (SU N : Laurent N) = S N := rfl
@[simp] theorem TU_val : (TU N : Laurent N) = T N := rfl
@[simp] theorem DU_val (i : Fin N) : (DU i : Laurent N) = D i := rfl

/-- Every monomial is the corresponding product of powers of the variables. -/
theorem monoUnit_eq_prod (x : Exponent N) :
    monoUnit x = SU N ^ x.s * TU N ^ x.t * ∏ i, DU i ^ x.d i := by
  conv_lhs => rw [x.eq_sum_generators]
  rw [monoUnit_add, monoUnit_add, monoUnit_zsmul, monoUnit_zsmul]
  congr 1
  induction (Finset.univ : Finset (Fin N)) using Finset.induction with
  | empty => simpa using monoUnit_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, monoUnit_add, monoUnit_zsmul, ih]
      rfl

/-- A `ℚ`-algebra homomorphism on `L_N` is determined by the images of the variables
`S`, `T`, `D i`.  The paper specifies its homomorphisms (`φ_Q`, and the normal-form map
onto `A₀`) exactly this way. -/
theorem algHom_ext_laurent {A : Type*} [CommRing A] [Algebra ℚ A]
    {f g : Laurent N →ₐ[ℚ] A}
    (hS : f (S N) = g (S N)) (hT : f (T N) = g (T N)) (hD : ∀ i, f (D i) = g (D i)) :
    f = g := by
  apply AddMonoidAlgebra.algHom_ext
  intro x
  have key : ∀ (h : Laurent N →ₐ[ℚ] A),
      h (mono x) = (Units.map (h : Laurent N →* A)
        (SU N ^ x.s * TU N ^ x.t * ∏ i, DU i ^ x.d i) : A) := by
    intro h
    rw [← monoUnit_eq_prod]
    rfl
  show f (mono x) = g (mono x)
  rw [key f, key g]
  have hSU : Units.map (f : Laurent N →* A) (SU N) = Units.map (g : Laurent N →* A) (SU N) :=
    Units.ext (by simpa using hS)
  have hTU : Units.map (f : Laurent N →* A) (TU N) = Units.map (g : Laurent N →* A) (TU N) :=
    Units.ext (by simpa using hT)
  have hDU : ∀ i, Units.map (f : Laurent N →* A) (DU i) =
      Units.map (g : Laurent N →* A) (DU i) :=
    fun i => Units.ext (by simpa using hD i)
  simp only [map_mul, map_zpow, map_prod, hSU, hTU]
  norm_cast
  congr 2
  funext i
  rw [hDU i]

/-- Multiplying by a unit `c · S^a T^b D^d` of `L_N` translates the support by the exponent
vector of the monomial. -/
theorem support_smul_mono_mul {c : ℚ} (hc : c ≠ 0) (z : Exponent N) (g : Laurent N) :
    (c • (mono z * g)).support = g.support.image (z + ·) := by
  rw [Finsupp.support_smul_eq hc, mono,
    AddMonoidAlgebra.support_single_mul_eq_image g (fun y => by simp) (IsAddLeftRegular.all z)]

/-- "Up to units" does not change the number of terms: multiplying by `c · S^a T^b D^d`
preserves the cardinality of the support. -/
theorem supportCard_smul_mono_mul {c : ℚ} (hc : c ≠ 0) (z : Exponent N) (g : Laurent N) :
    (c • (mono z * g)).support.card = g.support.card := by
  rw [support_smul_mono_mul hc]
  exact Finset.card_image_of_injective _ (add_right_injective z)

/-- The decision problem `t(I) ≤ k` of the paper for an ideal of the Laurent ring `L_N`:
`I` contains a nonzero element with at most `k` (collected) terms.  (For ideals of the
polynomial ring `ℚ[S, T, D]` see `HasShortPoly` in `Trinomial/ShortestPolynomial.lean`.) -/
def HasShort (k : ℕ) (I : Ideal (Laurent N)) : Prop :=
  ∃ f ∈ I, f ≠ 0 ∧ f.support.card ≤ k

/-! ### The units of `L_N`

"Up to units of `L_N`" in Proposition 2.4 means up to nonzero scalars and Laurent
monomials.  The units of `L_N` are exactly the elements `c · S^a T^b D^d` with `c ≠ 0`.
The proof orders the exponent lattice lexicographically, through the injective additive map
`lexEmb N : Exponent N →+ Lex (Fin (N + 1 + 1) → ℤ)`: a product of two nonzero elements has
a nonzero coefficient at the sum of the largest exponents of the factors and at the sum of
the smallest ones, so if the product is `1`, both sums are `0`, and each factor has a single
exponent. -/

section Units

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [LinearOrder B]
  [IsOrderedAddMonoid B]

/-- Leading coefficients multiply: if `a₁` and `b₁` are `D`-maximal in the supports of `f`
and `g`, then `(f * g) (a₁ + b₁) = f a₁ * g b₁`. -/
theorem mul_apply_add_of_max (D : A →+ B) (hD : Function.Injective D)
    {f g : AddMonoidAlgebra ℚ A} {a₁ b₁ : A}
    (ha : ∀ a ∈ f.support, D a ≤ D a₁) (hb : ∀ b ∈ g.support, D b ≤ D b₁) :
    (f * g) (a₁ + b₁) = f a₁ * g b₁ := by
  classical
  simp_rw [AddMonoidAlgebra.mul_apply, Finsupp.sum]
  rw [Finset.sum_eq_single a₁, Finset.sum_eq_single b₁, if_pos rfl]
  · intro b hb' hne
    refine if_neg fun he => ?_
    have h := congrArg D he
    rw [map_add, map_add] at h
    exact (add_lt_add_of_le_of_lt le_rfl ((hb b hb').lt_of_ne (hD.ne hne))).ne h
  · intro h
    rw [if_pos rfl, Finsupp.notMem_support_iff.1 h, mul_zero]
  · intro a ha' hne
    refine Finset.sum_eq_zero fun b hb' => if_neg fun he => ?_
    have h := congrArg D he
    rw [map_add, map_add] at h
    exact (add_lt_add_of_lt_of_le ((ha a ha').lt_of_ne (hD.ne hne)) (hb b hb')).ne h
  · intro h
    refine Finset.sum_eq_zero fun b _ => ite_eq_right_iff.mpr fun _ => ?_
    rw [Finsupp.notMem_support_iff.1 h, zero_mul]

/-- Trailing coefficients multiply: the `D`-minimal version of `mul_apply_add_of_max`. -/
theorem mul_apply_add_of_min (D : A →+ B) (hD : Function.Injective D)
    {f g : AddMonoidAlgebra ℚ A} {a₀ b₀ : A}
    (ha : ∀ a ∈ f.support, D a₀ ≤ D a) (hb : ∀ b ∈ g.support, D b₀ ≤ D b) :
    (f * g) (a₀ + b₀) = f a₀ * g b₀ :=
  mul_apply_add_of_max (-D) (fun x y h => hD (neg_injective (show -(D x) = -(D y) from h)))
    (fun a ha' => show -(D a) ≤ -(D a₀) from neg_le_neg (ha a ha'))
    (fun b hb' => show -(D b) ≤ -(D b₀) from neg_le_neg (hb b hb'))

/-- If `f * g = 1` in `ℚ[A]`, where `A` embeds additively into a linearly ordered group,
then `f` has exactly one term. -/
theorem card_support_eq_one_of_mul_eq_one (D : A →+ B) (hD : Function.Injective D)
    {f g : AddMonoidAlgebra ℚ A} (h : f * g = 1) : f.support.card = 1 := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact zero_ne_one h
  have hg : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact zero_ne_one h
  obtain ⟨a₁, ha₁, hmax_a⟩ :=
    f.support.exists_max_image D (Finsupp.support_nonempty_iff.mpr hf)
  obtain ⟨b₁, hb₁, hmax_b⟩ :=
    g.support.exists_max_image D (Finsupp.support_nonempty_iff.mpr hg)
  obtain ⟨a₀, ha₀, hmin_a⟩ :=
    f.support.exists_min_image D (Finsupp.support_nonempty_iff.mpr hf)
  obtain ⟨b₀, hb₀, hmin_b⟩ :=
    g.support.exists_min_image D (Finsupp.support_nonempty_iff.mpr hg)
  have hone : ∀ x : A, (1 : AddMonoidAlgebra ℚ A) x ≠ 0 → x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    rw [AddMonoidAlgebra.one_def, Finsupp.single_apply, if_neg fun h0 => hne h0.symm]
  have e1 : a₁ + b₁ = 0 := by
    apply hone
    rw [← h, mul_apply_add_of_max D hD hmax_a hmax_b]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha₁) (Finsupp.mem_support_iff.mp hb₁)
  have e0 : a₀ + b₀ = 0 := by
    apply hone
    rw [← h, mul_apply_add_of_min D hD hmin_a hmin_b]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha₀) (Finsupp.mem_support_iff.mp hb₀)
  have key : D a₀ = D a₁ := by
    have hsum : D a₀ + D b₀ = D a₁ + D b₁ := by
      rw [← map_add, ← map_add, e0, e1]
    by_contra hne
    exact (add_lt_add_of_lt_of_le ((hmin_a a₁ ha₁).lt_of_ne hne) (hmin_b b₁ hb₁)).ne hsum
  rw [Finset.card_eq_one]
  refine ⟨a₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨ha₀, fun a ha => hD ?_⟩⟩
  exact le_antisymm ((hmax_a a ha).trans key.ge) (hmin_a a ha)

end Units

/-- The vector `(a, b, d₁, …, d_N) ∈ ℤ^{N+2}` of an exponent `(a, b, d)`. -/
def lexVec (x : Exponent N) : Fin (N + 1 + 1) → ℤ :=
  Fin.cons (α := fun _ => ℤ) x.s (Fin.cons (α := fun _ => ℤ) x.t x.d)

theorem lexVec_add (x y : Exponent N) : lexVec (x + y) = lexVec x + lexVec y := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  simp [lexVec]

theorem lexVec_injective : Function.Injective (lexVec (N := N)) := by
  intro x y h
  obtain ⟨hs, h'⟩ := Fin.cons_injective2 h
  obtain ⟨ht, hd⟩ := Fin.cons_injective2 h'
  exact Exponent.ext hs ht hd

/-- The exponent lattice, ordered lexicographically: the injective additive map
`(a, b, d) ↦ (a, b, d₁, …, d_N)` into `ℤ^{N+2}` with the lexicographic order. -/
def lexEmb (N : ℕ) : Exponent N →+ Lex (Fin (N + 1 + 1) → ℤ) where
  toFun x := toLex (lexVec x)
  map_zero' := by
    change toLex (lexVec 0) = toLex 0
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    simp [lexVec]
  map_add' x y := by
    change toLex (lexVec (x + y)) = toLex (lexVec x) + toLex (lexVec y)
    rw [lexVec_add]
    rfl

theorem lexEmb_injective (N : ℕ) : Function.Injective (lexEmb N) := fun x y h =>
  lexVec_injective (toLex_inj.mp (show toLex (lexVec x) = toLex (lexVec y) from h))

/-- **The units of `L_N`** are exactly the nonzero scalar multiples of monomials
`c · S^a T^b D^d`  [Proposition 2.4: "up to units of `L_N`"]. -/
theorem isUnit_laurent_iff (f : Laurent N) :
    IsUnit f ↔ ∃ (c : ℚ) (z : Exponent N), c ≠ 0 ∧ f = c • mono z := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := hf.exists_right_inv
    have h1 := card_support_eq_one_of_mul_eq_one (lexEmb N) (lexEmb_injective N) hg
    obtain ⟨z, c, hc, hfz⟩ := Finsupp.card_support_eq_one'.mp h1
    refine ⟨c, z, hc, ?_⟩
    rw [hfz, mono, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  · rintro ⟨c, z, hc, rfl⟩
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℚ (Laurent N))).mul (monoUnit z).isUnit

end Trinomial
