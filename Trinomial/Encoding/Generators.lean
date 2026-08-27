import Trinomial.Encoding.DegreeDecomposition
import Trinomial.Encoding.ZeroDimensional
import Trinomial.Encoding.PolynomialTrinomials
import Trinomial.Encoding.KernelBasis

/-!
# Explicit generators of `I_P`

[Theorem 4.5 ("a finite list of generators of an ideal `I_P`") and
Corollary 5.1 ("the computed presentation of `I_e`"); the mathematics is in the proof of
Theorem 4.5.]

With `𝔪 = ⟨s, t, c₁, …, c_N⟩`, `s = 2S−1`, `t = 2T−1`, `c_i = D_i−1`, and `𝔪⁵ ⊆ I_P`
(`Trinomial/Encoding/ZeroDimensional.lean`), the decomposition of
`Trinomial/Encoding/DegreeDecomposition.lean` gives `I_P = 𝔪⁵ + (I_P ∩ W₄)`, where `W₄` is spanned
by the products `s^a t^b c^γ` with `a + b + |γ| ≤ 4`.  An element
`∑ v_j s^{a_j} t^{b_j} c^{γ_j}` of `W₄` lies in `I_P` iff its images in `A₀` and in every
`A_{Q_i}` vanish, i.e. iff all coordinates of `∑ v_j ψ(s^{a_j} t^{b_j} c^{γ_j})` vanish: a
system of linear equations in `v`.  This module evaluates the images in the coordinate
algebras `A₀` (Lemma 2.2) and `A_Q` (Definition 3.4 of `φ_Q`), forms the rows of that
system, and applies `kernelBasis` ("linear algebra on the residues", the paper, proof of
Corollary 4.6).

* `PointPoly N`, `PointPoly.toPoly` — the output format: a list of pairs (coefficient,
  exponent vector of `s, t, c`) and the polynomial of `ℚ[S,T,D]` it denotes;
* `baseGen`, `cubeGen` — the images of `s, t, c_i` in `A₀` and `A_Q`;
* `rows Q` — the linear system;
* `generators Q` — the executable generator list: the products of degree `5` together with
  the kernel vectors;
* `generatedIdeal_eq` — `span (generators Q) = I_P`.
-/

set_option autoImplicit false

namespace Trinomial

open MvPolynomial

variable {N : ℕ}

/-! ### Output format -/

/-- A polynomial in the coordinates `s, t, c₁, …, c_N`, as a list of pairs (coefficient,
exponent vector): it denotes `∑ a · s^{e 0} t^{e 1} c₁^{e 2} ⋯ c_N^{e (N+1)} ∈ ℚ[S,T,D]`. -/
abbrev PointPoly (N : ℕ) := List (ℚ × (Fin (2 + N) → ℕ))

/-- The element of `ℚ[S, T, D]` denoted by a `PointPoly`. -/
noncomputable def PointPoly.toPoly (l : PointPoly N) : MvPolynomial (Var N) ℚ :=
  (l.map fun t => t.1 • pointMonomial N t.2).sum

@[simp] theorem PointPoly.toPoly_single (a : ℚ) (e : Fin (2 + N) → ℕ) :
    PointPoly.toPoly [(a, e)] = a • pointMonomial N e := by
  simp [PointPoly.toPoly]

/-! ### The maximal ideal `𝔪` and its generators `s, t, c_i` -/

/-- The span of `pointGen N` is the ideal `𝔪` of `Trinomial/Encoding/ZeroDimensional.lean`. -/
theorem span_pointGen_eq_pointIdeal : Ideal.span (Set.range (pointGen N)) = pointIdeal N := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left j =>
        fin_cases j
        · show pointGen N (Fin.castAdd N 0) ∈ pointIdeal N
          rw [pointGen_zero]
          exact Ideal.subset_span (Or.inl (Or.inl rfl))
        · show pointGen N (Fin.castAdd N 1) ∈ pointIdeal N
          rw [pointGen_one]
          exact Ideal.subset_span (Or.inl (Or.inr rfl))
    | right i =>
        rw [pointGen_natAdd]
        exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
  · rw [pointIdeal, Ideal.span_le]
    rintro g ((rfl | rfl) | ⟨i, rfl⟩)
    · exact Ideal.subset_span ⟨Fin.castAdd N 0, pointGen_zero⟩
    · exact Ideal.subset_span ⟨Fin.castAdd N 1, pointGen_one⟩
    · exact Ideal.subset_span ⟨Fin.natAdd 2 i, pointGen_natAdd i⟩

/-- `𝔪⁵ ⊆ I_P`, in terms of `pointGen`  [proof of Theorem 4.5]. -/
theorem span_pointGen_pow_five_le {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Ideal.span (Set.range (pointGen N)) ^ 5 ≤ polyReductionIdeal Q := by
  rw [span_pointGen_eq_pointIdeal]
  exact pointIdeal_pow_five_le Q

/-! ### The images of `s, t, c_i` in `A₀` and `A_Q` -/

/-- The images of `s = 2S−1`, `t = 2T−1`, `c_i = D_i − 1` in `A₀`: `B`, `−B`, `C_i`
[Lemma 2.2: `S ≡ (1+B)/2`, `T ≡ (1−B)/2`, `D_i ≡ 1 + C_i`]. -/
def baseGen (N : ℕ) : Fin (2 + N) → BaseAlgebra N :=
  Fin.append ![BaseAlgebra.B N, -BaseAlgebra.B N] BaseAlgebra.C

/-- The images of `s, t, c_i` under `φ_Q`: `Exp(v₀) − 1`, `Exp(−v₀) − 1`, `Exp(v_i) − 1`
[Definition 3.4 of `φ_Q`]. -/
def cubeGen (G : BilinearFormMatrix (Option (Fin N))) : Fin (2 + N) → CubeAlgebra G :=
  Fin.append ![CubeAlgebra.exp G (homVec 0 1) - 1, CubeAlgebra.exp G (homVec 0 (-1)) - 1]
    (fun i => CubeAlgebra.exp G (homVec (Pi.single i 1) 0) - 1)

theorem baseGen_zero : baseGen N (Fin.castAdd N 0) = BaseAlgebra.B N := by
  simp [baseGen, Fin.append_left]

theorem baseGen_one : baseGen N (Fin.castAdd N 1) = -BaseAlgebra.B N := by
  simp [baseGen, Fin.append_left]

theorem baseGen_natAdd (i : Fin N) : baseGen N (Fin.natAdd 2 i) = BaseAlgebra.C i := by
  simp [baseGen, Fin.append_right]

theorem cubeGen_zero (G : BilinearFormMatrix (Option (Fin N))) :
    cubeGen G (Fin.castAdd N 0) = CubeAlgebra.exp G (homVec 0 1) - 1 := by
  simp [cubeGen, Fin.append_left]

theorem cubeGen_one (G : BilinearFormMatrix (Option (Fin N))) :
    cubeGen G (Fin.castAdd N 1) = CubeAlgebra.exp G (homVec 0 (-1)) - 1 := by
  simp [cubeGen, Fin.append_left]

theorem cubeGen_natAdd (G : BilinearFormMatrix (Option (Fin N))) (i : Fin N) :
    cubeGen G (Fin.natAdd 2 i) = CubeAlgebra.exp G (homVec (Pi.single i 1) 0) - 1 := by
  simp [cubeGen, Fin.append_right]

theorem toLaurent_pointGen_zero : toLaurent N (pointGen N (Fin.castAdd N 0)) = 2 * S N - 1 := by
  rw [pointGen_zero, map_sub, map_mul, map_ofNat, map_one, toLaurent_X_S]

theorem toLaurent_pointGen_one : toLaurent N (pointGen N (Fin.castAdd N 1)) = 2 * T N - 1 := by
  rw [pointGen_one, map_sub, map_mul, map_ofNat, map_one, toLaurent_X_T]

theorem toLaurent_pointGen_natAdd (i : Fin N) :
    toLaurent N (pointGen N (Fin.natAdd 2 i)) = D i - 1 := by
  rw [pointGen_natAdd, map_sub, map_one, toLaurent_X_D]

theorem baseEval_toLaurent_pointGen (i : Fin (2 + N)) :
    baseEval N (toLaurent N (pointGen N i)) = baseGen N i := by
  induction i using Fin.addCases with
  | left j =>
      fin_cases j
      · show baseEval N (toLaurent N (pointGen N (Fin.castAdd N 0))) = baseGen N (Fin.castAdd N 0)
        rw [toLaurent_pointGen_zero, baseGen_zero, map_sub, map_mul, map_ofNat, map_one,
          BaseAlgebra.baseEval_S, two_mul]
        ext <;> norm_num [BaseAlgebra.B, sub_eq_add_neg]
      · show baseEval N (toLaurent N (pointGen N (Fin.castAdd N 1))) = baseGen N (Fin.castAdd N 1)
        rw [toLaurent_pointGen_one, baseGen_one, map_sub, map_mul, map_ofNat, map_one,
          BaseAlgebra.baseEval_T, two_mul]
        ext <;> norm_num [BaseAlgebra.B, sub_eq_add_neg]
  | right i =>
      rw [toLaurent_pointGen_natAdd, baseGen_natAdd]
      exact baseEval_D_sub_one i

theorem phi_toLaurent_pointGen (G : BilinearFormMatrix (Option (Fin N))) (i : Fin (2 + N)) :
    phi G (toLaurent N (pointGen N i)) = cubeGen G i := by
  induction i using Fin.addCases with
  | left j =>
      fin_cases j
      · show phi G (toLaurent N (pointGen N (Fin.castAdd N 0))) = cubeGen G (Fin.castAdd N 0)
        rw [toLaurent_pointGen_zero, cubeGen_zero, map_sub, map_mul, map_ofNat, map_one, phi_S,
          two_mul, ← add_smul]
        norm_num
      · show phi G (toLaurent N (pointGen N (Fin.castAdd N 1))) = cubeGen G (Fin.castAdd N 1)
        rw [toLaurent_pointGen_one, cubeGen_one, map_sub, map_mul, map_ofNat, map_one, phi_T,
          two_mul, ← add_smul]
        norm_num
  | right i =>
      rw [toLaurent_pointGen_natAdd, cubeGen_natAdd, map_sub, map_one, phi_D]

/-- The image of `s^a t^b c^γ` in `A₀`. -/
def baseImage (N : ℕ) (e : Fin (2 + N) → ℕ) : BaseAlgebra N :=
  ∏ i, baseGen N i ^ e i

/-- The image of `s^a t^b c^γ` in `A_Q`. -/
def cubeImage (G : BilinearFormMatrix (Option (Fin N))) (e : Fin (2 + N) → ℕ) : CubeAlgebra G :=
  ∏ i, cubeGen G i ^ e i

theorem baseEval_toLaurent_pointMonomial (e : Fin (2 + N) → ℕ) :
    baseEval N (toLaurent N (pointMonomial N e)) = baseImage N e := by
  simp only [pointMonomial, baseImage, map_prod, map_pow, baseEval_toLaurent_pointGen]

theorem phi_toLaurent_pointMonomial (G : BilinearFormMatrix (Option (Fin N)))
    (e : Fin (2 + N) → ℕ) :
    phi G (toLaurent N (pointMonomial N e)) = cubeImage G e := by
  simp only [pointMonomial, cubeImage, map_prod, map_pow, phi_toLaurent_pointGen]

/-! ### The coordinates of `A₀` and `A_Q`, as linear maps -/

/-- The coordinate `b_k` of `A₀` (the coefficient of `B^k`), as a linear map. -/
def bCoord (N : ℕ) (k : Fin 5) : BaseAlgebra N →ₗ[ℚ] ℚ :=
  match k with
  | 0 => { toFun := BaseAlgebra.b0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
  | 1 => { toFun := BaseAlgebra.b1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
  | 2 => { toFun := BaseAlgebra.b2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
  | 3 => { toFun := BaseAlgebra.b3, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
  | 4 => { toFun := BaseAlgebra.b4, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

/-- The coordinate `c_j` of `A₀` (the coefficient of `C_j`), as a linear map. -/
def cCoord (N : ℕ) (j : Fin N) : BaseAlgebra N →ₗ[ℚ] ℚ :=
  { toFun := fun x => x.c j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

/-- The coordinate functions of `A₀` with respect to the basis `1, B, B², B³, B⁴, C₁, …, C_N`
[Lemma 2.1]. -/
def baseCoordFns (N : ℕ) : List (BaseAlgebra N →ₗ[ℚ] ℚ) :=
  (List.finRange 5).map (bCoord N) ++ (List.finRange N).map (cCoord N)

theorem bCoord_mem (k : Fin 5) : bCoord N k ∈ baseCoordFns N := by
  simp [baseCoordFns]

theorem cCoord_mem (j : Fin N) : cCoord N j ∈ baseCoordFns N := by
  simp [baseCoordFns]

/-- An element of `A₀` all of whose coordinates vanish is zero. -/
theorem baseCoordFns_eq_zero_iff (x : BaseAlgebra N) :
    (∀ κ ∈ baseCoordFns N, κ x = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact BaseAlgebra.ext (h _ (bCoord_mem 0)) (h _ (bCoord_mem 1)) (h _ (bCoord_mem 2))
      (h _ (bCoord_mem 3)) (h _ (bCoord_mem 4)) (funext fun j => h _ (cCoord_mem j))
  · rintro rfl κ _
    simp

/-- The `ℚ`-coordinate of `A_Q`, as a linear map. -/
def scalarCoord (G : BilinearFormMatrix (Option (Fin N))) : CubeAlgebra G →ₗ[ℚ] ℚ :=
  { toFun := CubeAlgebra.scalar, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

/-- The coordinate of `A_Q` along the basis vector `v_o` of `V` (`o = none` is `v₀`). -/
def vectorCoord (G : BilinearFormMatrix (Option (Fin N))) (o : Option (Fin N)) :
    CubeAlgebra G →ₗ[ℚ] ℚ :=
  { toFun := fun x => x.vector o, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

/-- The coordinate of `A_Q` along `ζ`. -/
def socleCoord (G : BilinearFormMatrix (Option (Fin N))) : CubeAlgebra G →ₗ[ℚ] ℚ :=
  { toFun := CubeAlgebra.socle, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

/-- The coordinate functions of `A_Q = ℚ ⊕ V ⊕ ℚζ` with respect to the basis
`1, v₀, v₁, …, v_N, ζ`  [§3]. -/
def cubeCoordFns (G : BilinearFormMatrix (Option (Fin N))) : List (CubeAlgebra G →ₗ[ℚ] ℚ) :=
  scalarCoord G :: (none :: (List.finRange N).map some).map (vectorCoord G) ++ [socleCoord G]

theorem scalarCoord_mem (G : BilinearFormMatrix (Option (Fin N))) :
    scalarCoord G ∈ cubeCoordFns G := by
  simp [cubeCoordFns]

theorem vectorCoord_mem (G : BilinearFormMatrix (Option (Fin N))) (o : Option (Fin N)) :
    vectorCoord G o ∈ cubeCoordFns G := by
  cases o <;> simp [cubeCoordFns]

theorem socleCoord_mem (G : BilinearFormMatrix (Option (Fin N))) :
    socleCoord G ∈ cubeCoordFns G := by
  simp [cubeCoordFns]

/-- An element of `A_Q` all of whose coordinates vanish is zero. -/
theorem cubeCoordFns_eq_zero_iff (G : BilinearFormMatrix (Option (Fin N))) (x : CubeAlgebra G) :
    (∀ κ ∈ cubeCoordFns G, κ x = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact CubeAlgebra.ext (h _ (scalarCoord_mem G)) (funext fun o => h _ (vectorCoord_mem G o))
      (h _ (socleCoord_mem G))
  · rintro rfl κ _
    simp

/-! ### The linear system and the generator list -/

/-! #### The executable computation of the images in `A_Q`

An element of `A_Q` carries its vector coordinate as a function `Option (Fin N) → ℚ`, and
compiled code re-evaluates such a function on every access; likewise the matrix `(b_ij)` of
a form produced by `homogenize` is a function that sums over the terms of the equation on
every access, and the bilinear form `polar` is a double `Finset.sum`.  A product of nine
factors would nest all of this.  The compiled code therefore stores the matrix in an array
(`matTable`), multiplies with the stored matrix (`mulWith`), stores the vector coordinate
after every multiplication (`CubeAlgebra.store`), and takes the powers `cubeGen G i ^ k`
from a table computed once (`cubePowTable`).  `rowsImpl` is the resulting implementation of
`rows`, proved equal to it in `rowsImpl_eq`; nothing is trusted. -/

/-- `x ∈ A₀` with its `C`-coordinates stored in an array.  Extensionally the identity
(`BaseAlgebra.store_eq`). -/
def BaseAlgebra.store (x : BaseAlgebra N) : BaseAlgebra N :=
  ⟨x.b0, x.b1, x.b2, x.b3, x.b4, ofArr N (Array.ofFn x.c)⟩

@[simp] theorem BaseAlgebra.store_eq (x : BaseAlgebra N) : x.store = x := by
  rcases x with ⟨b0, b1, b2, b3, b4, c⟩
  simp only [BaseAlgebra.store, BaseAlgebra.mk.injEq, true_and]
  exact ofArr_toArr c

/-- The product `∏ᵢ baseGen N i ^ e i` accumulated from the left, storing the
`C`-coordinates after every multiplication. -/
def baseImageImpl (N : ℕ) (e : Fin (2 + N) → ℕ) : BaseAlgebra N :=
  (List.finRange (2 + N)).foldl
    (fun acc i => BaseAlgebra.store (acc * BaseAlgebra.store (baseGen N i ^ e i))) 1

theorem baseImageImpl_eq (N : ℕ) (e : Fin (2 + N) → ℕ) : baseImageImpl N e = baseImage N e := by
  rw [baseImage, baseImageImpl, Fin.prod_univ_def]
  have h : ∀ (l : List (Fin (2 + N))) (a : BaseAlgebra N),
      l.foldl (fun acc i => BaseAlgebra.store (acc * BaseAlgebra.store (baseGen N i ^ e i))) a
        = a * (l.map fun i => baseGen N i ^ e i).prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons i l ih =>
        intro a
        rw [List.foldl_cons, ih, BaseAlgebra.store_eq, BaseAlgebra.store_eq, List.map_cons,
          List.prod_cons, mul_assoc]
  rw [h, one_mul]

/-- `x ∈ A_Q` with its vector coordinate stored in an array: the coordinates at
`v₁, …, v_N` in an array, the coordinate at `v₀` separately.  Extensionally the identity
(`CubeAlgebra.store_eq`). -/
def CubeAlgebra.store {G : BilinearFormMatrix (Option (Fin N))} (x : CubeAlgebra G) :
    CubeAlgebra G :=
  ⟨x.scalar, homVec (ofArr N (Array.ofFn fun i => x.vector (some i))) (x.vector none), x.socle⟩

@[simp] theorem CubeAlgebra.store_eq {G : BilinearFormMatrix (Option (Fin N))}
    (x : CubeAlgebra G) : x.store = x := by
  rcases x with ⟨r, v, s⟩
  simp only [CubeAlgebra.store, CubeAlgebra.mk.injEq, true_and, and_true]
  funext o
  cases o with
  | none => rfl
  | some i =>
      show ofArr N (Array.ofFn fun i => v (some i)) i = v (some i)
      rw [show (Array.ofFn fun i => v (some i)) = toArr fun i => v (some i) from rfl, ofArr_toArr]

/-- The index `Option (Fin N) ≃ Fin (N+1)`: `none ↦ 0`, `some i ↦ i + 1`. -/
def optOf : Fin (N + 1) → Option (Fin N) := Fin.cases none some

theorem sum_optOf (f : Option (Fin N) → ℚ) : ∑ i : Fin (N + 1), f (optOf i) = ∑ o, f o := by
  rw [Fin.sum_univ_succ, Fintype.sum_option]
  simp [optOf]

/-- The matrix `(b_ij)` of `G` as an array of rows, indexed by `optOf`. -/
def matTable (G : BilinearFormMatrix (Option (Fin N))) : Array (Array ℚ) :=
  Array.ofFn fun i : Fin (N + 1) => Array.ofFn fun j : Fin (N + 1) => G.b (optOf i) (optOf j)

theorem matTable_getD (G : BilinearFormMatrix (Option (Fin N))) (i j : Fin (N + 1)) :
    ((matTable G).getD i #[]).getD j 0 = G.b (optOf i) (optOf j) := by
  have hi : (i : ℕ) < (matTable G).size := by simp [matTable]; omega
  have hrow : (matTable G).getD i #[] = Array.ofFn fun j : Fin (N + 1) => G.b (optOf i) (optOf j) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp [matTable]
  rw [hrow, show (Array.ofFn fun j : Fin (N + 1) => G.b (optOf i) (optOf j)) = toArr _ from rfl, getD_toArr]

/-- `B(x, y)` computed from the stored matrix. -/
def polarWith (tbl : Array (Array ℚ)) (x y : Option (Fin N) → ℚ) : ℚ :=
  (List.ofFn fun i : Fin (N + 1) =>
    (List.ofFn fun j : Fin (N + 1) => x (optOf i) * (tbl.getD i #[]).getD j 0 * y (optOf j)).sum).sum

theorem polarWith_matTable (G : BilinearFormMatrix (Option (Fin N))) (x y : Option (Fin N) → ℚ) :
    polarWith (matTable G) x y = G.polar x y := by
  classical
  rw [G.polar_eq_toBilin', Matrix.toBilin'_apply]
  change polarWith (matTable G) x y = ∑ o, ∑ o', x o * G.b o o' * y o'
  simp only [polarWith, List.sum_ofFn, matTable_getD]
  rw [sum_optOf fun o => ∑ j : Fin (N + 1), x o * G.b o (optOf j) * y (optOf j)]
  exact Finset.sum_congr rfl fun o _ => sum_optOf fun o' => x o * G.b o o' * y o'

/-- Multiplication in `A_Q` with `B(x, y)` computed from the stored matrix. -/
def mulWith {G : BilinearFormMatrix (Option (Fin N))} (tbl : Array (Array ℚ)) (x y : CubeAlgebra G) :
    CubeAlgebra G :=
  ⟨x.scalar * y.scalar, x.scalar • y.vector + y.scalar • x.vector,
    x.scalar * y.socle + y.scalar * x.socle + polarWith tbl x.vector y.vector⟩

theorem mulWith_matTable (G : BilinearFormMatrix (Option (Fin N))) (x y : CubeAlgebra G) :
    mulWith (matTable G) x y = x * y := by
  rw [mulWith, polarWith_matTable]
  rfl


/-- The power `x ^ k` computed with the stored matrix, storing the vector coordinate after
every multiplication. -/
def powWith {G : BilinearFormMatrix (Option (Fin N))} (tbl : Array (Array ℚ)) (x : CubeAlgebra G) :
    ℕ → CubeAlgebra G
  | 0 => 1
  | k + 1 => CubeAlgebra.store (mulWith tbl (powWith tbl x k) x)

theorem powWith_matTable (G : BilinearFormMatrix (Option (Fin N))) (x : CubeAlgebra G) (k : ℕ) :
    powWith (matTable G) x k = x ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powWith, CubeAlgebra.store_eq, mulWith_matTable, ih, pow_succ]

/-- The table of the powers `cubeGen G i ^ k`, `k = 0, …, 4` (the degrees occurring in
`lowMonomials`), computed with the stored matrix `tbl`. -/
def cubePowTable (G : BilinearFormMatrix (Option (Fin N))) (tbl : Array (Array ℚ)) :
    Array (Array (CubeAlgebra G)) :=
  Array.ofFn fun i : Fin (2 + N) => Array.ofFn fun k : Fin 5 => powWith tbl (cubeGen G i) k

/-- Look up `cubeGen G i ^ k` in the table, computing it directly when `k ≥ 5`. -/
def cubePow (G : BilinearFormMatrix (Option (Fin N))) (pows : Array (Array (CubeAlgebra G)))
    (i : Fin (2 + N)) (k : ℕ) : CubeAlgebra G :=
  if k < 5 then (pows.getD i #[]).getD k (cubeGen G i ^ k) else cubeGen G i ^ k

theorem cubePow_cubePowTable (G : BilinearFormMatrix (Option (Fin N))) (i : Fin (2 + N)) (k : ℕ) :
    cubePow G (cubePowTable G (matTable G)) i k = cubeGen G i ^ k := by
  rw [cubePow]
  split_ifs with h
  · have hi : (i : ℕ) < (cubePowTable G (matTable G)).size := by simp [cubePowTable]
    have hrow : (cubePowTable G (matTable G)).getD i #[]
        = Array.ofFn fun k : Fin 5 => powWith (matTable G) (cubeGen G i) k := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      simp [cubePowTable]
    rw [hrow]
    have hk : k < (Array.ofFn fun k : Fin 5 => powWith (matTable G) (cubeGen G i) k).size := by
      simpa using h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simp [powWith_matTable]
  · rfl

/-- The product `∏ᵢ pows i (e i)` accumulated from the left with the stored matrix `tbl`,
storing the vector coordinate after every multiplication; `pows i k` is meant to be
`cubeGen G i ^ k`. -/
def cubeImageWith {G : BilinearFormMatrix (Option (Fin N))} (tbl : Array (Array ℚ))
    (pows : Fin (2 + N) → ℕ → CubeAlgebra G) (e : Fin (2 + N) → ℕ) : CubeAlgebra G :=
  (List.finRange (2 + N)).foldl (fun acc i => CubeAlgebra.store (mulWith tbl acc (pows i (e i)))) 1

theorem cubeImageWith_eq (G : BilinearFormMatrix (Option (Fin N)))
    {pows : Fin (2 + N) → ℕ → CubeAlgebra G} (hpows : ∀ i k, pows i k = cubeGen G i ^ k)
    (e : Fin (2 + N) → ℕ) : cubeImageWith (matTable G) pows e = cubeImage G e := by
  rw [cubeImage, cubeImageWith, Fin.prod_univ_def]
  have h : ∀ (l : List (Fin (2 + N))) (a : CubeAlgebra G),
      l.foldl (fun acc i => CubeAlgebra.store (mulWith (matTable G) acc (pows i (e i)))) a
        = a * (l.map fun i => cubeGen G i ^ e i).prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons i l ih =>
        intro a
        rw [List.foldl_cons, ih, CubeAlgebra.store_eq, mulWith_matTable, List.map_cons,
          List.prod_cons, mul_assoc, hpows]
  rw [h, one_mul]

/-- The rows of the linear system describing `I_P ∩ W₄`: one row for each coordinate of
`A₀` and of each `A_{Q_i}`, whose `j`-th entry is that coordinate of the image of the
`j`-th product `s^a t^b c^γ` of degree `≤ 4`.  The monomial list and the images are
computed once and stored in arrays.  Compiled code runs `rowsImpl`, proved equal in
`rowsImpl_eq`. -/
def rowsImpl {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    List (Fin (lowMonomials N).length → ℚ) :=
  let mons : Array (Fin (2 + N) → ℕ) := (lowMonomials N).toArray
  let baseImgs : Array (BaseAlgebra N) := mons.map (baseImageImpl N)
  (baseCoordFns N).map (fun κ => materialize fun j =>
      κ (baseImgs[j.val]'(by simp [baseImgs, mons])))
    ++ (List.finRange M).flatMap fun i =>
      let tbl := matTable (Q i)
      let pows := cubePowTable (Q i) tbl
      let cubeImgs : Array (CubeAlgebra (Q i)) :=
        mons.map (cubeImageWith tbl (cubePow (Q i) pows))
      (cubeCoordFns (Q i)).map (fun κ => materialize fun j =>
        κ (cubeImgs[j.val]'(by simp [cubeImgs, mons])))

/-- The rows of the linear system describing `I_P ∩ W₄`: one row for each coordinate of
`A₀` and of each `A_{Q_i}`, whose `j`-th entry is that coordinate of the image of the
`j`-th product `s^a t^b c^γ` of degree `≤ 4`. -/
@[implemented_by rowsImpl]
def rows {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    List (Fin (lowMonomials N).length → ℚ) :=
  let mons : Array (Fin (2 + N) → ℕ) := (lowMonomials N).toArray
  let baseImgs : Array (BaseAlgebra N) := mons.map (baseImage N)
  (baseCoordFns N).map (fun κ => materialize fun j =>
      κ (baseImgs[j.val]'(by simp [baseImgs, mons])))
    ++ (List.finRange M).flatMap fun i =>
      let cubeImgs : Array (CubeAlgebra (Q i)) := mons.map (cubeImage (Q i))
      (cubeCoordFns (Q i)).map (fun κ => materialize fun j =>
        κ (cubeImgs[j.val]'(by simp [cubeImgs, mons])))

/-- The compiled implementation computes exactly `rows`. -/
theorem rowsImpl_eq {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    rowsImpl Q = rows Q := by
  have h : ∀ i : Fin M, (lowMonomials N).toArray.map
        (cubeImageWith (matTable (Q i)) (cubePow (Q i) (cubePowTable (Q i) (matTable (Q i)))))
      = (lowMonomials N).toArray.map (cubeImage (Q i)) := by
    intro i
    exact Array.map_congr_left fun e _ =>
      cubeImageWith_eq (Q i) (cubePow_cubePowTable (Q i)) e
  have hb : (lowMonomials N).toArray.map (baseImageImpl N)
      = (lowMonomials N).toArray.map (baseImage N) :=
    Array.map_congr_left fun e _ => baseImageImpl_eq N e
  simp only [rowsImpl, rows, h, hb]

/-- The polynomial `∑ v_j s^{a_j} t^{b_j} c^{γ_j}` of a coefficient vector `v`. -/
noncomputable def lowCombination (N : ℕ) :
    (Fin (lowMonomials N).length → ℚ) →ₗ[ℚ] MvPolynomial (Var N) ℚ :=
  Fintype.linearCombination ℚ fun j => pointMonomial N (lowMonomial N j)

theorem lowCombination_apply (v : Fin (lowMonomials N).length → ℚ) :
    lowCombination N v = ∑ j, v j • pointMonomial N (lowMonomial N j) := by
  rw [lowCombination, Fintype.linearCombination_apply]

/-- The output polynomial of a coefficient vector. -/
def kernelPoly (v : Fin (lowMonomials N).length → ℚ) : PointPoly N :=
  ((List.finRange _).map fun j => (v j, lowMonomial N j)).filter fun t => t.1 ≠ 0

/-- `kernelPoly` with the monomial list supplied as an array (computed once), for the
executable definition of `generators`; terms with coefficient `0` are dropped. -/
def kernelPolyWith (mons : Array (Fin (2 + N) → ℕ)) (hm : mons.size = (lowMonomials N).length)
    (v : Fin (lowMonomials N).length → ℚ) : PointPoly N :=
  ((List.finRange _).map fun j => (v j, mons[j.val]'(by rw [hm]; exact j.isLt))).filter
    fun t => t.1 ≠ 0

theorem kernelPolyWith_toArray (v : Fin (lowMonomials N).length → ℚ) :
    kernelPolyWith (lowMonomials N).toArray (by simp) v = kernelPoly v := by
  simp [kernelPolyWith, kernelPoly, lowMonomial, List.get_eq_getElem]

/-- Dropping the terms with coefficient `0` does not change the polynomial. -/
theorem toPoly_filter_ne_zero (l : PointPoly N) :
    PointPoly.toPoly (l.filter fun t => t.1 ≠ 0) = l.toPoly := by
  induction l with
  | nil => rfl
  | cons t l ih =>
      by_cases h : t.1 = 0
      · rw [List.filter_cons_of_neg (by simp [h]), ih]
        show PointPoly.toPoly l = PointPoly.toPoly (t :: l)
        rw [PointPoly.toPoly, PointPoly.toPoly, List.map_cons, List.sum_cons, h, zero_smul,
          zero_add]
      · rw [List.filter_cons_of_pos (by simp [h]), PointPoly.toPoly, PointPoly.toPoly,
          List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
        exact congrArg _ ih

theorem toPoly_kernelPoly (v : Fin (lowMonomials N).length → ℚ) :
    (kernelPoly v).toPoly = lowCombination N v := by
  rw [kernelPoly, toPoly_filter_ne_zero]
  simp [PointPoly.toPoly, lowCombination_apply, Fin.sum_univ_def, List.map_map,
    Function.comp_def]

/-- **The generator list of `I_P`**: the products `s^a t^b c^γ` of degree five (which
generate `𝔪⁵`) and the polynomials of degree `≤ 4` in `I_P`, computed by linear algebra
[Theorem 4.5]. -/
def generators {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) : List (PointPoly N) :=
  (exponentsEQ (2 + N) 5).map (fun e => [(1, e)])
    ++ (kernelBasis (rows Q)).map (kernelPolyWith (lowMonomials N).toArray (by simp))

/-- The ideal generated by the output list. -/
noncomputable def generatedIdeal {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    Ideal (MvPolynomial (Var N) ℚ) :=
  Ideal.span {g | ∃ l ∈ generators Q, g = l.toPoly}

/-! ### Correctness -/

/-- Membership of an element of `W₄` in `I_P`, in coordinates. -/
theorem lowCombination_mem_iff_coords {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (v : Fin (lowMonomials N).length → ℚ) :
    lowCombination N v ∈ polyReductionIdeal Q ↔
      (∀ κ ∈ baseCoordFns N, κ (∑ j, v j • baseImage N (lowMonomial N j)) = 0)
      ∧ ∀ i, ∀ κ ∈ cubeCoordFns (Q i), κ (∑ j, v j • cubeImage (Q i) (lowMonomial N j)) = 0 := by
  have hb : baseEval N (toLaurent N (lowCombination N v))
      = ∑ j, v j • baseImage N (lowMonomial N j) := by
    simp only [lowCombination_apply, map_sum, map_smul, baseEval_toLaurent_pointMonomial]
  have hc : ∀ i, phi (Q i) (toLaurent N (lowCombination N v))
      = ∑ j, v j • cubeImage (Q i) (lowMonomial N j) := by
    intro i
    simp only [lowCombination_apply, map_sum, map_smul, phi_toLaurent_pointMonomial]
  rw [mem_polyReductionIdeal_iff, mem_reductionIdeal_iff, mem_baseIdeal_iff, hb]
  simp only [RingHom.mem_ker, hc]
  exact and_congr (baseCoordFns_eq_zero_iff _).symm
    (forall_congr' fun i => (cubeCoordFns_eq_zero_iff _ _).symm)

/-- An element of `W₄` with coefficient vector `v` lies in `I_P` iff `v` solves the linear
system `rows Q`. -/
theorem lowCombination_mem_iff {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    (v : Fin (lowMonomials N).length → ℚ) :
    lowCombination N v ∈ polyReductionIdeal Q ↔ ∀ r ∈ rows Q, ∑ j, r j * v j = 0 := by
  rw [lowCombination_mem_iff_coords]
  simp only [map_sum, map_smul, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩ r hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
      simpa [mul_comm, materialize_apply, lowMonomial, List.get_eq_getElem] using h1 κ hκ
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.mp h
      obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h
      simpa [mul_comm, materialize_apply, lowMonomial, List.get_eq_getElem] using h2 i κ hκ
  · intro h
    refine ⟨fun κ hκ => ?_, fun i κ hκ => ?_⟩
    · simpa [mul_comm, materialize_apply, lowMonomial, List.get_eq_getElem] using
        h _ (List.mem_append_left _ (List.mem_map_of_mem hκ))
    · simpa [mul_comm, materialize_apply, lowMonomial, List.get_eq_getElem] using
        h _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map_of_mem hκ⟩))

/-- The ideal generated by the products `s^a t^b c^γ` of degree exactly `k`. -/
noncomputable def degreeSpan (N k : ℕ) : Ideal (MvPolynomial (Var N) ℚ) :=
  Ideal.span {g | ∃ e ∈ exponentsEQ (2 + N) k, g = pointMonomial N e}

theorem pointMonomial_add_single (e : Fin (2 + N) → ℕ) (i : Fin (2 + N)) :
    pointMonomial N (e + Pi.single i 1) = pointMonomial N e * pointGen N i := by
  simp only [pointMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

theorem degreeSpan_mul_le (k : ℕ) :
    degreeSpan N k * Ideal.span (Set.range (pointGen N)) ≤ degreeSpan N (k + 1) := by
  unfold degreeSpan
  rw [Ideal.span_mul_span']
  apply Ideal.span_le.mpr
  rintro x ⟨g, hg, h, hh, rfl⟩
  obtain ⟨e, he, rfl⟩ := hg
  obtain ⟨i, rfl⟩ := hh
  refine Ideal.subset_span ⟨e + Pi.single i 1, mem_exponentsEQ.mpr ?_,
    (pointMonomial_add_single e i).symm⟩
  simp [Finset.sum_add_distrib, mem_exponentsEQ.mp he, Finset.sum_pi_single']

/-- `𝔪^k` is generated by the products of degree `k`. -/
theorem pow_le_degreeSpan (k : ℕ) :
    Ideal.span (Set.range (pointGen N)) ^ k ≤ degreeSpan N k := by
  induction k with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      exact Ideal.subset_span ⟨0, mem_exponentsEQ.mpr (by simp), by simp [pointMonomial]⟩
  | succ k ih =>
      rw [pow_succ]
      exact le_trans (Ideal.mul_mono_left ih) (degreeSpan_mul_le k)

theorem degreeSpan_five_le_generatedIdeal {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    degreeSpan N 5 ≤ generatedIdeal Q := by
  rw [degreeSpan, Ideal.span_le]
  rintro g ⟨e, he, rfl⟩
  refine Ideal.subset_span ⟨[(1, e)], List.mem_append_left _ (List.mem_map_of_mem he), ?_⟩
  simp

/-- **Correctness of the generator list**: the ideal generated by `generators Q` is `I_P`
[Theorem 4.5]. -/
theorem generatedIdeal_eq {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N))) :
    generatedIdeal Q = polyReductionIdeal Q := by
  have hpow := span_pointGen_pow_five_le Q
  apply le_antisymm
  · rw [generatedIdeal, Ideal.span_le]
    rintro g ⟨l, hl, rfl⟩
    rcases List.mem_append.mp hl with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      rw [PointPoly.toPoly_single, one_smul]
      exact hpow (pointMonomial_mem_pow_five e (mem_exponentsEQ.mp he).ge)
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
      rw [kernelPolyWith_toArray, toPoly_kernelPoly, SetLike.mem_coe, lowCombination_mem_iff]
      exact kernelBasis_mem _ hv
  · intro f hf
    obtain ⟨g, hg, hfg⟩ := exists_lowDegree_sub_mem_pow_five f
    have hgI : g ∈ polyReductionIdeal Q := by
      have := Ideal.sub_mem _ hf (hpow hfg)
      simpa using this
    rw [show f = (f - g) + g by ring]
    refine Ideal.add_mem _ (degreeSpan_five_le_generatedIdeal Q (pow_le_degreeSpan 5 hfg)) ?_
    obtain ⟨v, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hg
    rw [← lowCombination_apply] at hgI ⊢
    have hv : v ∈ Submodule.span ℚ {w | w ∈ kernelBasis (rows Q)} :=
      mem_span_kernelBasis_of_forall _ ((lowCombination_mem_iff Q v).mp hgI)
    have hmap : lowCombination N v ∈ Submodule.map (lowCombination N)
        (Submodule.span ℚ {w | w ∈ kernelBasis (rows Q)}) :=
      Submodule.mem_map_of_mem hv
    rw [Submodule.map_span] at hmap
    have hle : Submodule.span ℚ (lowCombination N '' {w | w ∈ kernelBasis (rows Q)})
        ≤ (generatedIdeal Q).restrictScalars ℚ := by
      rw [Submodule.span_le]
      rintro x ⟨w, hw, rfl⟩
      exact Ideal.subset_span ⟨kernelPolyWith (lowMonomials N).toArray (by simp) w,
        List.mem_append_right _ (List.mem_map_of_mem hw),
        by rw [kernelPolyWith_toArray, toPoly_kernelPoly]⟩
    exact hle hmap

/-- Every generator has degree at most five in the coordinates `s, t, c`: each term of the
`PointPoly` has exponent sum `≤ 5`. -/
theorem generators_degree_le {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    {l : PointPoly N} (hl : l ∈ generators Q) : ∀ t ∈ l, ∑ i, t.2 i ≤ 5 := by
  intro t ht
  rcases List.mem_append.mp hl with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    rw [List.mem_singleton] at ht
    subst ht
    exact (mem_exponentsEQ.mp he).le
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
    rw [kernelPolyWith_toArray, kernelPoly, List.mem_filter] at ht
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht.1
    exact le_trans (mem_lowMonomials.mp (List.get_mem _ _)) (by norm_num)

/-! ### Total degree in `S, T, D` -/

/-- The coordinates `s = 2S−1`, `t = 2T−1`, `c_i = D_i − 1` have total degree `1`. -/
theorem totalDegree_pointGen_le (i : Fin (2 + N)) : (pointGen N i).totalDegree ≤ 1 := by
  have hX : ∀ (v : Var N) (c : ℚ),
      (C c * X v - 1 : MvPolynomial (Var N) ℚ).totalDegree ≤ 1 := by
    intro v c
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
    · simp
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · simpa [show (2 : MvPolynomial (Var N) ℚ) = C 2 from rfl] using hX Var.S 2
    · simpa [show (2 : MvPolynomial (Var N) ℚ) = C 2 from rfl] using hX Var.T 2
  · simpa using hX (Var.D j) 1

/-- The product `s^a t^b c^γ` has total degree at most `a + b + |γ|`. -/
theorem totalDegree_pointMonomial_le (e : Fin (2 + N) → ℕ) :
    (pointMonomial N e).totalDegree ≤ ∑ i, e i := by
  rw [pointMonomial]
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc (pointGen N i ^ e i).totalDegree ≤ e i * (pointGen N i).totalDegree :=
        totalDegree_pow _ _
    _ ≤ e i * 1 := Nat.mul_le_mul_left _ (totalDegree_pointGen_le i)
    _ = e i := Nat.mul_one _

/-- The change of coordinates preserves total degree: a `PointPoly` all of whose terms have
exponent sum `≤ d` denotes a polynomial of total degree `≤ d` in `S, T, D`. -/
theorem totalDegree_toPoly_le {l : PointPoly N} {d : ℕ} (h : ∀ t ∈ l, ∑ i, t.2 i ≤ d) :
    l.toPoly.totalDegree ≤ d := by
  rw [PointPoly.toPoly]
  induction l with
  | nil => simp
  | cons t l ih =>
      rw [List.map_cons, List.sum_cons]
      refine (totalDegree_add _ _).trans
        (max_le ?_ (ih fun t ht => h t (List.mem_cons_of_mem _ ht)))
      exact (totalDegree_smul_le _ _).trans
        ((totalDegree_pointMonomial_le _).trans (h t List.mem_cons_self))

/-- **Every generator of `I_P` has total degree at most five** [Theorem 4.5 and Corollary 5.1]. -/
theorem generators_totalDegree_le {M : ℕ} (Q : Fin M → BilinearFormMatrix (Option (Fin N)))
    {l : PointPoly N} (hl : l ∈ generators Q) : l.toPoly.totalDegree ≤ 5 :=
  totalDegree_toPoly_le (generators_degree_le Q hl)

end Trinomial
