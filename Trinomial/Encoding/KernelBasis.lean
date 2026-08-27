import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Linear algebra on the residues

[proof of Corollary 4.6].  The first paragraph of that proof reduces
the problems (A)–(C) to the halting problem: the finite exponent sets can be enumerated
effectively, and "linear algebra on the residues" decides whether the ideal contains a
nonzero polynomial with support contained in, or equal to, a given set.  This file
supplies the linear algebra in executable form.  A finite list `rows` of vectors in
`Fin n → ℚ` encodes the linear conditions `x ↦ ∑ j, r j * x j` with `r ∈ rows`, and
`kernelBasis rows` computes a finite spanning set of their common kernel

  `{x : Fin n → ℚ | ∀ r ∈ rows, ∑ j, r j * x j = 0}`.

The specification is `mem_span_kernelBasis_iff`, with the one-directional consequences
`kernelBasis_mem` and `mem_span_kernelBasis_of_forall`.

The definitions `eliminate` and `kernelBasis` on `Fin n → ℚ` are the reference
implementation used in all proofs.  Compiled code runs `kernelBasisImpl` instead
(`implemented_by`), the same algorithm on vectors stored as `Array ℚ`, so that a coordinate
is computed once and not on every access; `kernelBasisImpl_eq` proves that the two
functions are equal, so nothing is trusted.

The algorithm starts from the standard basis of `Fin n → ℚ` and processes one linear
condition at a time (`eliminate`).  For the current spanning set `vs` and the condition
`r`, write `a v = ∑ j, r j * v j`.  Elements `v` with `a v = 0` are kept until the first
`v₀` with `a v₀ ≠ 0` appears.  That `v₀` is dropped and every later `v` is replaced by
`v - (a v / a v₀) • v₀`, which lies in the span of the old list and satisfies `a = 0`.
The invariant `span (eliminate r vs) = span vs ⊓ ker a` is `span_eliminate`.  The output
is a spanning set, not necessarily a basis: linear independence is neither claimed nor
needed, and repetitions in the list are harmless.
-/

set_option autoImplicit false

namespace Trinomial

variable {n : ℕ}

/-- The linear condition encoded by the row `r`, evaluated at `x`: `∑ j, r j * x j`.
This is the plain function used by the executable algorithm. -/
def rowEval (r x : Fin n → ℚ) : ℚ := ∑ j, r j * x j

lemma rowEval_add (r x y : Fin n → ℚ) : rowEval r (x + y) = rowEval r x + rowEval r y := by
  simp [rowEval, mul_add, Finset.sum_add_distrib]

lemma rowEval_smul (r : Fin n → ℚ) (c : ℚ) (x : Fin n → ℚ) :
    rowEval r (c • x) = c * rowEval r x := by
  simp [rowEval, Finset.mul_sum, mul_left_comm]

lemma rowEval_sub (r x y : Fin n → ℚ) : rowEval r (x - y) = rowEval r x - rowEval r y := by
  simp [rowEval, mul_sub, Finset.sum_sub_distrib]

/-- The linear condition encoded by the row `r`, as a linear functional on `Fin n → ℚ`.
Its kernel is the solution space of the condition; this is the form used by the
specification. -/
def rowForm (r : Fin n → ℚ) : (Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun := rowEval r
  map_add' := rowEval_add r
  map_smul' := rowEval_smul r

@[simp] lemma rowForm_apply (r x : Fin n → ℚ) : rowForm r x = ∑ j, r j * x j := rfl

/-- Store the values of a vector in an array.  Extensionally the identity
(`materialize_eq`); used by `Trinomial/Encoding/Generators.lean` when the rows of the
linear system are formed. -/
def materialize (v : Fin n → ℚ) : Fin n → ℚ :=
  let a : Array ℚ := Array.ofFn v
  fun j => a[j.val]'(by simp [a])

@[simp] theorem materialize_apply (v : Fin n → ℚ) (j : Fin n) : materialize v j = v j := by
  simp [materialize]

@[simp] theorem materialize_eq (v : Fin n → ℚ) : materialize v = v :=
  funext (materialize_apply v)

/-! ### The executable implementation on arrays

A vector `v : Fin n → ℚ` is a function, and compiled code recomputes `v j` on every access;
the elimination steps nest such recomputations.  The implementation therefore stores
vectors as arrays of length `n`: `toArr` and `ofArr` convert, `rowEvalA` and `subSmulA` are
the two operations of the algorithm, and `eliminateA`, `kernelBasisA` are the algorithm
itself.  `kernelBasisA_map_toArr` shows that it computes, array by array, the same lists as
the reference definitions below. -/

/-- A vector of `ℚⁿ` as an array. -/
def toArr (v : Fin n → ℚ) : Array ℚ := Array.ofFn v

/-- The vector of `ℚⁿ` stored in an array (entries beyond the size read as `0`). -/
def ofArr (n : ℕ) (a : Array ℚ) : Fin n → ℚ := fun j => a.getD j 0

@[simp] theorem getD_toArr (v : Fin n → ℚ) (j : Fin n) : (toArr v).getD j 0 = v j := by
  have h : (j : ℕ) < (toArr v).size := by simp [toArr]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  simp [toArr]

@[simp] theorem ofArr_toArr (v : Fin n → ℚ) : ofArr n (toArr v) = v := by
  funext j
  rw [ofArr, getD_toArr]

/-- `rowEval` on arrays. -/
def rowEvalA (n : ℕ) (r x : Array ℚ) : ℚ :=
  (List.ofFn fun j : Fin n => r.getD j 0 * x.getD j 0).sum

theorem rowEvalA_toArr (r x : Fin n → ℚ) : rowEvalA n (toArr r) (toArr x) = rowEval r x := by
  simp only [rowEvalA, rowEval, List.sum_ofFn, getD_toArr]

/-- `w - c • v` on arrays. -/
def subSmulA (n : ℕ) (w v : Array ℚ) (c : ℚ) : Array ℚ :=
  Array.ofFn fun j : Fin n => w.getD j 0 - c * v.getD j 0

theorem subSmulA_toArr (w v : Fin n → ℚ) (c : ℚ) :
    subSmulA n (toArr w) (toArr v) c = toArr (w - c • v) := by
  rw [subSmulA, toArr]
  congr 1
  funext j
  rw [show (Array.ofFn w).getD (j : ℕ) 0 = (toArr w).getD j 0 from rfl, getD_toArr, getD_toArr]
  rfl

/-- `eliminate` on arrays. -/
def eliminateA (n : ℕ) (r : Array ℚ) : List (Array ℚ) → List (Array ℚ)
  | [] => []
  | v :: vs =>
    if rowEvalA n r v = 0 then v :: eliminateA n r vs
    else vs.map fun w => subSmulA n w v (rowEvalA n r w / rowEvalA n r v)

/-- `kernelBasis` on arrays. -/
def kernelBasisA (n : ℕ) : List (Array ℚ) → List (Array ℚ)
  | [] => (List.finRange n).map fun j => toArr (Pi.single j 1)
  | r :: rows => eliminateA n r (kernelBasisA n rows)

/-- The compiled implementation of `kernelBasis`: convert to arrays, run `kernelBasisA`,
convert back. -/
def kernelBasisImpl (rows : List (Fin n → ℚ)) : List (Fin n → ℚ) :=
  (kernelBasisA n (rows.map toArr)).map (ofArr n)

/-! ### The reference definitions -/

/-- One step of the algorithm: the spanning set `eliminate r vs` of
`span vs ⊓ ker (rowForm r)`.  Elements `v` with `rowEval r v = 0` are kept until the
first `v` with `rowEval r v ≠ 0` appears; that `v` is dropped and every later `w` is
replaced by `w - (rowEval r w / rowEval r v) • v`. -/
def eliminate (r : Fin n → ℚ) : List (Fin n → ℚ) → List (Fin n → ℚ)
  | [] => []
  | v :: vs =>
    if rowEval r v = 0 then v :: eliminate r vs
    else vs.map fun w => w - (rowEval r w / rowEval r v) • v

/-- Spanning set of `{x : Fin n → ℚ | ∀ r ∈ rows, ∑ j, r j * x j = 0}`, computed one
linear condition at a time: the standard basis for no conditions, and `eliminate r`
applied to the spanning set for `rows` when the condition `r` is added.  Compiled code
runs `kernelBasisImpl`, proved equal in `kernelBasisImpl_eq`. -/
@[implemented_by kernelBasisImpl]
def kernelBasis : List (Fin n → ℚ) → List (Fin n → ℚ)
  | [] => (List.finRange n).map fun j => Pi.single j 1
  | r :: rows => eliminate r (kernelBasis rows)

theorem eliminateA_map_toArr (r : Fin n → ℚ) (vs : List (Fin n → ℚ)) :
    eliminateA n (toArr r) (vs.map toArr) = (eliminate r vs).map toArr := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [List.map_cons, eliminateA, eliminate, rowEvalA_toArr]
      split_ifs
      · rw [List.map_cons, ih]
      · rw [List.map_map, List.map_map]
        refine List.map_congr_left fun w _ => ?_
        simp only [Function.comp_apply, rowEvalA_toArr, subSmulA_toArr]

theorem kernelBasisA_map_toArr (rows : List (Fin n → ℚ)) :
    kernelBasisA n (rows.map toArr) = (kernelBasis rows).map toArr := by
  induction rows with
  | nil => simp [kernelBasisA, kernelBasis, List.map_map, Function.comp_def]
  | cons r rows ih => rw [List.map_cons, kernelBasisA, kernelBasis, ih, eliminateA_map_toArr]

/-- The compiled implementation computes exactly the reference function. -/
theorem kernelBasisImpl_eq (rows : List (Fin n → ℚ)) : kernelBasisImpl rows = kernelBasis rows := by
  rw [kernelBasisImpl, kernelBasisA_map_toArr, List.map_map]
  simp [Function.comp_def]

/-! ### The single elimination step -/

/-- The substitution `w ↦ w - (rowEval r w / rowEval r v) • v` of the elimination step,
as a linear map in `w`. -/
def elimMap (r v : Fin n → ℚ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun w := w - (rowEval r w / rowEval r v) • v
  map_add' x y := by
    simp only [rowEval_add, add_div, add_smul]
    abel
  map_smul' c x := by
    simp only [rowEval_smul, RingHom.id_apply, mul_div_assoc, mul_smul, smul_sub]

@[simp] lemma elimMap_apply (r v w : Fin n → ℚ) :
    elimMap r v w = w - (rowEval r w / rowEval r v) • v := rfl

/-- Every vector produced by the elimination step satisfies the condition `r`. -/
lemma rowEval_elimMap {r v : Fin n → ℚ} (hv : rowEval r v ≠ 0) (w : Fin n → ℚ) :
    rowEval r (elimMap r v w) = 0 := by
  rw [elimMap_apply, rowEval_sub, rowEval_smul, div_mul_cancel₀ _ hv, sub_self]

/-- The dropped vector `v` is sent to `0` by the elimination step. -/
lemma elimMap_self {r v : Fin n → ℚ} (hv : rowEval r v ≠ 0) : elimMap r v v = 0 := by
  rw [elimMap_apply, div_self hv, one_smul, sub_self]

/-- A vector satisfying the condition `r` is fixed by the elimination step. -/
lemma elimMap_of_rowEval_eq_zero {r w : Fin n → ℚ} (v : Fin n → ℚ) (hw : rowEval r w = 0) :
    elimMap r v w = w := by
  rw [elimMap_apply, hw, zero_div, zero_smul, sub_zero]

lemma setOf_mem_cons (v : Fin n → ℚ) (l : List (Fin n → ℚ)) :
    {w | w ∈ v :: l} = insert v {w | w ∈ l} := by
  ext w
  simp

/-- The invariant of the algorithm: one elimination step cuts the span with the kernel
of the condition `r`. -/
theorem span_eliminate (r : Fin n → ℚ) (vs : List (Fin n → ℚ)) :
    Submodule.span ℚ {w | w ∈ eliminate r vs} =
      Submodule.span ℚ {w | w ∈ vs} ⊓ LinearMap.ker (rowForm r) := by
  induction vs with
  | nil => simp [eliminate]
  | cons v vs ih =>
    by_cases hv : rowEval r v = 0
    · rw [eliminate, if_pos hv, setOf_mem_cons, setOf_mem_cons, Submodule.span_insert,
        Submodule.span_insert, ih]
      have hvk : (ℚ ∙ v) ≤ LinearMap.ker (rowForm r) :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_ker.mpr hv)
      exact (sup_inf_assoc_of_le _ hvk).symm
    · rw [eliminate, if_neg hv]
      have himg : {w | w ∈ vs.map fun w => w - (rowEval r w / rowEval r v) • v}
          = elimMap r v '' {w | w ∈ vs} := by
        ext w
        simp [List.mem_map]
      rw [himg, Submodule.span_image]
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        intro w hw
        refine Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_ker.mpr ?_⟩)
        · rw [elimMap_apply]
          exact Submodule.sub_mem _ (Submodule.subset_span (List.mem_cons_of_mem _ hw))
            (Submodule.smul_mem _ _ (Submodule.subset_span (List.mem_cons_self ..)))
        · exact rowEval_elimMap hv w
      · intro x hx
        obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.mp hx
        rw [setOf_mem_cons, Submodule.mem_span_insert] at hx₁
        obtain ⟨c, z, hz, rfl⟩ := hx₁
        have hfix : elimMap r v (c • v + z) = c • v + z :=
          elimMap_of_rowEval_eq_zero v (LinearMap.mem_ker.mp hx₂)
        rw [← hfix, map_add, map_smul, elimMap_self hv, smul_zero, zero_add]
        exact Submodule.mem_map_of_mem hz

/-! ### The specification of `kernelBasis` -/

/-- The standard basis spans `Fin n → ℚ`. -/
lemma span_kernelBasis_nil :
    Submodule.span ℚ {v | v ∈ (kernelBasis ([] : List (Fin n → ℚ)))} = ⊤ := by
  have hrange : {v | v ∈ (kernelBasis ([] : List (Fin n → ℚ)))} =
      Set.range (Pi.basisFun ℚ (Fin n)) := by
    ext v
    simp [kernelBasis, List.mem_map, List.mem_finRange, Pi.basisFun_apply, eq_comm]
  rw [hrange, Module.Basis.span_eq]

/-- Specification of `kernelBasis`: the span of the output is exactly the common kernel
of the linear conditions `rows`. -/
theorem mem_span_kernelBasis_iff (rows : List (Fin n → ℚ)) (x : Fin n → ℚ) :
    x ∈ Submodule.span ℚ {v | v ∈ kernelBasis rows} ↔
      ∀ r ∈ rows, ∑ j, r j * x j = 0 := by
  induction rows with
  | nil => simp [span_kernelBasis_nil]
  | cons r rows ih =>
    rw [kernelBasis, span_eliminate, Submodule.mem_inf, ih, LinearMap.mem_ker, rowForm_apply,
      List.forall_mem_cons]
    exact and_comm

/-- Every vector produced by `kernelBasis` satisfies all the linear conditions. -/
theorem kernelBasis_mem (rows : List (Fin n → ℚ)) {v : Fin n → ℚ}
    (hv : v ∈ kernelBasis rows) : ∀ r ∈ rows, ∑ j, r j * v j = 0 :=
  (mem_span_kernelBasis_iff rows v).mp (Submodule.subset_span hv)

/-- Every common solution of the linear conditions lies in the span of `kernelBasis`. -/
theorem mem_span_kernelBasis_of_forall (rows : List (Fin n → ℚ)) {x : Fin n → ℚ}
    (hx : ∀ r ∈ rows, ∑ j, r j * x j = 0) :
    x ∈ Submodule.span ℚ {v | v ∈ kernelBasis rows} :=
  (mem_span_kernelBasis_iff rows x).mpr hx

/-! ### Size of the output -/

/-- One elimination step never lengthens the list. -/
theorem length_eliminate_le (r : Fin n → ℚ) (vs : List (Fin n → ℚ)) :
    (eliminate r vs).length ≤ vs.length := by
  induction vs with
  | nil => simp [eliminate]
  | cons v vs ih =>
      rw [eliminate]
      split_ifs
      · simpa using ih
      · simp

/-- `kernelBasis` returns at most `n` vectors of `ℚⁿ`: it starts from the standard basis
and every elimination step drops or substitutes. -/
theorem length_kernelBasis_le (rows : List (Fin n → ℚ)) :
    (kernelBasis rows).length ≤ n := by
  induction rows with
  | nil => simp [kernelBasis]
  | cons r rows ih => exact (length_eliminate_le r _).trans ih

end Trinomial
