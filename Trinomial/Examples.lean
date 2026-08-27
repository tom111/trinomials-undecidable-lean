import Trinomial.Universal.HaltingFamily
import Trinomial.Encoding.GuardSection

/-!
# Running the executable parts of the construction

Every step of the algorithm of Theorem 4.5 is an executable definition.  This file runs
them on small inputs; the outputs are printed at build time.

* Lemma 4.1 on the paper's example `P(y₁, y₂) = 3y₁² + y₁y₂ + 1` [§4]: the
  straight line program, the number of its auxiliary variables and gates, and the size of
  the guarded system of Lemma 4.2.
* Lemma 4.2: the computable section `guardSection` (the first Pell solution with
  `h ≥ Σ xᵢ²` and a four-squares witness found by exhaustive search).
* "Linear algebra on the residues" (proof of Corollary 4.6): `kernelBasis` on tiny
  systems.
* The syntax `U(e, Y)` of Corollary 5.1 for a toy relation: the exponent vectors do not
  depend on `e`, so neither does the number of auxiliary variables.

Running `generatorsOf` itself takes about a minute on the smallest instance (the zero
polynomial in no variables, `N = 7`, a linear system with `52` rows and `C(13, 4) = 715`
unknowns) and is not part of the build; the commented lines at the end show how to run it.
The end-to-end cross-check of the generator algorithm against an independent computation is
the Macaulay2 script `certificates/degree_five_check.m2`.
-/

set_option autoImplicit false

namespace Trinomial.Examples

open TrinomialUndecidability.Computability (IntPolynomialCode EffDiophRel)

/-! ### Lemma 4.1 on the paper's example -/

deriving instance Repr for DegreeTwoEquation

/-- `P(y₁, y₂) = 3y₁² + y₁y₂ + 1`  [§4], as sparse syntax. -/
def examplePoly : IntPolynomialCode 2 := [(![2, 0], 3), (![1, 1], 1), (![0, 0], 1)]

-- The number of auxiliary variables of the straight line program (the paper's hand-written
-- program uses `5`; the compiler uses a scaling step `x = c·x'` and multiplies by input
-- variables directly).
#eval (StraightLineProgram.ofCode examplePoly).k

-- The gates of the program.
#eval (StraightLineProgram.ofCode examplePoly).gates

-- The number of equations of the degree-two system (the gates and `x_out = 0`).
#eval (degreeTwoSystem examplePoly).length

-- The number `M` of quadratic forms: the equations plus the two guards.
#eval (guarded (degreeTwoSystem examplePoly)).length

-- The number `N` of variables `D_i` of the ideal `I_P` attached to the example.
#eval numVars examplePoly

/-! ### Lemma 4.2: the computable section -/

-- A four-squares witness of `30`.
#eval fourSquares 30

-- The first Pell solution `(h, k)` of `h² − 3k² = 1` with `h ≥ 100`.
#eval pellSolution 100

-- The section applied to the point `x = (3, 4)`: `h, k` and `u₁, …, u₄` with
-- `h² − 3k² = 1` and `3² + 4² + Σ uⱼ² = h`.
#eval List.ofFn (guardSection (![3, 4] : Fin 2 → ℤ))

/-! ### Linear algebra on the residues

The kernel of the two conditions `x₀ + x₁ = 0` and `x₁ + x₂ = 0` on `ℚ³` is spanned by
`(1, -1, 1)`; with no condition the standard basis is returned, a repeated condition
changes nothing, and the zero row is ignored. -/

/-- Print a list of vectors as a list of lists of rationals. -/
private def showVecs {n : ℕ} (vs : List (Fin n → ℚ)) : List (List String) :=
  vs.map fun v => (List.ofFn v).map toString

#eval showVecs (kernelBasis (n := 3) [![1, 1, 0], ![0, 1, 1]])
#eval showVecs (kernelBasis (n := 3) [])
#eval showVecs (kernelBasis (n := 3) [![1, 1, 0], ![1, 1, 0], ![0, 0, 0]])
#eval showVecs (kernelBasis (n := 2) [![1, 0], ![0, 1]])

/-! ### The syntax `U(e, Y)` of Corollary 5.1 on a toy relation

For the always-true relation `0 = 0` in one free variable (`zeroEquation 1`, no auxiliary
variables) `frozenCode` is the unsimplified square `(X₀ − e)² = X₀² − e·X₀ − e·X₀ + e²`:
four terms with the same exponents for every `e`, and the straight line program has the
same number of auxiliary variables for every `e`. -/

#eval (frozenCode (EffDiophRel.zeroEquation 1) 5).map fun t => (List.ofFn t.1, t.2)
#eval (frozenCode (EffDiophRel.zeroEquation 1) 7).map fun t => (List.ofFn t.1, t.2)
#eval Universal.k₀ (EffDiophRel.zeroEquation 1)
#eval (StraightLineProgram.ofCode (frozenCode (EffDiophRel.zeroEquation 1) 7)).k
#eval Universal.N₀ (EffDiophRel.zeroEquation 1)
#eval Universal.M₀ (EffDiophRel.zeroEquation 1)

/-! ### The generator algorithm of Theorem 4.5

On the smallest instance, the zero polynomial in no variables (one auxiliary variable
`x₁ = 0` and the output equation `x₁ = 0`, plus the two guards: `N = 7`, `M = 4`),
`generatorsOf` returns `C(13, 5) = 1287` products of degree five and `700` kernel vectors,
in about a minute.  The lines are commented out to keep the build fast:

    def zeroPoly : IntPolynomialCode 0 := []
    #eval (generatorsOf zeroPoly).length                       -- 1987
    #eval ((generatorsOf zeroPoly).drop 1287).take 3 |>.map PointPoly.display
-/

end Trinomial.Examples
