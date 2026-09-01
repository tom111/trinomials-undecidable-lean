import Trinomial.ShortestPolynomial

import Trinomial.Base.Laurent
import Trinomial.Base.RatAlgebra
import Trinomial.Base.BaseAlgebra
import Trinomial.Base.Trinomials
import Trinomial.Base.BaseIdeal
import Trinomial.Base.BaseAlgebraBasis
import Trinomial.Base.BasePrimary
import Trinomial.Base.Shape
import Trinomial.Base.ShapeTable
import Trinomial.Base.ShapeCertificates
import Trinomial.Base.ShapeClassification
import Trinomial.Base.PrimitiveNormalization

import Trinomial.Quadrics.QuadraticAlgebra
import Trinomial.Quadrics.CubeAlgebraStructure
import Trinomial.Quadrics.CubeAlgebraSocle
import Trinomial.Quadrics.CubeAlgebraGraded
import Trinomial.Quadrics.CubeAlgebraPresentation
import Trinomial.Quadrics.KernelEvaluation

import Trinomial.Encoding.DegreeTwoEquation
import Trinomial.Encoding.Homogenization
import Trinomial.Encoding.PellGuard
import Trinomial.Encoding.MainLaurent
import Trinomial.Encoding.GuardedSystem
import Trinomial.Encoding.GuardSection
import Trinomial.Encoding.RationalInfinity
import Trinomial.Encoding.PolynomialSide
import Trinomial.Encoding.PolynomialTrinomials
import Trinomial.Encoding.StraightLineProgram
import Trinomial.Encoding.DegreeDecomposition
import Trinomial.Encoding.ZeroDimensional
import Trinomial.Encoding.KernelBasis
import Trinomial.Encoding.Generators
import Trinomial.Encoding.Colength
import Trinomial.Encoding.Counting
import Trinomial.Encoding.MainTheorem
import Trinomial.Encoding.Geometry
import Trinomial.Encoding.Codes
import Trinomial.Encoding.Semidecision
import Trinomial.Encoding.Compiler
import Trinomial.Encoding.Undecidability

import Trinomial.Universal.MRDP
import Trinomial.Universal.HaltingFamily
import Trinomial.Universal.FixedIdeal
import Trinomial.Universal.ComputableHaltingFamily

import Trinomial.Paper
import Trinomial.Examples

/-!
# Trinomial containment in polynomial ideals is undecidable

The Lean 4 formalization of *Trinomial containment in polynomial ideals is undecidable*
by Tobias Boege, Anna Hofer and Thomas Kahle, arXiv:2608.31162
(https://arxiv.org/abs/2608.31162).  The modules follow the sections of the paper;
`Trinomial/Paper.lean` restates every result of the paper in the paper's order and checks
its axioms, and `Trinomial/Examples.lean` runs the executable parts.

* §1  `ShortestPolynomial` — the number of terms and `t(I)`.
* §2  `Base/` — the Laurent ring `L_N`, the base ideal `J₀`, `A₀ = L_N/J₀`, the two
  trinomial families, Proposition 2.4.
* §3  `Quadrics/` — the algebras `A_B`, Lemma 3.2, `Exp`, the maps `φ_Q`,
  Proposition 3.5.
* §4  `Encoding/` — straight line programs (Lemma 4.1), the guards (Lemma 4.2),
  the ideals `J_P` and `I_P`, Theorem 4.5 with its executable generator list.
* §5  `Universal/` — the MRDP layer and Corollary 5.1.
-/
