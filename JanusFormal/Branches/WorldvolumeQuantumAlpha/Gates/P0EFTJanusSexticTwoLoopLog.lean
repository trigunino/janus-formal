import Mathlib

namespace JanusFormal.P0EFTJanusSexticTwoLoopLog

set_option autoImplicit false

/-- Superficial momentum degree for a scalar graph with two-derivative
propagators in three dimensions. -/
def scalarSuperficialDegree (loops internalEdges : ℤ) : ℤ :=
  3 * loops - 2 * internalEdges

/-- The two-vertex six-point graph has `L=2`, `I=3`, hence degree zero and is
the first logarithmic pure-sextic topology. -/
theorem sextic_two_loop_graph_is_logarithmic :
    scalarSuperficialDegree 2 3 = 0 := by
  norm_num [scalarSuperficialDegree]

/-- In `d=3-2 epsilon`, `[phi]=(d-2)/2` and the `phi^6` coupling has
engineering dimension `6-2d=4 epsilon`. -/
theorem sextic_coupling_dimension_near_three
    (epsilon d scalarDim couplingDim : ℝ)
    (hDimension : d = 3 - 2 * epsilon)
    (hScalar : scalarDim = (d - 2) / 2)
    (hCoupling : couplingDim = d - 6 * scalarDim) :
    couplingDim = 4 * epsilon := by
  rw [hScalar, hDimension] at hCoupling
  linarith

/-- Minimal-subtraction bookkeeping at quadratic order. `poleResidue` is the
coefficient `A` in `lambda_B=mu^(4epsilon)(lambda+A lambda^2/epsilon+...)`.
The resulting quadratic beta coefficient is `4A`; this theorem does not
compute `A`. -/
structure SexticMSPoleData where
  poleResidue : ℝ
  betaQuadraticCoefficient : ℝ
  bareScaleExponent : ℝ
  bareScaleExponentLaw : bareScaleExponent = 4
  betaPoleLaw : betaQuadraticCoefficient = bareScaleExponent * poleResidue

theorem beta_quadratic_coefficient_from_pole (s : SexticMSPoleData) :
    s.betaQuadraticCoefficient = 4 * s.poleResidue := by
  rw [s.betaPoleLaw, s.bareScaleExponentLaw]

structure SexticTwoLoopClosureStatus where
  nonzeroMomentumSubtractionPointFixed : Prop
  infraredRegulatorFixed : Prop
  allTwoLoopSixPointGraphsEnumerated : Prop
  subdivergencesSubtracted : Prop
  masterIntegralPoleComputed : Prop
  combinatorialNormalizationComputed : Prop
  poleResidueComputed : Prop
  betaCoefficientDerived : Prop

def sexticTwoLoopClosure (s : SexticTwoLoopClosureStatus) : Prop :=
  s.nonzeroMomentumSubtractionPointFixed ∧
  s.infraredRegulatorFixed ∧
  s.allTwoLoopSixPointGraphsEnumerated ∧
  s.subdivergencesSubtracted ∧
  s.masterIntegralPoleComputed ∧
  s.combinatorialNormalizationComputed ∧
  s.poleResidueComputed ∧
  s.betaCoefficientDerived

end JanusFormal.P0EFTJanusSexticTwoLoopLog
