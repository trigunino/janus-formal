import Mathlib

namespace JanusFormal.P0EFTJanusSexticMasterIntegralPole

set_option autoImplicit false

/-- Analytic input from the dimensionally regulated massless sunset master:
the coefficient of `1/epsilon` is `1/(64*pi^2)` in the `(2*pi)^-d` measure
convention. -/
structure SexticMasterPoleMatching where
  masterPole : ℝ
  combinatorialWeight : ℝ
  couplingPoleResidue : ℝ
  betaQuadraticCoefficient : ℝ
  masterPoleLaw : masterPole = 1 / (64 * Real.pi ^ 2)
  couplingResidueLaw : couplingPoleResidue = combinatorialWeight * masterPole
  betaLaw : betaQuadraticCoefficient = 4 * couplingPoleResidue

/-- Once the action/diagram combinatorial weight `W` is fixed, the quadratic
beta coefficient is `W/(16*pi^2)`. -/
theorem beta_coefficient_reduced_to_combinatorial_weight
    (s : SexticMasterPoleMatching) :
    s.betaQuadraticCoefficient =
      s.combinatorialWeight / (16 * Real.pi ^ 2) := by
  rw [s.betaLaw, s.couplingResidueLaw, s.masterPoleLaw]
  ring

/-- For `L_int=lambda6*phi^6/6`, labeled external-leg contractions, the
second-order expansion factor and division by the tree six-point vertex give
the total pure-scalar weight `W=200`. -/
theorem repository_sextic_combinatorial_weight :
    ((20 * 120 * 120 * 6 : ℚ) / (2 * 6 ^ 2)) / 120 = 200 := by
  norm_num

/-- In the standard `g*phi^6/6!` normalization the same graph has weight
`5/3`, providing a normalization cross-check. -/
theorem standard_sextic_combinatorial_weight :
    ((20 * 120 * 120 * 6 : ℚ) / (2 * 720 ^ 2)) = 5 / 3 := by
  norm_num

/-- Combining `W=200` with the master pole gives the pure-scalar contribution
`beta_lambda6 = 25/(2*pi^2) lambda6^2 + ...` in repository normalization. -/
theorem repository_pure_scalar_beta_coefficient
    (s : SexticMasterPoleMatching)
    (hWeight : s.combinatorialWeight = 200) :
    s.betaQuadraticCoefficient = 25 / (2 * Real.pi ^ 2) := by
  rw [beta_coefficient_reduced_to_combinatorial_weight s, hWeight]
  ring

structure MasterPoleClosureStatus where
  measureConventionFixed : Prop
  nonexceptionalExternalMomentumFixed : Prop
  gammaFunctionContinuationDerived : Prop
  masterPoleResidueDerived : Prop
  actionVertexNormalizationFixed : Prop
  graphSymmetryFactorsComputed : Prop
  subdivergenceCountertermsIncluded : Prop
  totalCombinatorialWeightComputed : Prop

def masterPoleClosure (s : MasterPoleClosureStatus) : Prop :=
  s.measureConventionFixed ∧
  s.nonexceptionalExternalMomentumFixed ∧
  s.gammaFunctionContinuationDerived ∧
  s.masterPoleResidueDerived ∧
  s.actionVertexNormalizationFixed ∧
  s.graphSymmetryFactorsComputed ∧
  s.subdivergenceCountertermsIncluded ∧
  s.totalCombinatorialWeightComputed

end JanusFormal.P0EFTJanusSexticMasterIntegralPole
