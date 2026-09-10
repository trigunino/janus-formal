import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D

/-!
# Invariant T02 realization of a rank-one quadratic channel

This gate turns the physical rank-one family into an actual
`ProgramPT02AdmissibleInvariantLocalFunctional4D`.  The value and selected
first-jet covectors are transported from the genuine Finsupp jet through the
Gate881 continuous linear equivalence.  Their linear combination and
symmetric rank-one bilinear combination are required, visibly, to satisfy
the exact T02 transition-invariance predicates on every genuine bundle
overlap.

Under those two explicit admissibility proofs, the resulting T02 functional
has zero cubic and quartic parts.  Its pulled-back T02 evaluation is exactly
the rank-one density, so the Gate880 formula, coefficient converse, and
explicit horizontal-divergence certificate transfer without changing the
local function.

The current T02 API expresses covariance through the actual bundle
`coordChange` maps.  It exposes no separate deck action on
`ActualPhysicalSecondOrderJetProductFiber`; consequently this gate asserts
no additional deck-equivariance theorem beyond the displayed transition
invariance.  It also supplies no nonzero invariant channel automatically:
membership in the two invariant submodules remains explicit data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02InvariantRankOneQuadraticBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev ValueFiber := ActualPhysicalValueProductFiber
private abbrev FinsuppSecondJet :=
  ThroatSpatialMultiindexJet2 ValueFiber
private abbrev FinsuppFourthJet :=
  ThroatSpatialMultiindexJet4 ValueFiber
private abbrev PhysicalSecondJet :=
  ActualPhysicalSecondOrderJetProductFiber

variable (period : Real) (hPeriod : period ≠ 0)

private def finsuppValueChannel
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    FinsuppSecondJet →L[Real] Real :=
  density.channel.comp
    (ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex)

private def finsuppFirstChannel
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    FinsuppSecondJet →L[Real] Real :=
  density.channel.comp
    (ContinuousLinearMap.proj
      (programPT06SecondOrderFirstMultiIndex density.direction))

/-- Value-coordinate channel transported to the actual T02 second-jet
fiber. -/
def programPT06T02RankOnePhysicalValueChannel
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    PhysicalSecondJet →L[Real] Real :=
  (finsuppValueChannel density).comp
    programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm.toContinuousLinearMap

/-- Selected first-coordinate channel transported to the actual T02
second-jet fiber. -/
def programPT06T02RankOnePhysicalFirstChannel
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    PhysicalSecondJet →L[Real] Real :=
  (finsuppFirstChannel density).comp
    programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm.toContinuousLinearMap

@[simp] theorem programPT06T02RankOnePhysicalValueChannel_bridge
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : FinsuppSecondJet) :
    programPT06T02RankOnePhysicalValueChannel density
        (programPT06T02FinsuppSecondJetBridge jet) =
      density.channel (jet programPT06SecondOrderZeroMultiIndex) := by
  change
    finsuppValueChannel density
        (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm
          (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
            jet)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

@[simp] theorem programPT06T02RankOnePhysicalFirstChannel_bridge
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : FinsuppSecondJet) :
    programPT06T02RankOnePhysicalFirstChannel density
        (programPT06T02FinsuppSecondJetBridge jet) =
      density.channel
        (jet (programPT06SecondOrderFirstMultiIndex density.direction)) := by
  change
    finsuppFirstChannel density
        (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm
          (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
            jet)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Linear part of the rank-one density on the actual T02 fiber. -/
def programPT06T02RankOnePhysicalLinearForm
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    PhysicalSecondJet →L[Real] Real :=
  density.valueLinear • programPT06T02RankOnePhysicalValueChannel density +
    density.firstLinear • programPT06T02RankOnePhysicalFirstChannel density

/-- Symmetric bilinear form whose diagonal is the quadratic part of the
rank-one density on the actual T02 fiber. -/
def programPT06T02RankOnePhysicalQuadraticForm
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    PhysicalSecondJet →L[Real] (PhysicalSecondJet →L[Real] Real) :=
  density.valueSquare •
      (programPT06T02RankOnePhysicalValueChannel density).smulRight
        (programPT06T02RankOnePhysicalValueChannel density) +
    (density.valueFirst / 2) •
      ((programPT06T02RankOnePhysicalValueChannel density).smulRight
          (programPT06T02RankOnePhysicalFirstChannel density) +
        (programPT06T02RankOnePhysicalFirstChannel density).smulRight
          (programPT06T02RankOnePhysicalValueChannel density)) +
    density.firstSquare •
      (programPT06T02RankOnePhysicalFirstChannel density).smulRight
        (programPT06T02RankOnePhysicalFirstChannel density)

theorem programPT06T02RankOnePhysicalQuadraticForm_symmetric
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (first second : PhysicalSecondJet) :
    programPT06T02RankOnePhysicalQuadraticForm density first second =
      programPT06T02RankOnePhysicalQuadraticForm density second first := by
  (simp [programPT06T02RankOnePhysicalQuadraticForm]; ring)

/-- Exact admissibility data needed to place the rank-one density inside
T02.  Both fields are the existing T02 predicates, hence quantify over every
actual physical bundle transition and every genuine overlap. -/
structure ProgramPT06T02InvariantRankOneQuadraticData4D where
  density : ProgramPT06T02RankOneDirectedQuadraticDensity4D
  linear_transition_invariant :
    IsActualPhysicalSecondOrderJetTransitionInvariant period hPeriod
      (programPT06T02RankOnePhysicalLinearForm density)
  quadratic_transition_invariant :
    IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm period hPeriod
      (programPT06T02RankOnePhysicalQuadraticForm density)

/-- Actual admissible T02 functional represented by the invariant rank-one
linear and quadratic forms. -/
def programPT06T02InvariantRankOneQuadraticFunctional
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod) :
    ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod where
  lower :=
    { lower :=
        { constant := data.density.constant
          linear :=
            ⟨programPT06T02RankOnePhysicalLinearForm data.density,
              data.linear_transition_invariant⟩
          quadratic :=
            ⟨programPT06T02RankOnePhysicalQuadraticForm data.density,
              data.quadratic_transition_invariant⟩ }
      cubic := 0 }
  quartic := 0

/-- The constructed object is invariant under every genuine T02 bundle
transition, with the overlap hypothesis shown explicitly. -/
theorem programPT06T02InvariantRankOneQuadraticFunctional_transitionInvariant
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod)
    (first second :
      ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : PhysicalSecondJet) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data)
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data) jet := by
  exact
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_transitionInvariant
      period hPeriod
      (programPT06T02InvariantRankOneQuadraticFunctional period hPeriod data)
      first second base hBase jet

theorem programPT06T02RankOneDensityEvaluation_explicit
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : FinsuppSecondJet) :
    programPT06T02RankOneDirectedQuadraticDensityEvaluation density jet =
      density.constant +
        density.valueLinear *
          density.channel (jet programPT06SecondOrderZeroMultiIndex) +
        density.firstLinear *
          density.channel
            (jet (programPT06SecondOrderFirstMultiIndex density.direction)) +
        density.valueSquare *
          density.channel (jet programPT06SecondOrderZeroMultiIndex) ^ 2 +
        density.valueFirst *
          density.channel (jet programPT06SecondOrderZeroMultiIndex) *
          density.channel
            (jet (programPT06SecondOrderFirstMultiIndex density.direction)) +
        density.firstSquare *
          density.channel
            (jet (programPT06SecondOrderFirstMultiIndex density.direction)) ^ 2 := by
  rfl

/-- Evaluation of the constructed T02 functional on the actual physical
fiber, before pulling it back through Gate881. -/
theorem programPT06T02InvariantRankOneQuadraticFunctional_evaluation
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod)
    (jet : PhysicalSecondJet) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data) jet =
      data.density.constant +
        data.density.valueLinear *
          programPT06T02RankOnePhysicalValueChannel data.density jet +
        data.density.firstLinear *
          programPT06T02RankOnePhysicalFirstChannel data.density jet +
        data.density.valueSquare *
          programPT06T02RankOnePhysicalValueChannel data.density jet ^ 2 +
        data.density.valueFirst *
          programPT06T02RankOnePhysicalValueChannel data.density jet *
          programPT06T02RankOnePhysicalFirstChannel data.density jet +
        data.density.firstSquare *
          programPT06T02RankOnePhysicalFirstChannel data.density jet ^ 2 := by
  (simp [programPT06T02InvariantRankOneQuadraticFunctional,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation,
    programPT06T02RankOnePhysicalLinearForm,
    programPT06T02RankOnePhysicalQuadraticForm]; ring)

/-- The genuine T02 local Lagrangian pulled back to Finsupp jets is exactly
the rank-one physical density. -/
@[simp] theorem programPT06T02InvariantRankOneLocalLagrangian_evaluation
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data) jet =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation
        data.density jet := by
  rw [programPT06T02FinsuppSecondJetLocalLagrangian_apply,
    programPT06T02InvariantRankOneQuadraticFunctional_evaluation,
    programPT06T02RankOnePhysicalValueChannel_bridge,
    programPT06T02RankOnePhysicalFirstChannel_bridge,
    programPT06T02RankOneDensityEvaluation_explicit]

/-- Function-level form of the exact T02/rank-one evaluation bridge. -/
theorem programPT06T02InvariantRankOneLocalLagrangian_eq
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data) =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation data.density := by
  funext jet
  exact programPT06T02InvariantRankOneLocalLagrangian_evaluation
    period hPeriod data jet

/-- Gate880 on the actual invariant T02 functional is exactly Gate880 on the
rank-one physical density. -/
theorem programPT06SecondOrderLocalEuler_t02InvariantRankOne_eq
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod)
    (jet : FinsuppFourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02InvariantRankOneQuadraticFunctional
            period hPeriod data)) jet =
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation data.density)
        jet := by
  rw [programPT06T02InvariantRankOneLocalLagrangian_eq]

/-- Exact coefficient converse for the constructed admissible invariant T02
subclass. -/
theorem programPT06_t02InvariantRankOne_euler_eq_zero_iff
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod) :
    (forall jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02InvariantRankOneQuadraticFunctional
            period hPeriod data)) jet = 0) <->
      And (data.density.valueLinear = 0)
        (And (data.density.valueSquare = 0)
          (data.density.firstSquare = 0)) := by
  rw [programPT06T02InvariantRankOneLocalLagrangian_eq]
  exact
    programPT06_t02RankOneDirectedQuadratic_euler_eq_zero_iff data.density

/-- Euler-null invariant rank-one T02 functionals have the explicit constant
plus genuine affine and quadratic horizontal-divergence presentation. -/
theorem programPT06T02InvariantRankOne_eq_constant_add_divergences_of_euler
    (data : ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod)
    (hEuler : forall jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02InvariantRankOneQuadraticFunctional
            period hPeriod data)) jet = 0)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02InvariantRankOneQuadraticFunctional
          period hPeriod data) jet =
      data.density.constant +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent data.density)
          jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent data.density)
          jet := by
  have hCoefficients :=
    (programPT06_t02InvariantRankOne_euler_eq_zero_iff
      period hPeriod data).mp hEuler
  rcases hCoefficients with ⟨hLinear, hValueSquare, hFirstSquare⟩
  rw [programPT06T02InvariantRankOneLocalLagrangian_evaluation]
  exact
    programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
      data.density hLinear hValueSquare hFirstSquare jet

end
end P0EFTJanusProgramPT06T02InvariantRankOneQuadraticBridge4D
end JanusFormal
