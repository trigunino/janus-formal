import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D

/-!
# Actual-atlas naturality of the T02 radial-current divergence

This gate transports the genuine derivative-corrected T02 second-jet
transition through Gate 881's continuous linear equivalence.  The terminal
T02 local Lagrangian is invariant under that transported action.  When its
Euler expression vanishes, the divergence of the canonical radial Cartan
current is invariant as well, after the canonical zero extension to fourth
jets.

The conclusion concerns the represented divergence.  It does not yet give a
transition law for the third-jet current itself or identify the actual atlas
action with Gate 902's spatially frozen moving-frame conjugation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02ActualAtlasRadialCurrentNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D

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

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FinsuppSecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev FinsuppFourthJet := ThroatSpatialMultiindexJet4 Fiber

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)
private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

/-- The actual derivative-corrected T02 coordinate change, conjugated into
the genuine spatial multi-index second-jet carrier. -/
def programPT06T02ActualAtlasFinsuppSecondJetCoordChange
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : FinsuppSecondJet) : FinsuppSecondJet :=
  programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm
    ((actualPhysicalSecondOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter).coordChange first second base
      (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
        jet))

/-- Gate 881 sends the transported multi-index action back to the genuine
T02 coordinate change. -/
theorem programPT06T02FinsuppSecondJetBridge_actualAtlasCoordChange
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetBridge
        (programPT06T02ActualAtlasFinsuppSecondJetCoordChange
          period hPeriod first second base jet) =
      (actualPhysicalSecondOrderJetProductVectorBundleCore
          period hPeriod .positiveQuarter).coordChange first second base
        (programPT06T02FinsuppSecondJetBridge jet) := by
  change
    programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
        (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm
          ((actualPhysicalSecondOrderJetProductVectorBundleCore
              period hPeriod .positiveQuarter).coordChange first second base
            (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
              jet))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The pulled-back T02 density is invariant under the transported genuine
atlas transition. -/
theorem programPT06T02FinsuppSecondJetLocalLagrangian_actualAtlas_invariant
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        (programPT06T02ActualAtlasFinsuppSecondJetCoordChange
          period hPeriod first second base jet) =
      programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional jet := by
  rw [programPT06T02FinsuppSecondJetLocalLagrangian_apply,
    programPT06T02FinsuppSecondJetBridge_actualAtlasCoordChange,
    programPT06T02FinsuppSecondJetLocalLagrangian_apply]
  exact
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_transitionInvariant
      period hPeriod functional first second base hBase
        (programPT06T02FinsuppSecondJetBridge jet)

/-- Under Euler vanishing, the canonical Cartan divergence descends through
every actual T02 second-jet transition.  The zero extensions are canonical
representatives; the result does not claim that the current itself glues. -/
theorem programPT06T02DegreeFourRadialCartanCurrentDH_actualAtlas_invariant
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (hEuler : ∀ jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second)
    (jet : FinsuppSecondJet) :
    programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional)
        (programPT06SecondJetZeroExtension
          (programPT06T02ActualAtlasFinsuppSecondJetCoordChange
            period hPeriod first second base jet)) =
      programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional)
        (programPT06SecondJetZeroExtension jet) := by
  have hChanged :=
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
      period hPeriod functional hEuler
        (programPT06SecondJetZeroExtension
          (programPT06T02ActualAtlasFinsuppSecondJetCoordChange
            period hPeriod first second base jet))
  have hOriginal :=
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
      period hPeriod functional hEuler
        (programPT06SecondJetZeroExtension jet)
  simp only
    [← programPT06FourthJetToSecondJetContinuousLinearMap_apply,
      programPT06FourthJetToSecondJet_zeroExtension] at hChanged
  simp only
    [← programPT06FourthJetToSecondJetContinuousLinearMap_apply,
      programPT06FourthJetToSecondJet_zeroExtension] at hOriginal
  have hDensity :=
    programPT06T02FinsuppSecondJetLocalLagrangian_actualAtlas_invariant
      period hPeriod functional first second base hBase jet
  linarith

end
end P0EFTJanusProgramPT06T02ActualAtlasRadialCurrentNaturality4D
end JanusFormal
