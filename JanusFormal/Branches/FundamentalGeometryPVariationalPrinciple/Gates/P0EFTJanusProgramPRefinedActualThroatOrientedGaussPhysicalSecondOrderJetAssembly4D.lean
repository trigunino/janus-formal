import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRefinedConditionalActualThroatPhysicalSecondOrderJetAssembly4D

/-!
# Refined actual throat jet with oriented Gauss normal data

This gate inserts the actual sector-metric Gauss second fundamental form into
the refined physical second-order jet at one lift of the throat orientation
double cover. The scalar normal coordinate is local to that oriented frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRefinedActualThroatOrientedGaussPhysicalSecondOrderJetAssembly4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D
open P0EFTJanusProgramPRefinedConditionalActualThroatPhysicalSecondOrderJetAssembly4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Refined physical second-order jet with genuine actual Gauss normal slots. -/
def globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hBase : orientationDoubleToThroat period hPeriod boundary ∈
      d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)) :
    ThroatPhysicalSecondOrderJet period hPeriod configuration :=
  globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
    period hPeriod configuration data index
      (orientationDoubleToThroat period hPeriod boundary) hBase hTransverse
      (actualThroatOrientedGaussCompletionData period hPeriod configuration
        boundary)

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hBase : orientationDoubleToThroat period hPeriod boundary ∈
      d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)) :
    (globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index boundary hBase hTransverse).point =
      orientationDoubleToThroat period hPeriod boundary :=
  rfl

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt_background
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hBase : orientationDoubleToThroat period hPeriod boundary ∈
      d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)) :
    (globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index boundary hBase hTransverse).background =
      globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet
        period hPeriod configuration data boundary hTransverse :=
  rfl

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hBase : orientationDoubleToThroat period hPeriod boundary ∈
      d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) :
    (globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index boundary hBase hTransverse).background.normalQuadratic
        sector =
      actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector :=
  rfl

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt_physicalNormal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hBase : orientationDoubleToThroat period hPeriod boundary ∈
      d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) :
    (globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index boundary hBase hTransverse).background.physicalNormal
        sector = 1 :=
  rfl

end
end P0EFTJanusProgramPRefinedActualThroatOrientedGaussPhysicalSecondOrderJetAssembly4D
end JanusFormal
