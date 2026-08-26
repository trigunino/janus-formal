import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D

/-!
# Pointwise normalization of the throat gauge second-jet quotient

After choosing one valid target frame and chart at a throat point, every
presentation class has a unique semidirectly transported raw jet in that
pair.  This gives a noncanonical pointwise equivalence with the framed
second-jet carrier; no smooth dependence on the point is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Representative normalization -/

/-- Transport one arbitrary representative into a fixed valid target pair. -/
def throatGaugeSecondOrderJetNormalizeRepresentativeAt
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (presentation : GaugePresentationAt period hPeriod current) : GaugeJet :=
  throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod presentation
    (targetPresentationAt period hPeriod targetFrame targetChart current
      hFrame hChart presentation.jet)
    presentation.jet

/-- Directly compatible representatives have the same normalized raw jet. -/
theorem throatGaugeSecondOrderJetNormalizeRepresentativeAt_eq_of_directCompatible
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    {first second : GaugePresentationAt period hPeriod current}
    (hDirect : DirectTransitionCompatible period hPeriod first second) :
    throatGaugeSecondOrderJetNormalizeRepresentativeAt period hPeriod
        targetFrame targetChart current hFrame hChart first =
      throatGaugeSecondOrderJetNormalizeRepresentativeAt period hPeriod
        targetFrame targetChart current hFrame hChart second := by
  apply directTransitionCompatible_target_jet_unique period hPeriod first
    targetFrame targetChart hFrame hFrame hChart hChart
  · simpa [throatGaugeSecondOrderJetNormalizeRepresentativeAt,
      targetPresentationAt,
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt] using
      (throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
        period hPeriod first
          (targetPresentationAt period hPeriod targetFrame targetChart current
            hFrame hChart first.jet))
  · have hSecondTarget :=
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
        period hPeriod second
          (targetPresentationAt period hPeriod targetFrame targetChart current
            hFrame hChart second.jet)
    have hFirstTarget :=
      directTransitionCompatible_trans period hPeriod hDirect hSecondTarget
    simpa [throatGaugeSecondOrderJetNormalizeRepresentativeAt,
      targetPresentationAt,
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt] using hFirstTarget

/-! ## Quotient normalization and inverse -/

/-- Normalize a pointwise quotient class in a chosen valid frame/chart pair. -/
def throatGaugeSecondOrderJetPointwiseNormalizeAt
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current → GaugeJet :=
  Quotient.lift
    (throatGaugeSecondOrderJetNormalizeRepresentativeAt period hPeriod
      targetFrame targetChart current hFrame hChart)
    (by
      intro first second hGenerated
      exact
        throatGaugeSecondOrderJetNormalizeRepresentativeAt_eq_of_directCompatible
          period hPeriod targetFrame targetChart current hFrame hChart
          (generatedTransitionRelation_directCompatible period hPeriod hGenerated))

/-- Install a raw jet in the chosen pair and take its pointwise class. -/
def throatGaugeSecondOrderJetPointwiseDenormalizeAt
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (jet : GaugeJet) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current :=
  throatGaugeSecondOrderJetPresentationClass period hPeriod current
    (targetPresentationAt period hPeriod targetFrame targetChart current
      hFrame hChart jet)

theorem throatGaugeSecondOrderJetPointwiseNormalizeAt_denormalize
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (jet : GaugeJet) :
    throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
        targetFrame targetChart current hFrame hChart
        (throatGaugeSecondOrderJetPointwiseDenormalizeAt period hPeriod
          targetFrame targetChart current hFrame hChart jet) =
      jet := by
  let presentation :=
    targetPresentationAt period hPeriod targetFrame targetChart current
      hFrame hChart jet
  have hSelf : DirectTransitionCompatible period hPeriod
      presentation presentation :=
    directTransitionCompatible_refl period hPeriod presentation
  have hTransport :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
      period hPeriod presentation presentation
  have hUnique := directTransitionCompatible_target_jet_unique period hPeriod
    presentation targetFrame targetChart hFrame hFrame hChart hChart
      jet
      (throatGaugeSecondOrderJetNormalizeRepresentativeAt period hPeriod
        targetFrame targetChart current hFrame hChart presentation)
      hSelf (by
        simpa [presentation,
          throatGaugeSecondOrderJetNormalizeRepresentativeAt,
          targetPresentationAt,
          throatGaugeSecondOrderJetSemidirectTargetPresentationAt] using
          hTransport)
  exact hUnique.symm

theorem throatGaugeSecondOrderJetPointwiseDenormalizeAt_normalize
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (quotientClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    throatGaugeSecondOrderJetPointwiseDenormalizeAt period hPeriod
        targetFrame targetChart current hFrame hChart
        (throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          targetFrame targetChart current hFrame hChart quotientClass) =
      quotientClass := by
  refine Quotient.inductionOn quotientClass ?_
  intro presentation
  apply Quotient.sound
  apply directCompatible_generated period hPeriod
  have hTransport :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
      period hPeriod presentation
        (targetPresentationAt period hPeriod targetFrame targetChart current
          hFrame hChart presentation.jet)
  simpa [throatGaugeSecondOrderJetPointwiseNormalizeAt,
    throatGaugeSecondOrderJetPointwiseDenormalizeAt,
    throatGaugeSecondOrderJetPresentationClass,
    throatGaugeSecondOrderJetNormalizeRepresentativeAt,
    targetPresentationAt,
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt] using
    (directTransitionCompatible_symm period hPeriod hTransport)

/-- A chosen valid frame/chart pair identifies the exact pointwise quotient
with the raw framed second-jet carrier. -/
def throatGaugeSecondOrderJetPointwiseQuotientEquivAt
    (targetFrame targetChart current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current ≃ GaugeJet where
  toFun := throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
    targetFrame targetChart current hFrame hChart
  invFun := throatGaugeSecondOrderJetPointwiseDenormalizeAt period hPeriod
    targetFrame targetChart current hFrame hChart
  left_inv := throatGaugeSecondOrderJetPointwiseDenormalizeAt_normalize
    period hPeriod targetFrame targetChart current hFrame hChart
  right_inv := throatGaugeSecondOrderJetPointwiseNormalizeAt_denormalize
    period hPeriod targetFrame targetChart current hFrame hChart

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D
end JanusFormal
