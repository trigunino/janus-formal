import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D

/-!
# Local coordinates of descended throat gauge second jets

The local trivializations of the vector-bundle core recover exactly the
pointwise quotient normalization in the selected frame/chart pair.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportGroupoid4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Changing between two valid atlas pairs carries the normalization in the
first pair to the normalization in the second pair. -/
theorem throatGaugeSecondOrderJetPointwiseNormalizeAt_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first)
    (hSecond : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod second)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current
        (throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          first.1 first.2 current hFirst.1 hFirst.2 jetClass) =
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
        second.1 second.2 current hSecond.1 hSecond.2 jetClass := by
  refine Quotient.inductionOn jetClass ?_
  intro presentation
  rw [throatGaugeSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current ⟨hFirst, hSecond⟩]
  simpa [throatGaugeSecondOrderJetPointwiseNormalizeAt,
    throatGaugeSecondOrderJetNormalizeRepresentativeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt,
    targetPresentationAt,
    throatGaugeSecondOrderJetSemidirectTransportAt,
    throatGaugeSecondOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionSecondDerivativeAt] using
    (throatGaugeSecondOrderJetSemidirectTransportAt_comp_apply
      period hPeriod presentation
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
        current hFirst)
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
        current hSecond) presentation.jet).symm

/-- The fiber coordinate of a descended quotient class in a core chart is
its pointwise normalization in that chart's frame/chart pair. -/
theorem throatGaugeSecondOrderJetPointwiseClass_localTriv_snd
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
        index
        (throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
          period hPeriod current jetClass)).2 =
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
        index.1 index.2 current hCurrent.1 hCurrent.2 jetClass := by
  rw [VectorBundleCore.localTriv_apply]
  exact throatGaugeSecondOrderJetPointwiseNormalizeAt_coordChange
    period hPeriod
      (throatGaugeSecondOrderJetBundleIndexAt period hPeriod current)
      index current
      (mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
        period hPeriod current)
      hCurrent jetClass

/-- For a represented class, the same local coordinate is the normalization
of that representative. -/
theorem throatGaugeSecondOrderJetPresentationClass_localTriv_snd
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index)
    (presentation :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current) :
    ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
        index
        (throatGaugeSecondOrderJetPointwiseClassInVectorBundleTotalSpace
          period hPeriod current
          (throatGaugeSecondOrderJetPresentationClass
            period hPeriod current presentation))).2 =
      throatGaugeSecondOrderJetNormalizeRepresentativeAt period hPeriod
        index.1 index.2 current hCurrent.1 hCurrent.2 presentation := by
  simpa [throatGaugeSecondOrderJetPresentationClass,
    throatGaugeSecondOrderJetPointwiseNormalizeAt] using
    (throatGaugeSecondOrderJetPointwiseClass_localTriv_snd
      period hPeriod index current hCurrent
        (throatGaugeSecondOrderJetPresentationClass
          period hPeriod current presentation))

/-- In every valid core chart, the descended actual section has the actual
extracted framed second jet as its fiber coordinate. -/
theorem actualThroatGaugeSecondOrderJetVectorBundleSection_localTriv_snd
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
        index
        (actualThroatGaugeSecondOrderJetVectorBundleSection
          period hPeriod potential component current)).2 =
      throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
        potential component index.1 index.2 current
          hCurrent.1 hCurrent.2 := by
  let presentation :=
    actualThroatGaugeSecondOrderJetPresentationAt period hPeriod potential
      component index.1 index.2 current hCurrent.1 hCurrent.2
  have hClass :=
    actualThroatGaugeSecondOrderJetPresentationClass_eq_canonical
      period hPeriod potential component index.1 index.2 current
        hCurrent.1 hCurrent.2
  calc
    ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
        index
        (actualThroatGaugeSecondOrderJetVectorBundleSection
          period hPeriod potential component current)).2 =
        throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          index.1 index.2 current hCurrent.1 hCurrent.2
          (actualThroatGaugeSecondOrderJetPointwiseClass
            period hPeriod potential component current) := by
      exact throatGaugeSecondOrderJetPointwiseClass_localTriv_snd
        period hPeriod index current hCurrent
          (actualThroatGaugeSecondOrderJetPointwiseClass
            period hPeriod potential component current)
    _ = throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          index.1 index.2 current hCurrent.1 hCurrent.2
          (throatGaugeSecondOrderJetPresentationClass
            period hPeriod current presentation) :=
      congrArg
        (throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          index.1 index.2 current hCurrent.1 hCurrent.2) hClass.symm
    _ = presentation.jet := by
      simpa [presentation,
        throatGaugeSecondOrderJetPointwiseDenormalizeAt,
        throatGaugeSecondOrderJetPresentationClass,
        targetPresentationAt,
        actualThroatGaugeSecondOrderJetPresentationAt] using
        (throatGaugeSecondOrderJetPointwiseNormalizeAt_denormalize
          period hPeriod index.1 index.2 current hCurrent.1 hCurrent.2
            presentation.jet)
    _ = throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
          potential component index.1 index.2 current
            hCurrent.1 hCurrent.2 := rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D
end JanusFormal
