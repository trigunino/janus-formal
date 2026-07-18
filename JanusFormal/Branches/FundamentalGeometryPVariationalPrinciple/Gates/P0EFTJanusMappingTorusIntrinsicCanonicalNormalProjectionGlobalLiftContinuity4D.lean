import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D

/-!
# Conditional continuity of the global canonical normal lift

This gate is deliberately separate from the algebraic choice.  The chosen
lift and its representation/orthogonality laws are therefore opaque here.
The only remaining input is local continuity of its metric square in the
already installed transported differential-normal charts.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance throatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance throatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance quotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- Squared intrinsic metric value of the chosen global lift. -/
def canonicalGlobalNormalMetricSquare
    (normal : DifferentialNormalTotalSpace period hPeriod) : Real :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
    (fixedThroatQuotientInclusion period hPeriod normal.1)
    (canonicalGlobalOrthogonalNormalLift period hPeriod normal.1 normal.2)
    (canonicalGlobalOrthogonalNormalLift period hPeriod normal.1 normal.2)

/-- Pullback of the global square through one transported differential-normal
chart. -/
def canonicalGlobalNormalMetricSquareInChart
    (anchor : EffectiveThroatCover period hPeriod) :
    EffectiveThroat period hPeriod × Real → Real :=
  canonicalGlobalNormalMetricSquare period hPeriod ∘
    (differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm

/-- Exact remaining local regularity contract. -/
def CanonicalGlobalNormalMetricSquareLocalRegularity : Prop :=
  ∀ anchor : EffectiveThroatCover period hPeriod,
    ContinuousOn
      (canonicalGlobalNormalMetricSquareInChart period hPeriod anchor)
      (differentialNormalLocalTriv period hPeriod anchor).target

private theorem canonicalGlobalNormalMetricSquare_continuous_of_local
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    Continuous (canonicalGlobalNormalMetricSquare period hPeriod) := by
  rw [continuous_iff_continuousAt]
  intro normal
  let anchor := normalBundleIndexAt period hPeriod normal.1
  let trivialization := differentialNormalLocalTriv period hPeriod anchor
  have hSource : normal ∈ trivialization.source := by
    change normal.1 ∈ normalBundleBaseSet period hPeriod anchor
    exact mem_normalBundleBaseSet_indexAt period hPeriod normal.1
  have hTarget : trivialization normal ∈ trivialization.target :=
    trivialization.toOpenPartialHomeomorph.map_source hSource
  have hLocalAt : ContinuousAt
      (canonicalGlobalNormalMetricSquareInChart period hPeriod anchor)
      (trivialization normal) :=
    (hLocal anchor (trivialization normal) hTarget).continuousAt
      (trivialization.toOpenPartialHomeomorph.open_target.mem_nhds hTarget)
  have hComposition := hLocalAt.comp
    (trivialization.toOpenPartialHomeomorph.continuousAt hSource)
  apply hComposition.congr_of_eventuallyEq
  filter_upwards
    [trivialization.toOpenPartialHomeomorph.open_source.mem_nhds hSource]
      with other hOther
  simp only [Function.comp_apply, canonicalGlobalNormalMetricSquareInChart]
  have hInverse :
      (differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm
          (trivialization other) = other :=
    trivialization.toOpenPartialHomeomorph.left_inv hOther
  rw [hInverse]

/-- Field-shaped continuity theorem for the final bridge record. -/
theorem canonicalGlobalOrthogonalNormalLift_continuous_metric_square
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    Continuous
      (fun normal : DifferentialNormalTotalSpace period hPeriod =>
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod normal.1)
          (canonicalGlobalOrthogonalNormalLift
            period hPeriod normal.1 normal.2)
          (canonicalGlobalOrthogonalNormalLift
            period hPeriod normal.1 normal.2)) := by
  change Continuous (canonicalGlobalNormalMetricSquare period hPeriod)
  exact canonicalGlobalNormalMetricSquare_continuous_of_local
    period hPeriod hLocal

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D
end JanusFormal
