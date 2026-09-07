import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D

/-!
# Exact fixed-volume Einstein--Hilbert action under affine recentering

Both charts describe the same final smooth metric.  The scalar-curvature
identification uses that common metric, while the transported regular frame
preserves the stored volume.  No equality of reconstructed bundles is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusFixedVolumeEinsteinHilbertActionRecenter4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Scalar curvature agrees in both affine charts because both represent the
same final smooth metric. -/
theorem regularGeneralMetricC0ScalarCurvature_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        variation ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric
        (variation + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation)) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric
        (regularGeneralMetricSmoothC2Variation period hPeriod metric
          (variation + increment)) =
      regularGeneralMetricC0ScalarCurvature period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation)
        (regularGeneralMetricSmoothC2Variation period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            variation hVariation) increment) := by
  let recentered := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric variation hVariation
  let variedMetric := regularGeneralMetricC2LorentzChartMetric period hPeriod
    metric (variation + increment) hTotal
  have hTotalTensor :
      variedMetric.tensor = metric.metric.tensor + (variation + increment) :=
    regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
      (variation + increment) hTotal
  have hCenterTensor :
      recentered.metric.tensor = metric.metric.tensor + variation :=
    regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
      variation hVariation
  have hRecenterTensor :
      variedMetric.tensor = recentered.metric.tensor + increment := by
    rw [hTotalTensor, hCenterTensor]
    exact (add_assoc _ _ _).symm
  have hOld := regularGeneralMetricC0ScalarCurvature_smooth period hPeriod
    metric (variation + increment) variedMetric hTotalTensor hTotal.1
  have hNew := regularGeneralMetricC0ScalarCurvature_smooth period hPeriod
    recentered increment variedMetric hRecenterTensor hIncrement.1
  simpa only [regularGeneralMetricSmoothC2Variation] using hOld.trans hNew.symm

/-- The native density, including its cosmological term and stored volume,
is unchanged by affine recentering. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        variation ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric
        (variation + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation))
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric
        couplings (regularGeneralMetricSmoothC2Variation period hPeriod metric
          (variation + increment)) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation) couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            variation hVariation) increment) := by
  have hScalar := regularGeneralMetricC0ScalarCurvature_recenter period hPeriod
    metric variation increment hVariation hTotal hIncrement
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
  rw [hScalar]
  rfl

/-- Equality of the actual native fixed-volume actions on their concrete
overlapping smooth chart domains, for every finite reference measure. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        variation ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric
        (variation + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation))
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod metric
        measure couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod metric
          (variation + increment)) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          variation hVariation) measure couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            variation hVariation) increment) := by
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
  exact congrArg (regularGeneralMetricC0IntegralCLM period hPeriod measure)
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_recenter period
      hPeriod metric variation increment hVariation hTotal hIncrement couplings)

end

end P0EFTJanusFixedVolumeEinsteinHilbertActionRecenter4D
end JanusFormal
