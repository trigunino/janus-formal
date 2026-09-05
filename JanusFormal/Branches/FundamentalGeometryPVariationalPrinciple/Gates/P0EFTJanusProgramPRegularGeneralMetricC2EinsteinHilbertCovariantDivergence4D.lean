import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D

/-! # Exact C² Einstein--Hilbert derivative with covariant divergence -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertCovariantDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertPalatiniDensity4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

/-- Exact physical C² EH density: Einstein contraction plus the covariant
divergence of the concrete Palatini vector. -/
theorem regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_divergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      (metric.volume point / (2 * couplings.gravitationalCoupling)) *
        (tensorPairing
            (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
              metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)
            (einsteinTensorAt
              (regularFrameMetricMatrixMap period hPeriod metric point)
              (regularGeneralMetricC0InverseMetricMatrixAt
                period hPeriod metric 0 point)
              (regularGeneralMetricC0RicciMatrixAt
                period hPeriod metric 0 point)
              couplings.cosmologicalConstant) +
          regularFramePalatiniVectorCovariantDivergence
            (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
              period hPeriod metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)) := by
  rw [regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_palatini]
  rw [regularGeneralMetricC0PalatiniScalarVelocity_eq_covariantDivergence]

/-- Integrated form of the exact Einstein-plus-divergence derivative. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_divergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      ∫ point,
        (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          (tensorPairing
              (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
                metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)
              (einsteinTensorAt
                (regularFrameMetricMatrixMap period hPeriod metric point)
                (regularGeneralMetricC0InverseMetricMatrixAt
                  period hPeriod metric 0 point)
                (regularGeneralMetricC0RicciMatrixAt
                  period hPeriod metric 0 point)
                couplings.cosmologicalConstant) +
            regularFramePalatiniVectorCovariantDivergence
              (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
                period hPeriod metric
                (regularGeneralMetricC2SmoothDirection
                  period hPeriod metric tensor) point)) ∂measure := by
  rw [regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_palatini]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularGeneralMetricC0PalatiniScalarVelocity_eq_covariantDivergence]

/-- Gate marker for the fully concrete Einstein-plus-Palatini-divergence
density. -/
theorem regular_general_metric_c2_einstein_hilbert_covariant_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) point =
      (metric.volume point / (2 * couplings.gravitationalCoupling)) *
        (tensorPairing
            (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
              metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)
            (einsteinTensorAt
              (regularFrameMetricMatrixMap period hPeriod metric point)
              (regularGeneralMetricC0InverseMetricMatrixAt
                period hPeriod metric 0 point)
              (regularGeneralMetricC0RicciMatrixAt
                period hPeriod metric 0 point)
              couplings.cosmologicalConstant) +
          regularFramePalatiniVectorCovariantDivergence
            (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
              period hPeriod metric
              (regularGeneralMetricC2SmoothDirection
                period hPeriod metric tensor) point)) :=
  regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_divergence
    period hPeriod metric couplings tensor point

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertCovariantDivergence4D
end JanusFormal
