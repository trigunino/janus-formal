import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetric4D

/-!
# Candidate-A boundary metric from the Lorentz C² chart

The mobile-boundary actual-metric matrices are specialized to the genuine
Lorentz metric constructed by the unified chart.  No varied metric or tensor
identity is supplied separately.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzChartMetricBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The smooth regular-frame matrix is exactly the chart-constructed Lorentz
metric, with no external varied-metric witness. -/
theorem candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_lorentzChartMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain
          period hPeriod metric)
    (row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column point =
      (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation).tensor.tensor point
        (metric.frame row point) (metric.frame column point) := by
  exact
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation)
        (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
          tensor hVariation)
        row column point

/-- The completed actual-metric matrix on the moving boundary graph evaluates
the same chart-constructed Lorentz metric. -/
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_lorentzChartMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain
          period hPeriod metric)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) row column boundary =
      (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation).tensor.tensor point
        (metric.frame row point) (metric.frame column point) := by
  exact
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation)
        (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
          tensor hVariation)
        displacement parameter boundary row column

/-- Gate marker: both ambient and moving-graph Candidate-A metric matrices are
now tied to the Lorentz chart metric without a duplicate metric input. -/
theorem global_candidateA_normal_boundary_c2_lorentz_chart_metric_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain
          period hPeriod metric) :
    (∀ (row column : Fin 4) (point : EffectiveQuotient period hPeriod),
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row column point =
        (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
            hVariation).tensor.tensor point
          (metric.frame row point) (metric.frame column point)) ∧
      ∀ (displacement : SmoothNormalDisplacement period hPeriod)
        (parameter : Real) (boundary : OrientationBoundary period hPeriod)
        (row column : Fin 4),
        let point := normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
              metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              row column boundary =
          (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
              hVariation).tensor.tensor point
            (metric.frame row point) (metric.frame column point) := by
  exact ⟨fun row column point =>
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_lorentzChartMetric
        period hPeriod metric tensor hVariation row column point,
    fun displacement parameter boundary row column =>
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_lorentzChartMetric
        period hPeriod metric tensor hVariation displacement parameter boundary
          row column⟩

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzChartMetricBridge4D
end JanusFormal
