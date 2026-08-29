import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalNormalGerm4D

/-!
# Historical regular-frame Gauss pairing for Candidate A

This file identifies the completed raw unit-normal Gauss scalar with the
regular-frame contraction of the same historical physical normal and the
already completed graph covariant acceleration.  It introduces no new
metric, normal, frame, chart, or admissibility hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 30000)
    historicalGaussOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalGaussEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- The completed raw Gauss scalar is exactly the regular-frame pairing of
its historical physical unit normal with the completed covariant graph
acceleration. -/
theorem candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalRegularPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -(∑ row : Fin 4, ∑ column : Fin 4,
        candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter
                hNonNull row boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              row column boundary *
          candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer inner column
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary) := by
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let normal := ∑ row : Fin 4,
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            row boundary •
      metric.frame row point
  have hNormal : normal =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
    simpa [normal, point] using
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_reconstructs
        period hPeriod metric variedMetric displacement parameter hNonNull
          boundary
  have hExpansion :
      variedMetric.tensor.tensor
          (normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter)) normal
          (candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
            period hPeriod metric tensor displacement parameter outer inner
              boundary) =
        ∑ row : Fin 4, ∑ column : Fin 4,
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
                period hPeriod metric variedMetric displacement parameter
                  hNonNull row boundary *
            candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                period hPeriod metric
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter)
                row column boundary *
            candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer inner column
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter) boundary := by
    unfold normal candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
      point
    rw [variedMetric.tensor.symmetric point]
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro row _
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro column _
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    rw [variedMetric.tensor.symmetric]
    ring
  rw [candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      outer inner boundary]
  rw [candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter boundary hCurrent hNonNull hRootNonneg]
  rw [← hNormal]
  exact congrArg Neg.neg hExpansion

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal