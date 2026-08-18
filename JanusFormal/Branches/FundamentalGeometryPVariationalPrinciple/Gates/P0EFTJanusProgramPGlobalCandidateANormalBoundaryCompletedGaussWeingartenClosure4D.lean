import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussWeingartenReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryDifferentiatedOrthogonality4D

/-!
# Completed Gauss--Weingarten closure for Candidate A

This file discharges the differentiated-orthogonality hypothesis left by the
completed H10 Gauss--Weingarten reduction.  The proof reuses the already
promoted derivative of the pointwise graph-normal orthogonality and merely
identifies its scalar derivative with the historical normal-coefficient
derivative used by the reduction theorem.  No new normal, connection, frame,
chart, or physical hypothesis is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
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

local instance completedGaussWeingartenClosureCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance completedGaussWeingartenClosureCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    completedGaussWeingartenClosureOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenClosureOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenClosureEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenClosureEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- The differentiated scalar orthogonality required by the reduction theorem
is already a theorem on the smooth admissible core.  The only conversion here
is the canonical identification of the scalar-valued `mvfderiv` with the
historical scalar `mfderiv`. -/
theorem candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt_smooth
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
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt
      period hPeriod metric tensor variedMetric displacement parameter hNonNull
        outer inner boundary := by
  have hDerivative :=
    candidateANormalBoundaryMetricUnitNormalGraphTangent_derivative_zero
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg boundary outer inner
  simp_rw [candidateANormalBoundary_mvfderiv_real_eq_mfderiv] at hDerivative
  unfold candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt
  dsimp only
  simpa [
    candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient]
      using hDerivative

set_option backward.isDefEq.respectTransparency false in
/-- Unconditional completed H10 Gauss--Weingarten reduction on the smooth
admissible core.  The raw Gauss scalar is the historical Weingarten pairing
without supplying differentiated orthogonality as an external hypothesis. -/
theorem candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten
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
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary := by
  apply
    candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten_of_differentiatedOrthogonality
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent outer inner boundary patch coordinate hAt
          (hRootNonneg boundary)
  exact
    candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt_smooth
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg boundary outer inner

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
