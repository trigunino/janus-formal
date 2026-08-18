import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalEncodingReduction4D

/-!
# Completed-Gauss reduction of the final H10 scalar residue

The historical Weingarten form has already been proved equal to the completed
Candidate-A Gauss form on the smooth admissible core.  Consequently the last
scalar second-form identity does not require any new historical calculation:
it is enough to identify the completed Gauss form directly with the canonical
pulled-back shape pairing.

This gate isolates precisely that residual geometric statement and threads it
through all previously completed historical, finite-frame, trace and action
bridges.
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

local instance completedGaussCanonicalSecondFormCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance completedGaussCanonicalSecondFormCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    completedGaussCanonicalSecondFormOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussCanonicalSecondFormOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    completedGaussCanonicalSecondFormEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussCanonicalSecondFormEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Exact final geometric residue after removing the historical regular-frame
presentation.  The completed Candidate-A Gauss form must equal the induced
metric paired with the canonical shape operator on each installed generator
pair. -/
abbrev CandidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Prop :=
  CandidateANormalBoundaryMetricUnitGaussPointwiseAgreement period hPeriod
    metric tensor variedMetric displacement parameter hNonNull

set_option maxHeartbeats 4800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The already proved completed-Gauss/historical equality transports the
residual canonical identification directly to the historical second form. -/
theorem candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_of_completedGaussCanonical
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
    (hCanonical :
      CandidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_of_metricUnitGaussPointwise
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter hNonNull hCurrent hRootNonneg hCanonical

/-- Direct chart-free trace consequence of the completed-Gauss canonical
second-form identification. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_completedGaussCanonical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrentGHY :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hCanonical :
      CandidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussTraceAgreement_of_pulledBackSecondForm
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      hNonNull hCurrentGHY.1.1.2
      (candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_of_completedGaussCanonical
        period hPeriod metric hTransverse tensor variedMetric hVaried
          displacement parameter hNonNull hCurrentGHY.1 hRootNonneg
            hCanonical)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
