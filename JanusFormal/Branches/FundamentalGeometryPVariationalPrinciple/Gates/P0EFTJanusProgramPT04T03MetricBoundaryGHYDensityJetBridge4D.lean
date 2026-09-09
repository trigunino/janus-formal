import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03MetricBoundaryScalarGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEHGHYCancellation

/-!
# Local GHY density jets at the T04 metric-boundary frontier

This module extracts genuine second-order Banach jets of the completed
Candidate-A induced-volume density, mean curvature and GHY integrand.  Their
first slots give the exact product rule, commute with the already constructed
continuous first-sheet integral, and therefore represent the mobile GHY Euler
covector occurring in Gate 820.

The remaining geometric input is isolated componentwise: an actual boundary
trace must identify the value and first derivative of the completed volume and
mean-curvature fields with induced metric and extrinsic-curvature data.  A
Gaussian-Dirichlet specialization then recovers the existing pointwise
Einstein--Hilbert/GHY cancellation.  No global bulk Einstein residual, graph
separation theorem, or terminal T04 claim is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03MetricBoundaryGHYDensityJetBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusGaussianNormalEHGHYCancellation

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
  (metric : RegularGeneralLorentzMetric period hPeriod)

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod metric

local notation "GHYInput" => GHYCore × Real

local notation "BoundaryField" =>
  CandidateANormalBoundaryScalarField period hPeriod

local instance ghyCoreNormedAddCommGroup : NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance ghyCoreNormedSpace : NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod metric

local instance : NormedSpace Real GHYInput := Prod.normedSpace

private theorem inducedVolume_contDiffAt_two
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric) current :=
  (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation_contDiffOn_two
      period hPeriod metric).contDiffAt
    ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      hCurrent)

private theorem meanCurvature_contDiffAt_two
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric) current :=
  ((candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse).mono (fun _ h => h.1)).contDiffAt
    ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      hCurrent)

private theorem integrand_contDiffAt_two
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryGHYIntegrandFiberEvaluation
        period hPeriod einsteinScale metric) current :=
  (candidateANormalBoundaryGHYIntegrandFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse).contDiffAt
    ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      hCurrent)

/-- Genuine second jet of the completed positive induced-volume density. -/
def programPT04T03GHYInducedVolumeSecondJetAt
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    FramedSecondOrderJet GHYInput BoundaryField :=
  chartwiseSecondOrderJetAt
    (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
      period hPeriod metric) current
    (inducedVolume_contDiffAt_two period hPeriod metric current hCurrent)

/-- Genuine second jet of the completed unit-normal mean curvature. -/
def programPT04T03GHYMeanCurvatureSecondJetAt
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    FramedSecondOrderJet GHYInput BoundaryField :=
  chartwiseSecondOrderJetAt
    (candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
      period hPeriod metric) current
    (meanCurvature_contDiffAt_two period hPeriod metric hTransverse current
      hCurrent)

/-- Genuine second jet of the completed first-sheet GHY integrand. -/
def programPT04T03GHYIntegrandSecondJetAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    FramedSecondOrderJet GHYInput BoundaryField :=
  chartwiseSecondOrderJetAt
    (candidateANormalBoundaryGHYIntegrandFiberEvaluation
      period hPeriod einsteinScale metric) current
    (integrand_contDiffAt_two period hPeriod metric einsteinScale hTransverse
      current hCurrent)

@[simp] theorem programPT04T03GHYIntegrandSecondJetAt_firstDerivative
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
      hTransverse current hCurrent).firstDerivative =
      fderiv Real
        (candidateANormalBoundaryGHYIntegrandFiberEvaluation
          period hPeriod einsteinScale metric) current :=
  rfl

/-- Product-rule derivative written with the first slots of the genuine
volume and mean-curvature jets. -/
def programPT04T03GHYFactorizedIntegrandFDerivAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    GHYInput →L[Real] BoundaryField :=
  einsteinScale •
    (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current •
        (programPT04T03GHYMeanCurvatureSecondJetAt period hPeriod metric
          hTransverse current hCurrent).firstDerivative +
      candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
          period hPeriod metric current •
        (programPT04T03GHYInducedVolumeSecondJetAt period hPeriod metric
          current hCurrent).firstDerivative)

@[simp] theorem programPT04T03GHYFactorizedIntegrandFDerivAt_apply
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput)
    (boundary : OrientationBoundary period hPeriod) :
    programPT04T03GHYFactorizedIntegrandFDerivAt period hPeriod metric
        einsteinScale hTransverse current hCurrent direction boundary =
      einsteinScale *
        (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
            period hPeriod metric current boundary *
          (programPT04T03GHYMeanCurvatureSecondJetAt period hPeriod metric
            hTransverse current hCurrent).firstDerivative direction boundary +
        candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
            period hPeriod metric current boundary *
          (programPT04T03GHYInducedVolumeSecondJetAt period hPeriod metric
            current hCurrent).firstDerivative direction boundary) := by
  simp [programPT04T03GHYFactorizedIntegrandFDerivAt, smul_eq_mul]
  ring

private theorem inducedVolumeSecondJet_hasFDerivAt
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric)
      (programPT04T03GHYInducedVolumeSecondJetAt period hPeriod metric current
        hCurrent).firstDerivative current := by
  rw [show
    (programPT04T03GHYInducedVolumeSecondJetAt period hPeriod metric current
      hCurrent).firstDerivative =
      fderiv Real
        (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric) current from rfl]
  exact (inducedVolume_contDiffAt_two period hPeriod metric current hCurrent)
    |>.differentiableAt (by norm_num) |>.hasFDerivAt

private theorem meanCurvatureSecondJet_hasFDerivAt
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric)
      (programPT04T03GHYMeanCurvatureSecondJetAt period hPeriod metric
        hTransverse current hCurrent).firstDerivative current := by
  rw [show
    (programPT04T03GHYMeanCurvatureSecondJetAt period hPeriod metric
      hTransverse current hCurrent).firstDerivative =
      fderiv Real
        (candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
          period hPeriod metric) current from rfl]
  exact (meanCurvature_contDiffAt_two period hPeriod metric hTransverse current
    hCurrent) |>.differentiableAt (by norm_num) |>.hasFDerivAt

/-- Exact Banach-algebra product rule for the completed GHY integrand. -/
theorem programPT04T03GHYIntegrand_hasFDerivAt_factorized
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (candidateANormalBoundaryGHYIntegrandFiberEvaluation
        period hPeriod einsteinScale metric)
      (programPT04T03GHYFactorizedIntegrandFDerivAt period hPeriod metric
        einsteinScale hTransverse current hCurrent) current := by
  unfold candidateANormalBoundaryGHYIntegrandFiberEvaluation
    programPT04T03GHYFactorizedIntegrandFDerivAt
  exact ((inducedVolumeSecondJet_hasFDerivAt period hPeriod metric current
    hCurrent).mul
      (meanCurvatureSecondJet_hasFDerivAt period hPeriod metric hTransverse
        current hCurrent)).const_smul einsteinScale

/-- The first slot of the genuine integrand jet is exactly the factored
volume/mean-curvature product rule. -/
theorem programPT04T03GHYIntegrandSecondJet_firstDerivative_eq_factorized
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
      hTransverse current hCurrent).firstDerivative =
      programPT04T03GHYFactorizedIntegrandFDerivAt period hPeriod metric
        einsteinScale hTransverse current hCurrent := by
  have hJet : HasFDerivAt
      (candidateANormalBoundaryGHYIntegrandFiberEvaluation
        period hPeriod einsteinScale metric)
      (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
        hTransverse current hCurrent).firstDerivative current := by
    rw [programPT04T03GHYIntegrandSecondJetAt_firstDerivative]
    exact (integrand_contDiffAt_two period hPeriod metric einsteinScale
      hTransverse current hCurrent) |>.differentiableAt (by norm_num)
        |>.hasFDerivAt
  exact hJet.unique
    (programPT04T03GHYIntegrand_hasFDerivAt_factorized period hPeriod metric
      einsteinScale hTransverse current hCurrent)

/-- First-sheet integrated derivative obtained by composing the density jet
with the existing continuous integral. -/
def programPT04T03GHYFirstSheetJetEulerAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    GHYInput →L[Real] Real :=
  (candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod).comp
    (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
      hTransverse current hCurrent).firstDerivative

/-- Two-sheet integrated derivative with the established multiplicity two. -/
def programPT04T03GHYTwoSheetJetEulerAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    GHYInput →L[Real] Real :=
  (2 : Real) •
    programPT04T03GHYFirstSheetJetEulerAt period hPeriod metric einsteinScale
      hTransverse current hCurrent

theorem programPT04T03GHYFirstSheetAction_hasFDerivAt_jet
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric)
      (programPT04T03GHYFirstSheetJetEulerAt period hPeriod metric
        einsteinScale hTransverse current hCurrent) current := by
  unfold candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
    programPT04T03GHYFirstSheetJetEulerAt
  exact (candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod).hasFDerivAt.comp
    current (by
      rw [programPT04T03GHYIntegrandSecondJetAt_firstDerivative]
      exact (integrand_contDiffAt_two period hPeriod metric einsteinScale
        hTransverse current hCurrent) |>.differentiableAt (by norm_num)
          |>.hasFDerivAt)

theorem programPT04T03GHYTwoSheetAction_hasFDerivAt_jet
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric)
      (programPT04T03GHYTwoSheetJetEulerAt period hPeriod metric
        einsteinScale hTransverse current hCurrent) current := by
  unfold candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
    programPT04T03GHYTwoSheetJetEulerAt
  exact (programPT04T03GHYFirstSheetAction_hasFDerivAt_jet period hPeriod
    metric einsteinScale hTransverse current hCurrent).const_mul (2 : Real)

/-- The mobile GHY boundary Euler in Gate 820 is the integrated first slot of
the genuine density jet. -/
theorem programPT04T03MobileGHYBoundaryEuler_eq_twoSheetJet
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
        period hPeriod metric einsteinScale current =
      programPT04T03GHYTwoSheetJetEulerAt period hPeriod metric einsteinScale
        hTransverse current hCurrent := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
  exact (programPT04T03GHYTwoSheetAction_hasFDerivAt_jet period hPeriod metric
    einsteinScale hTransverse current hCurrent).fderiv

theorem programPT04T03MobileGHYBoundaryEuler_apply_eq_integratedDensityJet
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
        period hPeriod metric einsteinScale current direction =
      2 * candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
        ((programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
          einsteinScale hTransverse current hCurrent).firstDerivative
            direction) := by
  rw [programPT04T03MobileGHYBoundaryEuler_eq_twoSheetJet period hPeriod
    metric einsteinScale hTransverse current hCurrent]
  simp only [programPT04T03GHYTwoSheetJetEulerAt,
    programPT04T03GHYFirstSheetJetEulerAt,
    smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]

/-- Pointwise first variation carried by the integrand jet. -/
def programPT04T03GHYJetFirstVariationDensityAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput)
    (boundary : OrientationBoundary period hPeriod) : Real :=
  (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
    hTransverse current hCurrent).firstDerivative direction boundary

/-- Missing geometric trace data, stated componentwise rather than by assuming
the final GHY Euler identity.  It must be constructed from the Candidate-A
metric trace, normal displacement, and the scalar fiber direction. -/
structure ProgramPT04T03GHYGeometricTraceContractAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) where
  boundaryData :
    OrientationBoundary period hPeriod → NonNullBoundaryPointData
  metricVariation :
    GHYInput → OrientationBoundary period hPeriod →
      NonNullGHYMetricVariation
  inducedVolume_value : ∀ boundary,
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric current boundary =
      Real.sqrt |Matrix.det (boundaryData boundary).inducedMetric|
  orientedMeanCurvature_value : ∀ boundary,
    candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric current boundary =
      (boundaryData boundary).orientationSign *
        meanCurvatureTrace (boundaryData boundary)
  inducedVolume_firstDerivative : ∀ direction boundary,
    (programPT04T03GHYInducedVolumeSecondJetAt period hPeriod metric current
        hCurrent).firstDerivative direction boundary =
      (metricFirstJetVariation (boundaryData boundary)
        (metricVariation direction boundary)).measureVariation
  orientedMeanCurvature_firstDerivative : ∀ direction boundary,
    (programPT04T03GHYMeanCurvatureSecondJetAt period hPeriod metric
        hTransverse current hCurrent).firstDerivative direction boundary =
      (boundaryData boundary).orientationSign *
        meanCurvatureTraceVariation (boundaryData boundary)
          (metricFirstJetVariation (boundaryData boundary)
            (metricVariation direction boundary))

/-- Under the componentwise trace contract, the actual density-jet derivative
is the determinant-derived pointwise GHY first variation. -/
theorem programPT04T03GHYJetFirstVariationDensity_eq_nonNullGHY
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (trace : ProgramPT04T03GHYGeometricTraceContractAt period hPeriod metric
      einsteinScale hTransverse current hCurrent)
    (direction : GHYInput)
    (boundary : OrientationBoundary period hPeriod) :
    programPT04T03GHYJetFirstVariationDensityAt period hPeriod metric
        einsteinScale hTransverse current hCurrent direction boundary =
      nonNullGHYFirstVariation einsteinScale (trace.boundaryData boundary)
        (metricFirstJetVariation (trace.boundaryData boundary)
          (trace.metricVariation direction boundary)) := by
  unfold programPT04T03GHYJetFirstVariationDensityAt
  rw [programPT04T03GHYIntegrandSecondJet_firstDerivative_eq_factorized]
  rw [programPT04T03GHYFactorizedIntegrandFDerivAt_apply]
  rw [trace.inducedVolume_value, trace.orientedMeanCurvature_value,
    trace.inducedVolume_firstDerivative,
    trace.orientedMeanCurvature_firstDerivative]
  unfold nonNullGHYFirstVariation
  ring

/-- Additional Dirichlet trace needed to connect the local density jet to the
existing Gaussian-normal Einstein--Hilbert boundary flux. -/
structure ProgramPT04T03GHYGaussianDirichletTraceContractAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) where
  geometric : ProgramPT04T03GHYGeometricTraceContractAt period hPeriod metric
    einsteinScale hTransverse current hCurrent
  gaussianJet :
    GHYInput → OrientationBoundary period hPeriod →
      GaussianNormalDirichletJet
  metricVariation_eq : ∀ direction boundary,
    geometric.metricVariation direction boundary =
      gaussianDirichletBoundaryVariation (gaussianJet direction boundary)

/-- Pointwise EH/GHY cancellation after the missing Candidate-A Dirichlet
trace has been supplied. -/
theorem programPT04T03EHFlux_add_GHYJetDensity_eq_zero
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (trace : ProgramPT04T03GHYGaussianDirichletTraceContractAt period hPeriod
      metric einsteinScale hTransverse current hCurrent)
    (direction : GHYInput)
    (boundary : OrientationBoundary period hPeriod) :
    einsteinHilbertDirichletBoundaryFlux einsteinScale
          (trace.geometric.boundaryData boundary)
          (trace.gaussianJet direction boundary) +
        programPT04T03GHYJetFirstVariationDensityAt period hPeriod metric
          einsteinScale hTransverse current hCurrent direction boundary = 0 := by
  rw [programPT04T03GHYJetFirstVariationDensity_eq_nonNullGHY]
  rw [trace.metricVariation_eq]
  exact einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
    einsteinScale (trace.geometric.boundaryData boundary)
      (trace.gaussianJet direction boundary)

/-- Bounded-continuous representative of the realized Gaussian-normal EH
flux.  Its identification with the explicit Palatini flux uses the trace
contract below; the definition itself does not claim a bulk Euler formula. -/
def programPT04T03RealizedGaussianEHFluxDensityAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput) : BoundaryField :=
  -((programPT04T03GHYIntegrandSecondJetAt period hPeriod metric einsteinScale
    hTransverse current hCurrent).firstDerivative direction)

theorem programPT04T03RealizedGaussianEHFluxDensity_apply
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (trace : ProgramPT04T03GHYGaussianDirichletTraceContractAt period hPeriod
      metric einsteinScale hTransverse current hCurrent)
    (direction : GHYInput)
    (boundary : OrientationBoundary period hPeriod) :
    programPT04T03RealizedGaussianEHFluxDensityAt period hPeriod metric
        einsteinScale hTransverse current hCurrent direction boundary =
      einsteinHilbertDirichletBoundaryFlux einsteinScale
        (trace.geometric.boundaryData boundary)
        (trace.gaussianJet direction boundary) := by
  have hCancel := programPT04T03EHFlux_add_GHYJetDensity_eq_zero period hPeriod
    metric einsteinScale hTransverse current hCurrent trace direction boundary
  change
    -((programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
      einsteinScale hTransverse current hCurrent).firstDerivative direction
        boundary) = _
  change
    _ + (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
      einsteinScale hTransverse current hCurrent).firstDerivative direction
        boundary = 0 at hCancel
  linarith

/-- Exact cancellation after continuous integration of the realized local EH
flux and the two-sheet GHY density jet.  This is conditional on the trace
contract and is not an identification with the old bulk Euler of Gate 820. -/
theorem programPT04T03IntegratedRealizedEH_add_mobileGHY_eq_zero
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (_trace : ProgramPT04T03GHYGaussianDirichletTraceContractAt period hPeriod
      metric einsteinScale hTransverse current hCurrent)
    (direction : GHYInput) :
    2 * candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
          (programPT04T03RealizedGaussianEHFluxDensityAt period hPeriod metric
            einsteinScale hTransverse current hCurrent direction) +
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
          period hPeriod metric einsteinScale current direction = 0 := by
  rw [programPT04T03MobileGHYBoundaryEuler_apply_eq_integratedDensityJet
    period hPeriod metric einsteinScale hTransverse current hCurrent direction]
  unfold programPT04T03RealizedGaussianEHFluxDensityAt
  rw [programPT04T03GHYIntegrandSecondJetAt_firstDerivative period hPeriod
    metric einsteinScale hTransverse current hCurrent]
  rw [map_neg]
  ring

end
end P0EFTJanusProgramPT04T03MetricBoundaryGHYDensityJetBridge4D
end JanusFormal
