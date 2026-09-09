import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03MetricBoundaryScalarGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D

/-!
# Admissible exact residual system for the T03 Euler covector

At an admissible T03 input this module packages four exact separating primal
representations: the constrained metric-boundary scalar graph, the two finite
physical null Riesz blocks, and the zero null/joint-normalization block.  The
remaining compatible-LL covector is kept as the already proved T03 block.  The
resulting residual equations are equivalent to vanishing of the full Euler
covector.  On a genuine smooth LL lift, its equation is replaced exactly by
the existing three-equation strong LL system.

The metric-boundary carrier is a completed scalar graph.  No claim that it is
a jet-local PDE residual is made here, and this gate does not close T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03AdmissibleFourBlockResidualSystem4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D
open P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D
open P0EFTJanusProgramPT04T03MetricBoundaryScalarGraphRieszResidual4D
open P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uTest

/-- A separating representation converts continuous-covector vanishing into
its strong residual equation. -/
theorem continuousLinearMap_eq_zero_iff_separatingResidual
    {Test : Type uTest} [SeminormedAddCommGroup Test] [NormedSpace Real Test]
    (covector : Test →L[Real] Real)
    (representation :
      SeparatingPDEResidualRepresentation covector.toLinearMap) :
    covector = 0 ↔
      representation.residual = representation.zeroResidual := by
  have hCore :=
    separatingPDEResidualRepresentation_covector_eq_zero_iff representation
  constructor
  · intro hCovector
    apply hCore.mp
    apply LinearMap.ext
    intro test
    simp [hCovector]
  · intro hResidual
    have hLinear := hCore.mpr hResidual
    apply ContinuousLinearMap.ext
    intro test
    have hValue := DFunLike.congr_fun hLinear test
    simpa using hValue

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance : Measure.IsOpenPosMeasure
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
  (couplings : GlobalCandidateAActionCouplings)

local notation "Frame" =>
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase

local notation "Geometry" =>
  regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart

local notation "MetricCore" =>
  RegularGeneralMetricC2Core period hPeriod plusBase

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod Geometry
    Frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "CompatibleLL" => CompatibleLLCompletion period hPeriod

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod Geometry
    Frame couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod plusBase

local notation "GHYInput" => GHYCore × Real

local notation "AmbientInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    Geometry Frame couplings plusBase

local notation "MetricBoundaryAmbient" => OldInput × GHYInput

local notation "MetricBoundary" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore period
    hPeriod plusBase minusBase hChart couplings

local notation "CompletedCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore
    period hPeriod plusBase minusBase hChart couplings

local instance metricCoreNormedAddCommGroup : NormedAddCommGroup MetricCore :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod Frame
    plusBase.metric).normedAddCommGroup

local instance metricCoreNormedSpace : NormedSpace Real MetricCore :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod Frame plusBase.metric)

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance frontierGHYCoreNormedAddCommGroup : NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance frontierGHYCoreNormedSpace : NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace
local instance frontierMetricBoundaryAmbientSMul : SMul Real MetricBoundaryAmbient :=
  Prod.instSMul
local instance : ContinuousSMul Real MetricBoundaryAmbient := by
  apply Prod.continuousSMul
local instance : NormedSpace Real MetricBoundaryAmbient := Prod.normedSpace
local instance frontierAmbientInputSMul : SMul Real AmbientInput := Prod.instSMul
local instance : ContinuousSMul Real LLInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real BulkInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real GHYInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real AmbientInput := by apply Prod.continuousSMul
local instance : NormedSpace Real AmbientInput := Prod.normedSpace

local instance frontierCompatibleLLNormedAddCommGroup :
    NormedAddCommGroup CompatibleLL :=
  (compatibleLLCompletionSubmodule period hPeriod).normedAddCommGroup

local instance frontierCompatibleLLNormedSpace : NormedSpace Real CompatibleLL :=
  Submodule.normedSpace (compatibleLLCompletionSubmodule period hPeriod)

local instance frontierMetricBoundarySMul : SMul Real MetricBoundary :=
  SetLike.smul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance frontierMetricBoundaryNormedAddCommGroup :
    NormedAddCommGroup MetricBoundary :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance frontierMetricBoundaryNormedSpace : NormedSpace Real MetricBoundary :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance frontierMetricBoundaryContinuousSMul :
    ContinuousSMul Real MetricBoundary :=
  SMulMemClass.continuousSMul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance : NormedSpace Real CompletedCoupled := Prod.normedSpace
local instance : ContinuousSMul Real CompletedCoupled := by
  apply Prod.continuousSMul

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPosition" => FiniteNullFacePositionHilbert NullFace
local notation "NullIntrinsic" => FiniteNullFaceIntrinsicMetricHilbert NullFace
local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace
local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local instance frontierPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance frontierInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (model : FiniteNullFacePhysicalActionModel NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

local notation "FullEuler" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients

/-- Residual equation carried by Gate 822's exact scalar closed-graph
representation of the admissible metric-boundary restriction. -/
def ProgramPT04T03MetricBoundaryScalarGraphResidualEquationAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) : Prop :=
  let representation :=
    programPT04T03MetricBoundaryScalarGraphRieszRepresentationOnDomainAt
      period hPeriod plusBase minusBase hChart couplings einsteinScale
        interactionScale coefficients (data := data) (model := model)
          hTransverse input hInput
  representation.residual = representation.zeroResidual

/-- Residual equation carried by Gate 818's primal null-position Riesz
representation. -/
def ProgramPT04T03NullPositionRieszResidualEquationAt
    (input : Input) : Prop :=
  let representation :=
    programPT04T03NullPositionRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input
  representation.residual = representation.zeroResidual

/-- Residual equation carried by Gate 818's primal intrinsic-screen Riesz
representation. -/
def ProgramPT04T03NullIntrinsicRieszResidualEquationAt
    (input : Input) : Prop :=
  let representation :=
    programPT04T03NullIntrinsicRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input
  representation.residual = representation.zeroResidual

/-- Residual equation carried by Gate 825's primal null/joint-normalization
Riesz representation. -/
def ProgramPT04T03NullJointNormalizationRieszResidualEquationAt
    (input : Input) : Prop :=
  let representation :=
    programPT04T03NullJointNormalizationRieszRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input
  representation.residual = representation.zeroResidual

theorem programPT04T03MetricBoundaryEuler_eq_zero_iff_scalarGraphResidual
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ProgramPT04T03MetricBoundaryScalarGraphResidualEquationAt period hPeriod
        plusBase minusBase hChart couplings
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          (data := data) (model := model) hTransverse input hInput := by
  unfold ProgramPT04T03MetricBoundaryScalarGraphResidualEquationAt
  exact
    continuousLinearMap_eq_zero_iff_separatingResidual _
      (programPT04T03MetricBoundaryScalarGraphRieszRepresentationOnDomainAt
        period hPeriod plusBase minusBase hChart couplings einsteinScale
          interactionScale coefficients (data := data) (model := model)
            hTransverse input hInput)

theorem programPT04T03NullPositionEuler_eq_zero_iff_rieszResidual
    (input : Input) :
    programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ProgramPT04T03NullPositionRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input := by
  unfold ProgramPT04T03NullPositionRieszResidualEquationAt
  exact
    continuousLinearMap_eq_zero_iff_separatingResidual _
      (programPT04T03NullPositionRieszResidualRepresentationAt period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input)

theorem programPT04T03NullIntrinsicEuler_eq_zero_iff_rieszResidual
    (input : Input) :
    programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ProgramPT04T03NullIntrinsicRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input := by
  unfold ProgramPT04T03NullIntrinsicRieszResidualEquationAt
  exact
    continuousLinearMap_eq_zero_iff_separatingResidual _
      (programPT04T03NullIntrinsicRieszResidualRepresentationAt period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input)

theorem programPT04T03NullNormalizationEuler_eq_zero_iff_rieszResidual
    (input : Input) :
    programPT04T03NullNormalizationEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ProgramPT04T03NullJointNormalizationRieszResidualEquationAt period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input := by
  unfold ProgramPT04T03NullJointNormalizationRieszResidualEquationAt
  exact
    continuousLinearMap_eq_zero_iff_separatingResidual _
      (programPT04T03NullJointNormalizationRieszRepresentationAt period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input)

/-- The four exact separating residual equations combined with the existing
compatible-LL Euler equation.  The metric member is a scalar graph equation;
no jet-local interpretation is asserted. -/
def ProgramPT04T03AdmissibleFourBlockResidualSystemAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) : Prop :=
  ((ProgramPT04T03MetricBoundaryScalarGraphResidualEquationAt period hPeriod
        plusBase minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse input hInput ∧
      programPT04T03CompatibleLLEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0) ∧
    (ProgramPT04T03NullPositionRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input ∧
      ProgramPT04T03NullIntrinsicRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input)) ∧
  ProgramPT04T03NullJointNormalizationRieszResidualEquationAt period hPeriod
    plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients input

/-- At every admissible T03 input, the full Euler equation is exactly the
assembled scalar-graph, LL, null-position, null-intrinsic and normalization
residual system. -/
theorem programPT04T03Euler_eq_zero_iff_admissibleFourBlockResidualSystem
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    FullEuler input = 0 ↔
      ProgramPT04T03AdmissibleFourBlockResidualSystemAt period hPeriod plusBase
        minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse input hInput := by
  have hNormalizationResidual :
      ProgramPT04T03NullJointNormalizationRieszResidualEquationAt period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input :=
    (programPT04T03NullNormalizationEuler_eq_zero_iff_rieszResidual period
      hPeriod plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input).mp
      (programPT04T03NullNormalizationEulerRestrictionAt_eq_zero period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input)
  rw [programPT04T03Euler_eq_zero_iff_four_restrictions,
    programPT04T03MetricBoundaryEuler_eq_zero_iff_scalarGraphResidual
      period hPeriod plusBase minusBase hChart couplings (data := data)
        (model := model) (einsteinScale := einsteinScale)
        (interactionScale := interactionScale) (coefficients := coefficients)
        hTransverse input hInput,
    programPT04T03NullPositionEuler_eq_zero_iff_rieszResidual,
    programPT04T03NullIntrinsicEuler_eq_zero_iff_rieszResidual]
  unfold ProgramPT04T03AdmissibleFourBlockResidualSystemAt
  constructor
  · intro hResiduals
    exact ⟨hResiduals, hNormalizationResidual⟩
  · intro hResiduals
    exact hResiduals.1

/-- Smooth-LL variant of the assembled system: its LL component is the actual
three-equation strong system already proved on smooth lifts. -/
def ProgramPT04T03AdmissibleFourBlockStrongResidualSystemAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (metricBoundary : MetricBoundary)
    (fields : IndependentFields period hPeriod)
    (normalization : NullNormalization)
    (nullPhysical : NullPhysical)
    (hInput :
      programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
          couplings metricBoundary fields normalization nullPhysical ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
          period hPeriod plusBase minusBase hChart couplings model) : Prop :=
  let input :=
    programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
      couplings metricBoundary fields normalization nullPhysical
  ((ProgramPT04T03MetricBoundaryScalarGraphResidualEquationAt period hPeriod
        plusBase minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse input hInput ∧
      ProgramPT04T03CompatibleLLStrongSystemAt period hPeriod fields) ∧
    (ProgramPT04T03NullPositionRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input ∧
      ProgramPT04T03NullIntrinsicRieszResidualEquationAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input)) ∧
  ProgramPT04T03NullJointNormalizationRieszResidualEquationAt period hPeriod
    plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients input

theorem programPT04T03ResidualSystem_smoothLL_iff_strong
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (metricBoundary : MetricBoundary)
    (fields : IndependentFields period hPeriod)
    (normalization : NullNormalization)
    (nullPhysical : NullPhysical)
    (hInput :
      programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
          couplings metricBoundary fields normalization nullPhysical ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
          period hPeriod plusBase minusBase hChart couplings model) :
    ProgramPT04T03AdmissibleFourBlockResidualSystemAt period hPeriod plusBase
        minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse
          (programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
            couplings metricBoundary fields normalization nullPhysical)
          hInput ↔
      ProgramPT04T03AdmissibleFourBlockStrongResidualSystemAt period hPeriod
        plusBase minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse metricBoundary fields normalization nullPhysical hInput := by
  unfold ProgramPT04T03AdmissibleFourBlockResidualSystemAt
    ProgramPT04T03AdmissibleFourBlockStrongResidualSystemAt
  rw [programPT04T03CompatibleLLEulerRestriction_smooth_eq_zero_iff_strong
    period hPeriod plusBase minusBase hChart couplings data model
      einsteinScale interactionScale coefficients hTransverse metricBoundary
        fields normalization nullPhysical hInput]

/-- On an admissible smooth LL input, the full T03 Euler equation is equivalent
to the four residual equations and the true LL strong system. -/
theorem programPT04T03Euler_smoothLL_eq_zero_iff_admissibleFourBlockStrongResidualSystem
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (metricBoundary : MetricBoundary)
    (fields : IndependentFields period hPeriod)
    (normalization : NullNormalization)
    (nullPhysical : NullPhysical)
    (hInput :
      programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
          couplings metricBoundary fields normalization nullPhysical ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
          period hPeriod plusBase minusBase hChart couplings model) :
    FullEuler
        (programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
          couplings metricBoundary fields normalization nullPhysical) = 0 ↔
      ProgramPT04T03AdmissibleFourBlockStrongResidualSystemAt period hPeriod
        plusBase minusBase hChart couplings (data := data) (model := model)
          (einsteinScale := einsteinScale)
          (interactionScale := interactionScale) (coefficients := coefficients)
          hTransverse metricBoundary fields normalization nullPhysical hInput :=
  (programPT04T03Euler_eq_zero_iff_admissibleFourBlockResidualSystem period
    hPeriod plusBase minusBase hChart couplings (data := data) (model := model)
      (einsteinScale := einsteinScale)
      (interactionScale := interactionScale) (coefficients := coefficients)
      hTransverse
      (programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
        couplings metricBoundary fields normalization nullPhysical)
      hInput).trans
    (programPT04T03ResidualSystem_smoothLL_iff_strong period hPeriod plusBase
      minusBase hChart couplings (data := data) (model := model)
        (einsteinScale := einsteinScale)
        (interactionScale := interactionScale) (coefficients := coefficients)
        hTransverse metricBoundary fields normalization nullPhysical hInput)

end

end
end P0EFTJanusProgramPT04T03AdmissibleFourBlockResidualSystem4D
end JanusFormal
