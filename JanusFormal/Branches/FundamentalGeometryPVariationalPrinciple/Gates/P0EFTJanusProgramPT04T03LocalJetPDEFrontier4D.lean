import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D

/-!
# Exact T03 local jet-PDE frontier for T04

This file restricts the exact T03 Euler covector to its four physical blocks.
The compatible LL block is connected to its proved strong equations on smooth
lifts.  The coupled metric/boundary and two physical null residuals remain
explicitly open; no local equation or Helmholtz identity is postulated for
them.  The null-normalization direction is recorded separately as an exact
action-independent direction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
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

/-- Insert one metric/GHY graph direction into the exact T03 tangent. -/
def programPT04T03MetricBoundaryInjection : MetricBoundary →L[Real] Input :=
  (ContinuousLinearMap.inl Real PriorInput NullPhysical).comp
    ((ContinuousLinearMap.inl Real CompletedCoupled NullNormalization).comp
      (ContinuousLinearMap.inl Real MetricBoundary CompatibleLL))

/-- Insert one compatible LL direction into the exact T03 tangent. -/
def programPT04T03CompatibleLLInjection : CompatibleLL →L[Real] Input :=
  (ContinuousLinearMap.inl Real PriorInput NullPhysical).comp
    ((ContinuousLinearMap.inl Real CompletedCoupled NullNormalization).comp
      (ContinuousLinearMap.inr Real MetricBoundary CompatibleLL))

/-- Insert one null-generator normalization direction. -/
def programPT04T03NullNormalizationInjection : NullNormalization →L[Real] Input :=
  (ContinuousLinearMap.inl Real PriorInput NullPhysical).comp
    (ContinuousLinearMap.inr Real CompletedCoupled NullNormalization)

/-- Insert one physical null-position direction. -/
def programPT04T03NullPositionInjection : NullPosition →L[Real] Input :=
  (ContinuousLinearMap.inr Real PriorInput NullPhysical).comp
    (ContinuousLinearMap.inl Real NullPosition NullIntrinsic)

/-- Insert one intrinsic null-screen direction. -/
def programPT04T03NullIntrinsicInjection : NullIntrinsic →L[Real] Input :=
  (ContinuousLinearMap.inr Real PriorInput NullPhysical).comp
    (ContinuousLinearMap.inr Real NullPosition NullIntrinsic)

@[simp] theorem programPT04T03MetricBoundaryInjection_apply
    (direction : MetricBoundary) :
    programPT04T03MetricBoundaryInjection (NullFace := NullFace) period hPeriod
        plusBase minusBase hChart couplings direction =
      (((direction, 0), 0), 0) :=
  rfl

@[simp] theorem programPT04T03CompatibleLLInjection_apply
    (direction : CompatibleLL) :
    programPT04T03CompatibleLLInjection (NullFace := NullFace) period hPeriod
        plusBase minusBase hChart couplings direction =
      (((0, direction), 0), 0) :=
  rfl

@[simp] theorem programPT04T03NullNormalizationInjection_apply
    (direction : NullNormalization) :
    programPT04T03NullNormalizationInjection period hPeriod plusBase minusBase
        hChart couplings direction = ((0, direction), 0) :=
  rfl

@[simp] theorem programPT04T03NullPositionInjection_apply
    (direction : NullPosition) :
    programPT04T03NullPositionInjection period hPeriod plusBase minusBase hChart
        couplings direction = (0, (direction, 0)) :=
  rfl

@[simp] theorem programPT04T03NullIntrinsicInjection_apply
    (direction : NullIntrinsic) :
    programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase hChart
        couplings direction = (0, (0, direction)) :=
  rfl

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

/-- Exact T03 Euler covector restricted to metric/GHY graph directions. -/
def programPT04T03MetricBoundaryEulerRestrictionAt (input : Input) :
    MetricBoundary →L[Real] Real :=
  (FullEuler input).comp
    (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
      hChart couplings)

/-- Exact T03 Euler covector restricted to compatible LL directions. -/
def programPT04T03CompatibleLLEulerRestrictionAt (input : Input) :
    CompatibleLL →L[Real] Real :=
  (FullEuler input).comp
    (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
      hChart couplings)

/-- Exact T03 Euler covector restricted to physical null-position directions. -/
def programPT04T03NullPositionEulerRestrictionAt (input : Input) :
    NullPosition →L[Real] Real :=
  (FullEuler input).comp
    (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
      hChart couplings)

/-- Exact T03 Euler covector restricted to intrinsic null-screen directions. -/
def programPT04T03NullIntrinsicEulerRestrictionAt (input : Input) :
    NullIntrinsic →L[Real] Real :=
  (FullEuler input).comp
    (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
      hChart couplings)

/-- Exact T03 Euler covector restricted to null-normalization directions. -/
def programPT04T03NullNormalizationEulerRestrictionAt (input : Input) :
    NullNormalization →L[Real] Real :=
  (FullEuler input).comp
    (programPT04T03NullNormalizationInjection period hPeriod plusBase minusBase
      hChart couplings)

theorem programPT04T03MetricBoundaryEulerRestrictionAt_eq
    (input : Input) :
    programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input.1.1 := by
  apply ContinuousLinearMap.ext
  intro direction
  simp [programPT04T03MetricBoundaryEulerRestrictionAt,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection,
    ContinuousLinearMap.comp_apply]

theorem programPT04T03CompatibleLLEulerRestrictionAt_eq
    (input : Input) :
    programPT04T03CompatibleLLEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler period
        hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input.1.1 := by
  apply ContinuousLinearMap.ext
  intro direction
  simp [programPT04T03CompatibleLLEulerRestrictionAt,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection,
    ContinuousLinearMap.comp_apply]

theorem programPT04T03NullPositionEulerRestrictionAt_eq
    (input : Input) :
    programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input =
      finiteNullFacePhysicalPositionEuler model input.2 := by
  apply ContinuousLinearMap.ext
  intro direction
  simp [programPT04T03NullPositionEulerRestrictionAt,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection,
    finiteNullFacePhysicalPositionEuler, ContinuousLinearMap.comp_apply]

theorem programPT04T03NullIntrinsicEulerRestrictionAt_eq
    (input : Input) :
    programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      finiteNullFacePhysicalIntrinsicEuler model input.2 := by
  apply ContinuousLinearMap.ext
  intro direction
  simp [programPT04T03NullIntrinsicEulerRestrictionAt,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection,
    finiteNullFacePhysicalIntrinsicEuler, ContinuousLinearMap.comp_apply]

/-- Null-generator normalization is an exact action-independent T03 direction. -/
theorem programPT04T03NullNormalizationEulerRestrictionAt_eq_zero
    (input : Input) :
    programPT04T03NullNormalizationEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 := by
  apply ContinuousLinearMap.ext
  intro direction
  simp [programPT04T03NullNormalizationEulerRestrictionAt,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection,
    ContinuousLinearMap.comp_apply]

/-- Every exact T03 direction is the sum of the four physical block directions
and its separate null-normalization direction. -/
theorem programPT04T03_direction_decomposition (direction : Input) :
    direction =
      programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
          hChart couplings direction.1.1.1 +
        programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
          hChart couplings direction.1.1.2 +
        programPT04T03NullNormalizationInjection period hPeriod plusBase
          minusBase hChart couplings direction.1.2 +
        programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings direction.2.1 +
        programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings direction.2.2 := by
  rcases direction with ⟨⟨⟨metricBoundary, ll⟩, normalization⟩,
    ⟨position, intrinsic⟩⟩
  change
    (((metricBoundary, ll), normalization), (position, intrinsic)) =
      (((metricBoundary, 0), 0), 0) +
        (((0, ll), 0), 0) +
        ((0, normalization), 0) +
        (0, (position, 0)) +
        (0, (0, intrinsic))
  simp

/-- The four physical restrictions exhaust vanishing of the exact T03 Euler
covector; the fifth product coordinate is annihilated identically. -/
theorem programPT04T03Euler_eq_zero_iff_four_restrictions
    (input : Input) :
    FullEuler input = 0 ↔
      (programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input = 0 ∧
        programPT04T03CompatibleLLEulerRestrictionAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input = 0) ∧
      (programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input = 0 ∧
        programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input = 0) := by
  have hCore :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_zero_iff_four_blocks
      period hPeriod plusBase minusBase hChart couplings data model
        einsteinScale interactionScale coefficients input
  have hMetric :=
    programPT04T03MetricBoundaryEulerRestrictionAt_eq period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input
  have hLL :=
    programPT04T03CompatibleLLEulerRestrictionAt_eq period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input
  have hPosition :=
    programPT04T03NullPositionEulerRestrictionAt_eq period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input
  have hIntrinsic :=
    programPT04T03NullIntrinsicEulerRestrictionAt_eq period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input
  constructor
  · intro hEuler
    rcases hCore.mp hEuler with ⟨⟨hMetricZero, hLLZero⟩,
      ⟨hPositionZero, hIntrinsicZero⟩⟩
    exact
      ⟨⟨hMetric.trans hMetricZero, hLL.trans hLLZero⟩,
        ⟨hPosition.trans hPositionZero, hIntrinsic.trans hIntrinsicZero⟩⟩
  · rintro ⟨⟨hMetricZero, hLLZero⟩, ⟨hPositionZero, hIntrinsicZero⟩⟩
    exact hCore.mpr
      ⟨⟨hMetric.symm.trans hMetricZero, hLL.symm.trans hLLZero⟩,
        ⟨hPosition.symm.trans hPositionZero,
          hIntrinsic.symm.trans hIntrinsicZero⟩⟩

/-- The already proved local three-equation LL system. -/
def ProgramPT04T03CompatibleLLStrongSystemAt
    (fields : IndependentFields period hPeriod) : Prop :=
  (∀ point : EffectiveThroat period hPeriod,
      ptSymmetricLLAuxMetricStrongResidual period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields point = 0) ∧
    (∀ point : EffectiveThroat period hPeriod,
      llMeasureStrongResidual period hPeriod fields point = 0) ∧
    SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (smoothLLStrongRegularity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)) fields

/-- Exact T03 input whose compatible LL coordinate is a genuine smooth lift. -/
def programPT04T03SmoothLLInput
    (metricBoundary : MetricBoundary)
    (fields : IndependentFields period hPeriod)
    (normalization : NullNormalization)
    (nullPhysical : NullPhysical) : Input :=
  (((metricBoundary,
      smoothToCompatibleLLCompletion period hPeriod
        (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
    normalization), nullPhysical)

/-- On genuine smooth LL lifts, the exact T03 LL restriction is precisely the
proved three-equation strong system. -/
theorem programPT04T03CompatibleLLEulerRestriction_smooth_eq_zero_iff_strong
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
    programPT04T03CompatibleLLEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients
          (programPT04T03SmoothLLInput period hPeriod plusBase minusBase hChart
            couplings metricBoundary fields normalization nullPhysical) = 0 ↔
      ProgramPT04T03CompatibleLLStrongSystemAt period hPeriod fields := by
  rw [programPT04T03CompatibleLLEulerRestrictionAt_eq]
  simpa [programPT04T03SmoothLLInput,
    ProgramPT04T03CompatibleLLStrongSystemAt] using
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler_smooth_eq_zero_iff_strong
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients hTransverse metricBoundary fields hInput.1.1)

/-- Exact reason why a local residual has not yet been installed. -/
inductive ProgramPT04T03OpenLocalJetPDEBlock where
  | metricBoundaryGraph
  | nullPosition
  | nullIntrinsic

universe uWitness

/-- A local residual is either supplied with its separating proof or remains
an explicitly named frontier. -/
inductive ProgramPT04T03LocalJetPDEAvailability
    (Witness : Type uWitness) : Type uWitness where
  | available (witness : Witness)
  | openFrontier (block : ProgramPT04T03OpenLocalJetPDEBlock)

/-- Missing separating metric/boundary residual family on the exact T03 core. -/
def ProgramPT04T03MetricBoundaryLocalPDEWitness : Type (uNull + 1) :=
  ∀ input : Input,
    SeparatingPDEResidualRepresentation.{_, uNull} (Test := MetricBoundary)
      (programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap

/-- Missing separating null-position residual family on the exact T03 core. -/
def ProgramPT04T03NullPositionLocalPDEWitness : Type (uNull + 1) :=
  ∀ input : Input,
    SeparatingPDEResidualRepresentation.{_, uNull} (Test := NullPosition)
      (programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap

/-- Missing separating intrinsic null-screen residual family on the exact T03
core. -/
def ProgramPT04T03NullIntrinsicLocalPDEWitness : Type (uNull + 1) :=
  ∀ input : Input,
    SeparatingPDEResidualRepresentation.{_, uNull} (Test := NullIntrinsic)
      (programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap

/-- Typed packet for the three genuinely open local residual families.  The LL,
normalization, direction-decomposition and four-block results remain the public
theorems above instead of being duplicated as structure fields. -/
structure ProgramPT04T03LocalJetPDEFrontier where
  metricBoundaryLocalPDE :
    ProgramPT04T03LocalJetPDEAvailability
      (ProgramPT04T03MetricBoundaryLocalPDEWitness period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients)
  nullPositionLocalPDE :
    ProgramPT04T03LocalJetPDEAvailability
      (ProgramPT04T03NullPositionLocalPDEWitness period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients)
  nullIntrinsicLocalPDE :
    ProgramPT04T03LocalJetPDEAvailability
      (ProgramPT04T03NullIntrinsicLocalPDEWitness period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients)

/-- The current exact frontier packet leaves the three missing local residual
families open without a placeholder equation. -/
def programPT04T03LocalJetPDEFrontier
    : ProgramPT04T03LocalJetPDEFrontier period hPeriod plusBase minusBase hChart
      couplings data model einsteinScale interactionScale coefficients where
  metricBoundaryLocalPDE := .openFrontier .metricBoundaryGraph
  nullPositionLocalPDE := .openFrontier .nullPosition
  nullIntrinsicLocalPDE := .openFrontier .nullIntrinsic

end

end
end P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D
end JanusFormal
