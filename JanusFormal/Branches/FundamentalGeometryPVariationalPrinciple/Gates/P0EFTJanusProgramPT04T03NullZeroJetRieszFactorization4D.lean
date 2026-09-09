import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalMultiindexJetTower4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D

/-!
# Finite zero-jet factorization of the T03 null and joint residuals

The exact T03 null state consists of one position coefficient and three
intrinsic-screen coefficients per supplied null face.  This module embeds that
finite state in the order-zero member of the four-dimensional multi-index jet
tower and records its continuous coordinate projections.  The two nonzero
physical residuals are exactly the primal Riesz residuals of Gate 818.  The
normalization coordinate, which carries the simultaneous null-face/joint
reparametrization, has the exact zero Riesz residual already forced by T03.

This is only a finite face-labelled zero-jet factorization.  It supplies no
spacetime embedding/screen derivative formula and does not close terminal T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusProgramPPhysicalMultiindexJetTower4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D
open P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uFiber uIndex

/-- Embed one fiber value as an honest order-zero four-dimensional jet. -/
def finiteOrderZeroJet4D {Fiber : Type uFiber} (value : Fiber) :
    TruncatedMultiindexJet4D Fiber 0 :=
  fun _ => value

/-- Evaluation of an order-zero jet at the zero multi-index. -/
def finiteOrderZeroJetValue4D {Fiber : Type uFiber}
    (jet : TruncatedMultiindexJet4D Fiber 0) : Fiber :=
  jet ⟨0, by simp⟩

@[simp] theorem finiteOrderZeroJetValue4D_of_value
    {Fiber : Type uFiber} (value : Fiber) :
    finiteOrderZeroJetValue4D (finiteOrderZeroJet4D value) = value :=
  rfl

/-- Order-zero jet carrier of the finite physical null-face state. -/
abbrev FiniteNullFacePhysicalZeroJet4D
    (NullFace : Type uIndex) [Fintype NullFace] :=
  TruncatedMultiindexJet4D (FiniteNullFacePhysicalHilbert NullFace) 0

/-- The finite physical null state viewed as a zero jet. -/
def finiteNullFacePhysicalZeroJet4D
    {NullFace : Type uIndex} [Fintype NullFace]
    (state : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePhysicalZeroJet4D NullFace :=
  finiteOrderZeroJet4D state

/-- Continuous projection to the position coefficient on every null face. -/
def finiteNullFacePositionZeroJetProjection
    {NullFace : Type uIndex} [Fintype NullFace] :
    FiniteNullFacePhysicalHilbert NullFace →L[Real]
      FiniteNullFacePositionHilbert NullFace :=
  ContinuousLinearMap.fst Real
    (FiniteNullFacePositionHilbert NullFace)
    (FiniteNullFaceIntrinsicMetricHilbert NullFace)

/-- Continuous projection to the three intrinsic-screen coefficients. -/
def finiteNullFaceIntrinsicZeroJetProjection
    {NullFace : Type uIndex} [Fintype NullFace] :
    FiniteNullFacePhysicalHilbert NullFace →L[Real]
      FiniteNullFaceIntrinsicMetricHilbert NullFace :=
  ContinuousLinearMap.snd Real
    (FiniteNullFacePositionHilbert NullFace)
    (FiniteNullFaceIntrinsicMetricHilbert NullFace)

/-- Scalar zero-jet extractor for one null-position coefficient. -/
def finiteNullFacePositionZeroJetCoordinate
    {NullFace : Type uIndex} [Fintype NullFace] (face : NullFace) :
    FiniteNullFacePhysicalHilbert NullFace →L[Real] Real :=
  (EuclideanSpace.proj (𝕜 := Real) face).comp
    finiteNullFacePositionZeroJetProjection

/-- Scalar zero-jet extractor for one intrinsic-screen coefficient. -/
def finiteNullFaceIntrinsicZeroJetCoordinate
    {NullFace : Type uIndex} [Fintype NullFace]
    (face : NullFace) (coefficient : Fin 3) :
    FiniteNullFacePhysicalHilbert NullFace →L[Real] Real :=
  (EuclideanSpace.proj (𝕜 := Real) (face, coefficient)).comp
    finiteNullFaceIntrinsicZeroJetProjection

@[simp] theorem finiteNullFacePositionZeroJetProjection_apply
    {NullFace : Type uIndex} [Fintype NullFace]
    (state : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFacePositionZeroJetProjection state = state.1 :=
  rfl

@[simp] theorem finiteNullFaceIntrinsicZeroJetProjection_apply
    {NullFace : Type uIndex} [Fintype NullFace]
    (state : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFaceIntrinsicZeroJetProjection state = state.2 :=
  rfl

@[simp] theorem finiteNullFacePositionZeroJetCoordinate_apply
    {NullFace : Type uIndex} [Fintype NullFace]
    (state : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    finiteNullFacePositionZeroJetCoordinate face state = state.1 face :=
  rfl

@[simp] theorem finiteNullFaceIntrinsicZeroJetCoordinate_apply
    {NullFace : Type uIndex} [Fintype NullFace]
    (state : FiniteNullFacePhysicalHilbert NullFace)
    (face : NullFace) (coefficient : Fin 3) :
    finiteNullFaceIntrinsicZeroJetCoordinate face coefficient state =
      state.2 (face, coefficient) :=
  rfl

/-- Product of the two primal finite Riesz residuals constructed in Gate 818. -/
def finiteNullFacePhysicalRieszResidualState
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (state : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePhysicalHilbert NullFace :=
  (finiteNullFacePhysicalPositionRieszResidual model state,
    finiteNullFacePhysicalIntrinsicRieszResidual model state)

/-- Gate 818's paired primal residual, placed in the order-zero jet carrier. -/
def finiteNullFacePhysicalRieszZeroJet4D
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (state : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePhysicalZeroJet4D NullFace :=
  finiteOrderZeroJet4D (finiteNullFacePhysicalRieszResidualState model state)

@[simp] theorem finiteNullFacePhysicalRieszZeroJet4D_position
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (state : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    finiteNullFacePositionZeroJetCoordinate face
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D model state)) =
      finiteNullFacePhysicalPositionRieszResidual model state face :=
  rfl

@[simp] theorem finiteNullFacePhysicalRieszZeroJet4D_intrinsic
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (state : FiniteNullFacePhysicalHilbert NullFace)
    (face : NullFace) (coefficient : Fin 3) :
    finiteNullFaceIntrinsicZeroJetCoordinate face coefficient
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D model state)) =
      finiteNullFacePhysicalIntrinsicRieszResidual model state
        (face, coefficient) :=
  rfl

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

/-- Continuous projection from the exact T03 core to its finite physical
null-face state. -/
def programPT04T03NullPhysicalStateProjection :
    Input →L[Real] NullPhysical :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection
    period hPeriod plusBase minusBase hChart couplings

@[simp] theorem programPT04T03NullPhysicalStateProjection_apply
    (input : Input) :
    programPT04T03NullPhysicalStateProjection period hPeriod plusBase minusBase
        hChart couplings input =
      input.2 :=
  rfl

/-- The exact T03 physical null state embedded as a finite order-zero jet. -/
def programPT04T03NullPhysicalZeroJetExtractor (input : Input) :
    FiniteNullFacePhysicalZeroJet4D NullFace :=
  finiteNullFacePhysicalZeroJet4D
    (programPT04T03NullPhysicalStateProjection period hPeriod plusBase minusBase
      hChart couplings input)

@[simp] theorem programPT04T03NullPhysicalZeroJetExtractor_value
    (input : Input) :
    finiteOrderZeroJetValue4D
        (programPT04T03NullPhysicalZeroJetExtractor period hPeriod plusBase
          minusBase hChart couplings input) =
      input.2 :=
  rfl

/-- The normalization coordinate together with the two physical null
coordinates is the finite null-face/joint sector of the exact T03 core. -/
abbrev ProgramPT04T03NullJointZeroJet4D :=
  TruncatedMultiindexJet4D (NullNormalization × NullPhysical) 0

/-- Explicit order-zero extraction of the T03 null-face/joint sector. -/
def programPT04T03NullJointZeroJetExtractor (input : Input) :
    ProgramPT04T03NullJointZeroJet4D (NullFace := NullFace) :=
  finiteOrderZeroJet4D
    (input.1.2,
      programPT04T03NullPhysicalStateProjection period hPeriod plusBase minusBase
        hChart couplings input)

@[simp] theorem programPT04T03NullJointZeroJetExtractor_value
    (input : Input) :
    finiteOrderZeroJetValue4D
        (programPT04T03NullJointZeroJetExtractor period hPeriod plusBase
          minusBase hChart couplings input) =
      (input.1.2, input.2) :=
  rfl

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (model : FiniteNullFacePhysicalActionModel NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

/-- Primal Riesz residual of the T03 null-face/joint normalization direction. -/
def programPT04T03NullJointNormalizationRieszResidualAt
    (input : Input) : NullNormalization :=
  finiteEuclideanRieszResidual
    (programPT04T03NullNormalizationEulerRestrictionAt period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input)

/-- Face/joint reparametrization cancellation makes the normalization Riesz
residual exactly zero. -/
theorem programPT04T03NullJointNormalizationRieszResidualAt_eq_zero
    (input : Input) :
    programPT04T03NullJointNormalizationRieszResidualAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      0 := by
  unfold programPT04T03NullJointNormalizationRieszResidualAt
  apply (finiteEuclideanCovector_eq_zero_iff_rieszResidual _).mp
  exact
    programPT04T03NullNormalizationEulerRestrictionAt_eq_zero period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input

/-- Separating primal representation of the exact zero normalization block. -/
def programPT04T03NullJointNormalizationRieszRepresentationAt
    (input : Input) :
    SeparatingPDEResidualRepresentation
      (programPT04T03NullNormalizationEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap :=
  finiteEuclideanRieszResidualRepresentation _

/-- The two Gate 818 residuals assembled in the physical null state. -/
def programPT04T03NullPhysicalRieszResidualStateAt
    (input : Input) : NullPhysical :=
  (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase minusBase
      hChart couplings data model einsteinScale interactionScale coefficients
        input,
    programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase minusBase
      hChart couplings data model einsteinScale interactionScale coefficients
        input)

/-- Exact factorization of both T03 physical null residuals through the finite
physical-state projection. -/
theorem programPT04T03NullPhysicalRieszResidualStateAt_eq_physical
    (input : Input) :
    programPT04T03NullPhysicalRieszResidualStateAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      finiteNullFacePhysicalRieszResidualState model
        (programPT04T03NullPhysicalStateProjection period hPeriod plusBase
          minusBase hChart couplings input) := by
  apply Prod.ext
  · exact
      programPT04T03NullPositionRieszResidualAt_eq_physical period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input
  · exact
      programPT04T03NullIntrinsicRieszResidualAt_eq_physical period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input

/-- The exact normalization, position and intrinsic Riesz residuals in one
finite null-face/joint order-zero jet. -/
def programPT04T03NullJointRieszZeroJetAt
    (input : Input) :
    ProgramPT04T03NullJointZeroJet4D (NullFace := NullFace) :=
  finiteOrderZeroJet4D
    (programPT04T03NullJointNormalizationRieszResidualAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input,
      programPT04T03NullPhysicalRieszResidualStateAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input)

/-- Exact order-zero factorization: the joint-normalization component vanishes,
while both physical components are Gate 818's Riesz residual evaluated after
the concrete T03 null-state projection. -/
theorem programPT04T03NullJointRieszZeroJetAt_factorization
    (input : Input) :
    programPT04T03NullJointRieszZeroJetAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input =
      finiteOrderZeroJet4D
        (0, finiteNullFacePhysicalRieszResidualState model
          (finiteOrderZeroJetValue4D
            (programPT04T03NullPhysicalZeroJetExtractor period hPeriod plusBase
              minusBase hChart couplings input))) := by
  funext index
  apply Prod.ext
  · exact
      programPT04T03NullJointNormalizationRieszResidualAt_eq_zero period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input
  · exact
      programPT04T03NullPhysicalRieszResidualStateAt_eq_physical period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input

/-- The exact separating representations consist of the derived zero
normalization Riesz representation and Gate 818's two physical ones. -/
def programPT04T03NullJointRieszRepresentationsAt
    (input : Input) :
    SeparatingPDEResidualRepresentation
        (programPT04T03NullNormalizationEulerRestrictionAt period hPeriod
          plusBase minusBase hChart couplings data model einsteinScale
            interactionScale coefficients input).toLinearMap ×
      (SeparatingPDEResidualRepresentation
          (programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
            minusBase hChart couplings data model einsteinScale interactionScale
              coefficients input).toLinearMap ×
        SeparatingPDEResidualRepresentation
          (programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
            minusBase hChart couplings data model einsteinScale interactionScale
              coefficients input).toLinearMap) :=
  (programPT04T03NullJointNormalizationRieszRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input,
    programPT04T03NullPositionRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input,
    programPT04T03NullIntrinsicRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input)

/-- The position component of the combined zero jet is exactly Gate 818's
facewise Riesz residual. -/
@[simp] theorem programPT04T03NullJointRieszZeroJetAt_position
    (input : Input) (face : NullFace) :
    (finiteOrderZeroJetValue4D
      (programPT04T03NullJointRieszZeroJetAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input)).2.1 face =
      programPT04T03NullPositionRieszResidualAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input face :=
  rfl

/-- The intrinsic-screen component is exactly Gate 818's three-coefficient
Riesz residual. -/
@[simp] theorem programPT04T03NullJointRieszZeroJetAt_intrinsic
    (input : Input) (face : NullFace) (coefficient : Fin 3) :
    (finiteOrderZeroJetValue4D
      (programPT04T03NullJointRieszZeroJetAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input)).2.2 (face, coefficient) =
      programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input (face, coefficient) :=
  rfl

end

end
end P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D
end JanusFormal
