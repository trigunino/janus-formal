import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D

/-!
# Faithful null-density second-jet factorization at the T03 component

This gate adds the joint physical-state/generator-parameter second jets of the
expansion and inaffinity supplied by the mobile geometric datum.  It also
isolates the genuinely missing `C²` contract for the normalization fields and
endpoint joint angles, then extracts their actual chartwise second jets.

The original and reparametrized face densities, the local normalization
transgression, and both endpoint joint values are written exactly through the
value slots of these jets and Gate 837's screen-metric coefficient jets.  The
total finite face-plus-joints action has an unconditional second jet from the
existing realization contract; its first slot is the exact T03 Euler covector
and hence the two existing Riesz pairings in their respective directions.

No differentiation under the parameter integral is asserted.  The current
realization supplies interval integrability and `C²` regularity only after the
full finite sum has been assembled; it supplies neither a state-uniform
dominating derivative nor facewise action regularity.  Thus the total-action
jet is not factored through an integral of the local density jets here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D
open P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D
open P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D
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

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNullExpansionCountertermNonDifferentiable
open P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

/-- The regularity absent from the mobile datum for the normalization fields
and endpoint angles.  These hypotheses concern the geometric scalar fields,
not the density or residual conclusions below. -/
structure ProgramPT04T03FaithfulNullMissingScalarC2
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace) :
    Prop where
  sigma_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
        faithful.realization.geometry.sigma state.1 face state.2)
      (faithful.realization.geometry.domain ×ˢ Set.univ)
  sigmaDerivative_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
        faithful.realization.geometry.sigmaDerivative state.1 face state.2)
      (faithful.realization.geometry.domain ×ˢ Set.univ)
  initialJointAngle_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : NullPhysical =>
        faithful.realization.geometry.initialJointAngle state face)
      faithful.realization.geometry.domain
  finalJointAngle_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : NullPhysical =>
        faithful.realization.geometry.finalJointAngle state face)
      faithful.realization.geometry.domain

private theorem programPT04T03FaithfulNullState_mem_geometryDomain
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    input.2 ∈ faithful.realization.geometry.domain := by
  simpa only [toActionModel_domain,
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization_domain]
    using hInput.2

/-- Genuine joint second jet of the null expansion. -/
def programPT04T03FaithfulNullExpansionSecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace) Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
      faithful.realization.geometry.expansion state.1 face state.2)
    (input.2, parameter)
    ((faithful.realization.geometry.expansion_contDiffOn_two face).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

/-- Genuine joint second jet of the null inaffinity. -/
def programPT04T03FaithfulNullInaffinitySecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace) Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
      faithful.realization.geometry.inaffinity state.1 face state.2)
    (input.2, parameter)
    ((faithful.realization.geometry.inaffinity_contDiffOn_two face).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

/-- Genuine joint second jet of the normalization exponent, conditional on
the explicit missing regularity contract. -/
def programPT04T03FaithfulNullSigmaSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace) Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
      faithful.realization.geometry.sigma state.1 face state.2)
    (input.2, parameter)
    ((regularity.sigma_contDiffOn_two face).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

/-- Genuine joint second jet of the supplied normalization derivative. -/
def programPT04T03FaithfulNullSigmaDerivativeSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace) Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
      faithful.realization.geometry.sigmaDerivative state.1 face state.2)
    (input.2, parameter)
    ((regularity.sigmaDerivative_contDiffOn_two face).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

/-- Genuine physical-state second jet of the initial endpoint angle. -/
def programPT04T03FaithfulNullInitialJointAngleSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) : FramedSecondOrderJet NullPhysical Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : NullPhysical =>
      faithful.realization.geometry.initialJointAngle state face)
    input.2
    ((regularity.initialJointAngle_contDiffOn_two face).contDiffAt
      (faithful.realization.geometry.domain_isOpen.mem_nhds hNull))

/-- Genuine physical-state second jet of the final endpoint angle. -/
def programPT04T03FaithfulNullFinalJointAngleSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) : FramedSecondOrderJet NullPhysical Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : NullPhysical =>
      faithful.realization.geometry.finalJointAngle state face)
    input.2
    ((regularity.finalJointAngle_contDiffOn_two face).contDiffAt
      (faithful.realization.geometry.domain_isOpen.mem_nhds hNull))

/-- Genuine second jet of the complete finite face-plus-joints action.  This
uses exactly the `C²` law already carried by the realization. -/
def programPT04T03FaithfulNullTotalActionSecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    FramedSecondOrderJet NullPhysical Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (finiteNullFaceMobileGeometricTotalAction faithful.realization.geometry)
    input.2
    (faithful.realization.totalAction_contDiffOn_two.contDiffAt
      (faithful.realization.geometry.domain_isOpen.mem_nhds hNull))

@[simp] theorem programPT04T03FaithfulNullExpansionSecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face parameter).value =
      faithful.realization.geometry.expansion input.2 face parameter :=
  rfl

@[simp] theorem programPT04T03FaithfulNullExpansionSecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face
        parameter).firstDerivative =
      fderiv Real
        (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
          faithful.realization.geometry.expansion state.1 face state.2)
        (input.2, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullExpansionSecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face
        parameter).secondDerivative =
      fderiv Real
        (fderiv Real
          (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
            faithful.realization.geometry.expansion state.1 face state.2))
        (input.2, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullInaffinitySecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullInaffinitySecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face parameter).value =
      faithful.realization.geometry.inaffinity input.2 face parameter :=
  rfl

@[simp] theorem programPT04T03FaithfulNullInaffinitySecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullInaffinitySecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face
        parameter).firstDerivative =
      fderiv Real
        (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
          faithful.realization.geometry.inaffinity state.1 face state.2)
        (input.2, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullInaffinitySecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullInaffinitySecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face
        parameter).secondDerivative =
      fderiv Real
        (fderiv Real
          (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
            faithful.realization.geometry.inaffinity state.1 face state.2))
        (input.2, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullSigmaSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful regularity input hInput face
        parameter).value =
      faithful.realization.geometry.sigma input.2 face parameter :=
  rfl

@[simp] theorem programPT04T03FaithfulNullSigmaDerivativeSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullSigmaDerivativeSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful regularity input hInput face
        parameter).value =
      faithful.realization.geometry.sigmaDerivative input.2 face parameter :=
  rfl

@[simp] theorem programPT04T03FaithfulNullInitialJointAngleSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) :
    (programPT04T03FaithfulNullInitialJointAngleSecondJetAt period hPeriod
      plusBase minusBase hChart couplings faithful regularity input hInput
        face).value =
      faithful.realization.geometry.initialJointAngle input.2 face :=
  rfl

@[simp] theorem programPT04T03FaithfulNullFinalJointAngleSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) :
    (programPT04T03FaithfulNullFinalJointAngleSecondJetAt period hPeriod
      plusBase minusBase hChart couplings faithful regularity input hInput
        face).value =
      faithful.realization.geometry.finalJointAngle input.2 face :=
  rfl

@[simp] theorem programPT04T03FaithfulNullTotalActionSecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput).value =
      finiteNullFaceMobileGeometricTotalAction
        faithful.realization.geometry input.2 :=
  rfl

@[simp] theorem programPT04T03FaithfulNullTotalActionSecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput).firstDerivative =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 :=
  rfl

@[simp] theorem programPT04T03FaithfulNullTotalActionSecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput).secondDerivative =
      fderiv Real
        (fderiv Real
          (finiteNullFaceMobileGeometricTotalAction
            faithful.realization.geometry)) input.2 :=
  rfl

/-- The original face density factors exactly through the value slots of the
screen-metric, inaffinity and expansion second jets. -/
theorem programPT04T03FaithfulNullFaceDensity_eq_secondJetValues
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    nullFaceDensity
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face)
        parameter =
      nullFaceCoefficient
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face) *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column parameter).value)| *
        (programPT04T03FaithfulNullInaffinitySecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful input hInput face
            parameter).value +
      nullFaceCoefficient
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face) *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column parameter).value)| *
        zeroExtendedExpansionCountertermFactor
          (faithful.realization.geometry.renormalizationLengthScale face)
          (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face
              parameter).value :=
  rfl

/-- The finite normalization transgression is already a local expression in
the screen, expansion, sigma and sigma-derivative jet values. -/
theorem programPT04T03FaithfulNullLocalFaceShift_eq_secondJetValues
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    localFaceShift
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face).generator
        parameter =
      Real.sqrt |Matrix.det (fun row column : Fin 2 =>
        (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful input hInput face row
            column parameter).value)| *
        (programPT04T03FaithfulNullSigmaDerivativeSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful regularity input hInput
            face parameter).value +
      Real.sqrt |Matrix.det (fun row column : Fin 2 =>
        (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful input hInput face row
            column parameter).value)| *
        (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful input hInput face
            parameter).value *
        (programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod plusBase
          minusBase hChart couplings faithful regularity input hInput face
            parameter).value := by
  rw [localFaceShift_eq_productDerivative]
  rfl

/-- The reparametrized face density factors through the same screen and
physical scalar second jets, including both normalization fields. -/
theorem programPT04T03FaithfulReparametrizedNullFaceDensity_eq_secondJetValues
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (parameter : Real) :
    reparametrizedNullFaceDensity
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face)
        parameter =
      nullFaceCoefficient
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face) *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column parameter).value)| *
        Real.exp (-(programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful regularity input hInput
            face parameter).value) *
        (Real.exp
            (programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod plusBase
              minusBase hChart couplings faithful regularity input hInput face
                parameter).value *
          ((programPT04T03FaithfulNullInaffinitySecondJetAt period hPeriod
              plusBase minusBase hChart couplings faithful input hInput face
                parameter).value +
            (programPT04T03FaithfulNullSigmaDerivativeSecondJetAt period hPeriod
              plusBase minusBase hChart couplings faithful regularity input
                hInput face parameter).value)) +
      nullFaceCoefficient
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face) *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column parameter).value)| *
        Real.exp (-(programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful regularity input hInput
            face parameter).value) *
        zeroExtendedExpansionCountertermFactor
          (faithful.realization.geometry.renormalizationLengthScale face)
          (Real.exp
              (programPT04T03FaithfulNullSigmaSecondJetAt period hPeriod
                plusBase minusBase hChart couplings faithful regularity input
                  hInput face parameter).value *
            (programPT04T03FaithfulNullExpansionSecondJetAt period hPeriod
              plusBase minusBase hChart couplings faithful input hInput face
                parameter).value) :=
  rfl

/-- Initial endpoint density through the endpoint screen and angle jet values. -/
theorem programPT04T03FaithfulInitialJointAction_eq_secondJetValues
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) :
    (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face).initialJointAction =
      faithful.realization.geometry.einsteinScale face *
        faithful.realization.geometry.initialJointOrientationSign face *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column
              (faithful.realization.geometry.interval face).initialParameter).value)| *
        (programPT04T03FaithfulNullInitialJointAngleSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful regularity input hInput
            face).value :=
  rfl

/-- Final endpoint density through the endpoint screen and angle jet values. -/
theorem programPT04T03FaithfulFinalJointAction_eq_secondJetValues
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) :
    (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2 face).finalJointAction =
      faithful.realization.geometry.einsteinScale face *
        faithful.realization.geometry.finalJointOrientationSign face *
        Real.sqrt |Matrix.det (fun row column : Fin 2 =>
          (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod
            plusBase minusBase hChart couplings faithful input hInput face row
              column
              (faithful.realization.geometry.interval face).finalParameter).value)| *
        (programPT04T03FaithfulNullFinalJointAngleSecondJetAt period hPeriod
          plusBase minusBase hChart couplings faithful regularity input hInput
            face).value :=
  rfl

/-- The faithful physical Euler covector is the first slot of the genuine
total-action second jet. -/
theorem programPT04T03FaithfulNullPhysicalEuler_eq_totalActionJetFirstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    finiteNullFacePhysicalEuler Model input.2 =
      (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
        minusBase hChart couplings faithful input hInput).firstDerivative := by
  exact programPT04T03FaithfulNullPhysicalEuler_eq_geometric_fderiv period
    hPeriod plusBase minusBase hChart couplings faithful input hInput

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

/-- The position Riesz pairing is evaluation of the first slot of the genuine
total-action second jet. -/
theorem programPT04T03FaithfulNullPositionRieszPairing_eq_totalActionJet
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (direction : NullPosition) :
    inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
        minusBase hChart couplings faithful input hInput).firstDerivative
          (direction, 0) := by
  exact programPT04T03FaithfulNullPositionRieszPairing_eq_geometric_fderiv
    period hPeriod plusBase minusBase hChart couplings faithful data
      einsteinScale interactionScale coefficients input hInput direction

/-- The intrinsic-screen Riesz pairing is evaluation of the same first slot. -/
theorem programPT04T03FaithfulNullIntrinsicRieszPairing_eq_totalActionJet
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (direction : NullIntrinsic) :
    inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
        minusBase hChart couplings faithful input hInput).firstDerivative
          (0, direction) := by
  exact programPT04T03FaithfulNullIntrinsicRieszPairing_eq_geometric_fderiv
    period hPeriod plusBase minusBase hChart couplings faithful data
      einsteinScale interactionScale coefficients input hInput direction

end

end
end P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D
end JanusFormal
