import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D

/-!
# Faithful geometric second jets at the T03 physical null component

For a faithful mobile null realization, this gate extracts genuine Frechet
second jets of the embedding and of every ambient- and screen-metric
coefficient.  Each jet is joint in the finite physical null state and its
displayed geometric source, and is centred at the physical null component
selected by the exact T03 core.  The value slots therefore refine Gate 825's
order-zero extractor, while the first and second slots are the actual `fderiv`
and iterated `fderiv` supplied by the geometric regularity contract.

On the admissible T03 domain, the faithful physical Euler covector is also
identified with the derivative of the concrete geometric face-plus-joint
action.  The two Gate 818 Riesz pairings are consequently identified with
that derivative in the position and intrinsic-screen directions.

No theorem below factors either Riesz residual through these local geometric
second jets.  In particular, no differentiation-under-the-null-face-integral
or local Euler density formula is claimed, so this gate does not close T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D

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
/-- Joint domain of the physical null state and the embedding source. -/
abbrev ProgramPT04T03FaithfulNullEmbeddingJetDomain
    (NullFace : Type uNull) [Fintype NullFace] :=
  FiniteNullFacePhysicalHilbert NullFace ×
    (Real × FiniteNullFaceScreenCoordinate2)

/-- Joint domain of the physical null state and an ambient chart point. -/
abbrev ProgramPT04T03FaithfulNullAmbientMetricJetDomain
    (NullFace : Type uNull) [Fintype NullFace] :=
  FiniteNullFacePhysicalHilbert NullFace × FiniteNullFaceAmbientCoordinate4

/-- Joint domain of the physical null state and the generator parameter. -/
abbrev ProgramPT04T03FaithfulNullScreenMetricJetDomain
    (NullFace : Type uNull) [Fintype NullFace] :=
  FiniteNullFacePhysicalHilbert NullFace × Real

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

private theorem programPT04T03FaithfulNullState_mem_geometryDomain
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    input.2 ∈ faithful.realization.geometry.domain := by
  simpa only [toActionModel_domain,
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization_domain]
    using hInput.2

/-- Genuine joint second jet of the faithful null embedding, centred at the
physical null component of an admissible T03 input. -/
def programPT04T03FaithfulNullEmbeddingSecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (source : Real × FiniteNullFaceScreenCoordinate2) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullEmbeddingJetDomain NullFace)
      FiniteNullFaceAmbientCoordinate4 := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullEmbeddingJetDomain NullFace =>
      faithful.realization.geometry.embedding state.1 face state.2)
    (input.2, source)
    (((faithful.realization.geometry.embedding_contDiffOn_three face).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩)).of_le (by norm_num))

/-- Genuine joint second jet of one faithful ambient-metric coefficient. -/
def programPT04T03FaithfulNullAmbientMetricSecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 4)
    (point : FiniteNullFaceAmbientCoordinate4) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullAmbientMetricJetDomain NullFace)
      Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullAmbientMetricJetDomain NullFace =>
      faithful.realization.geometry.ambientMetric state.1 face state.2
        row column)
    (input.2, point)
    ((faithful.realization.geometry.ambientMetric_contDiffOn_two
      face row column).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

/-- Genuine joint second jet of one faithful screen-metric coefficient. -/
def programPT04T03FaithfulNullScreenMetricSecondJetAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 2) (parameter : Real) :
    FramedSecondOrderJet
      (ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace) Real := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  exact chartwiseSecondOrderJetAt
    (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
      faithful.realization.geometry.screenMetric state.1 face state.2
        row column)
    (input.2, parameter)
    ((faithful.realization.geometry.screenMetric_contDiffOn_two
      face row column).contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hNull, Set.mem_univ _⟩))

@[simp] theorem programPT04T03FaithfulNullEmbeddingSecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (source : Real × FiniteNullFaceScreenCoordinate2) :
    (programPT04T03FaithfulNullEmbeddingSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face source).value =
      faithful.realization.geometry.embedding
        (finiteOrderZeroJetValue4D
          (programPT04T03NullPhysicalZeroJetExtractor period hPeriod plusBase
            minusBase hChart couplings input)) face source :=
  rfl

@[simp] theorem programPT04T03FaithfulNullEmbeddingSecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (source : Real × FiniteNullFaceScreenCoordinate2) :
    (programPT04T03FaithfulNullEmbeddingSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face source).firstDerivative =
      fderiv Real
        (fun state : ProgramPT04T03FaithfulNullEmbeddingJetDomain NullFace =>
          faithful.realization.geometry.embedding state.1 face state.2)
        (input.2, source) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullEmbeddingSecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (source : Real × FiniteNullFaceScreenCoordinate2) :
    (programPT04T03FaithfulNullEmbeddingSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face source).secondDerivative =
      fderiv Real
        (fderiv Real
          (fun state : ProgramPT04T03FaithfulNullEmbeddingJetDomain NullFace =>
            faithful.realization.geometry.embedding state.1 face state.2))
        (input.2, source) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullAmbientMetricSecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 4)
    (point : FiniteNullFaceAmbientCoordinate4) :
    (programPT04T03FaithfulNullAmbientMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        point).value =
      faithful.realization.geometry.ambientMetric
        (finiteOrderZeroJetValue4D
          (programPT04T03NullPhysicalZeroJetExtractor period hPeriod plusBase
            minusBase hChart couplings input)) face point row column :=
  rfl

@[simp]
theorem programPT04T03FaithfulNullAmbientMetricSecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 4)
    (point : FiniteNullFaceAmbientCoordinate4) :
    (programPT04T03FaithfulNullAmbientMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        point).firstDerivative =
      fderiv Real
        (fun state : ProgramPT04T03FaithfulNullAmbientMetricJetDomain NullFace =>
          faithful.realization.geometry.ambientMetric state.1 face state.2
            row column)
        (input.2, point) :=
  rfl

@[simp]
theorem programPT04T03FaithfulNullAmbientMetricSecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 4)
    (point : FiniteNullFaceAmbientCoordinate4) :
    (programPT04T03FaithfulNullAmbientMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        point).secondDerivative =
      fderiv Real
        (fderiv Real
          (fun state : ProgramPT04T03FaithfulNullAmbientMetricJetDomain NullFace =>
            faithful.realization.geometry.ambientMetric state.1 face state.2
              row column))
        (input.2, point) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullScreenMetricSecondJetAt_value
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 2) (parameter : Real) :
    (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        parameter).value =
      faithful.realization.geometry.screenMetric
        (finiteOrderZeroJetValue4D
          (programPT04T03NullPhysicalZeroJetExtractor period hPeriod plusBase
            minusBase hChart couplings input)) face parameter row column :=
  rfl

@[simp] theorem programPT04T03FaithfulNullScreenMetricSecondJetAt_firstDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 2) (parameter : Real) :
    (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        parameter).firstDerivative =
      fderiv Real
        (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
          faithful.realization.geometry.screenMetric state.1 face state.2
            row column)
        (input.2, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullScreenMetricSecondJetAt_secondDerivative
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace) (row column : Fin 2) (parameter : Real) :
    (programPT04T03FaithfulNullScreenMetricSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face row column
        parameter).secondDerivative =
      fderiv Real
        (fderiv Real
          (fun state : ProgramPT04T03FaithfulNullScreenMetricJetDomain NullFace =>
            faithful.realization.geometry.screenMetric state.1 face state.2
              row column))
        (input.2, parameter) :=
  rfl

/-- T03 specialization of faithful Euler agreement with the concrete geometric
action derivative. -/
theorem programPT04T03FaithfulNullPhysicalEuler_eq_geometric_fderiv
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    finiteNullFacePhysicalEuler Model input.2 =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 := by
  exact
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
      faithful input.2
        (programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod
          plusBase minusBase hChart couplings faithful input hInput)

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

/-- The exact T03 position Riesz pairing is the directional derivative of the
faithful geometric null action. -/
theorem programPT04T03FaithfulNullPositionRieszPairing_eq_geometric_fderiv
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (direction : NullPosition) :
    inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 (direction, 0) := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  calc
    inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data Model einsteinScale interactionScale
          coefficients input direction :=
      (programPT04T03NullPositionEulerRestriction_eq_rieszPairing period hPeriod
        plusBase minusBase hChart couplings data Model einsteinScale
          interactionScale coefficients input direction).symm
    _ = finiteNullFacePhysicalPositionEuler Model input.2 direction := by
      rw [programPT04T03NullPositionEulerRestrictionAt_eq]
    _ = finiteNullFacePhysicalEuler Model input.2 (direction, 0) := rfl
    _ = fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 (direction, 0) := by
      rw [FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
        faithful input.2 hNull]

/-- The exact T03 intrinsic-screen Riesz pairing is the corresponding
directional derivative of the faithful geometric null action. -/
theorem programPT04T03FaithfulNullIntrinsicRieszPairing_eq_geometric_fderiv
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (direction : NullIntrinsic) :
    inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 (0, direction) := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  calc
    inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data Model einsteinScale interactionScale
          coefficients input direction :=
      (programPT04T03NullIntrinsicEulerRestriction_eq_rieszPairing period hPeriod
        plusBase minusBase hChart couplings data Model einsteinScale
          interactionScale coefficients input direction).symm
    _ = finiteNullFacePhysicalIntrinsicEuler Model input.2 direction := by
      rw [programPT04T03NullIntrinsicEulerRestrictionAt_eq]
    _ = finiteNullFacePhysicalEuler Model input.2 (0, direction) := rfl
    _ = fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input.2 (0, direction) := by
      rw [FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
        faithful input.2 hNull]

end

end
end P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D
end JanusFormal
