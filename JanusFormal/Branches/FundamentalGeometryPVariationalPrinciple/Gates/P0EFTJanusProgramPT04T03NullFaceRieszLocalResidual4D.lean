import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

/-!
# Finite null-face local residuals for T04

The two physical null blocks of the exact T03 core are finite Euclidean fields:
one scalar per null face and three intrinsic-screen coefficients per null face.
This file represents their actual Euler restrictions by primal Riesz residuals,
proves pointwise separation, and records the corresponding exact Hessian-block
Helmholtz identities.  No dual covector is reused as a residual.

The construction supplies no missing embedding/screen jet formula for the
abstract null action model and does not close terminal T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
open P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uIndex

/-- Primal finite-face residual represented by the Euclidean Riesz vector. -/
def finiteEuclideanRieszResidual
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real) :
    EuclideanSpace Real Index :=
  (InnerProductSpace.toDual Real (EuclideanSpace Real Index)).symm covector

/-- The primal residual pairs exactly to the supplied covector. -/
theorem finiteEuclideanRieszResidual_pairing
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real)
    (test : EuclideanSpace Real Index) :
    covector test = inner Real (finiteEuclideanRieszResidual covector) test := by
  symm
  exact InnerProductSpace.toDual_symm_apply

/-- All finite-face tests separate a primal Euclidean residual. -/
theorem finiteEuclideanRieszResidual_pairing_separates
    {Index : Type uIndex} [Fintype Index]
    (residual : EuclideanSpace Real Index) :
    (∀ test, inner Real residual test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    exact inner_self_eq_zero.mp (hPairing residual)
  · intro hResidual test
    rw [hResidual]
    exact inner_zero_left test

/-- A genuine primal residual representation, rather than the algebraic dual
used as its own residual. -/
def finiteEuclideanRieszResidualRepresentation
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real) :
    SeparatingPDEResidualRepresentation covector.toLinearMap where
  Residual := EuclideanSpace Real Index
  zeroResidual := 0
  residual := finiteEuclideanRieszResidual covector
  pairing := fun residual test => inner Real residual test
  represents := finiteEuclideanRieszResidual_pairing covector
  separates := finiteEuclideanRieszResidual_pairing_separates
    (finiteEuclideanRieszResidual covector)

theorem finiteEuclideanCovector_eq_zero_iff_rieszResidual
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real) :
    covector = 0 ↔ finiteEuclideanRieszResidual covector = 0 := by
  constructor
  · intro hCovector
    rw [hCovector]
    simp [finiteEuclideanRieszResidual]
  · intro hResidual
    apply (InnerProductSpace.toDual Real
      (EuclideanSpace Real Index)).symm.injective
    simpa [finiteEuclideanRieszResidual] using hResidual

theorem finiteEuclideanRieszResidual_eq_zero_iff_pointwise
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real) :
    finiteEuclideanRieszResidual covector = 0 ↔
      ∀ index, finiteEuclideanRieszResidual covector index = 0 := by
  constructor
  · intro hResidual index
    rw [hResidual]
    rfl
  · intro hPointwise
    apply PiLp.ext
    intro index
    simpa using hPointwise index

theorem finiteEuclideanCovector_eq_zero_iff_rieszResidual_pointwise
    {Index : Type uIndex} [Fintype Index]
    (covector : EuclideanSpace Real Index →L[Real] Real) :
    covector = 0 ↔ ∀ index, finiteEuclideanRieszResidual covector index = 0 :=
  (finiteEuclideanCovector_eq_zero_iff_rieszResidual covector).trans
    (finiteEuclideanRieszResidual_eq_zero_iff_pointwise covector)

/-- Position residual: one actual Euler coefficient per supplied null face. -/
def finiteNullFacePhysicalPositionRieszResidual
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePositionHilbert NullFace :=
  finiteEuclideanRieszResidual
    (finiteNullFacePhysicalPositionEuler model input)

/-- Intrinsic residual: three actual Euler coefficients per supplied null face. -/
def finiteNullFacePhysicalIntrinsicRieszResidual
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFaceIntrinsicMetricHilbert NullFace :=
  finiteEuclideanRieszResidual
    (finiteNullFacePhysicalIntrinsicEuler model input)

theorem finiteNullFacePhysicalPositionEuler_eq_zero_iff_pointwise
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFacePhysicalPositionEuler model input = 0 ↔
      ∀ face, finiteNullFacePhysicalPositionRieszResidual model input face = 0 :=
  finiteEuclideanCovector_eq_zero_iff_rieszResidual_pointwise _

theorem finiteNullFacePhysicalIntrinsicEuler_eq_zero_iff_pointwise
    {NullFace : Type uIndex} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFacePhysicalIntrinsicEuler model input = 0 ↔
      ∀ face coefficient,
        finiteNullFacePhysicalIntrinsicRieszResidual model input
          (face, coefficient) = 0 := by
  have hCore := finiteEuclideanCovector_eq_zero_iff_rieszResidual_pointwise
    (finiteNullFacePhysicalIntrinsicEuler model input)
  constructor
  · intro hZero face coefficient
    exact hCore.mp hZero (face, coefficient)
  · intro hZero
    apply hCore.mpr
    rintro ⟨face, coefficient⟩
    exact hZero face coefficient


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

/-- Primal position residual of the exact T03 Euler restriction. -/
def programPT04T03NullPositionRieszResidualAt (input : Input) : NullPosition :=
  finiteEuclideanRieszResidual
    (programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input)

/-- Primal intrinsic-screen residual of the exact T03 Euler restriction. -/
def programPT04T03NullIntrinsicRieszResidualAt (input : Input) : NullIntrinsic :=
  finiteEuclideanRieszResidual
    (programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input)

/-- The exact T03 position residual is the physical null-model Riesz residual. -/
theorem programPT04T03NullPositionRieszResidualAt_eq_physical
    (input : Input) :
    programPT04T03NullPositionRieszResidualAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input =
      finiteNullFacePhysicalPositionRieszResidual model input.2 := by
  unfold programPT04T03NullPositionRieszResidualAt
    finiteNullFacePhysicalPositionRieszResidual
  rw [programPT04T03NullPositionEulerRestrictionAt_eq]

/-- The exact T03 intrinsic residual is the physical null-model Riesz residual. -/
theorem programPT04T03NullIntrinsicRieszResidualAt_eq_physical
    (input : Input) :
    programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input =
      finiteNullFacePhysicalIntrinsicRieszResidual model input.2 := by
  unfold programPT04T03NullIntrinsicRieszResidualAt
    finiteNullFacePhysicalIntrinsicRieszResidual
  rw [programPT04T03NullIntrinsicEulerRestrictionAt_eq]

/-- Exact weak/strong pairing for the null-position block. -/
theorem programPT04T03NullPositionEulerRestriction_eq_rieszPairing
    (input : Input) (direction : NullPosition) :
    programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input direction =
      inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input) direction :=
  finiteEuclideanRieszResidual_pairing _ _

/-- Exact weak/strong pairing for the intrinsic null-screen block. -/
theorem programPT04T03NullIntrinsicEulerRestriction_eq_rieszPairing
    (input : Input) (direction : NullIntrinsic) :
    programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input direction =
      inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input) direction :=
  finiteEuclideanRieszResidual_pairing _ _

/-- Position stationarity is exactly the pointwise equation on every null face. -/
theorem programPT04T03NullPositionEulerRestriction_eq_zero_iff_pointwise
    (input : Input) :
    programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ∀ face,
        programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input face = 0 :=
  finiteEuclideanCovector_eq_zero_iff_rieszResidual_pointwise _

/-- Intrinsic stationarity is exactly the three pointwise equations on every
null face. -/
theorem programPT04T03NullIntrinsicEulerRestriction_eq_zero_iff_pointwise
    (input : Input) :
    programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input = 0 ↔
      ∀ face coefficient,
        programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data model einsteinScale interactionScale
            coefficients input (face, coefficient) = 0 := by
  have hCore := finiteEuclideanCovector_eq_zero_iff_rieszResidual_pointwise
    (programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients input)
  constructor
  · intro hZero face coefficient
    exact hCore.mp hZero (face, coefficient)
  · intro hZero
    apply hCore.mpr
    rintro ⟨face, coefficient⟩
    exact hZero face coefficient

/-- Separating primal representation of the exact position restriction. -/
def programPT04T03NullPositionRieszResidualRepresentationAt (input : Input) :
    SeparatingPDEResidualRepresentation
      (programPT04T03NullPositionEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap :=
  finiteEuclideanRieszResidualRepresentation _

/-- Separating primal representation of the exact intrinsic restriction. -/
def programPT04T03NullIntrinsicRieszResidualRepresentationAt (input : Input) :
    SeparatingPDEResidualRepresentation
      (programPT04T03NullIntrinsicEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap :=
  finiteEuclideanRieszResidualRepresentation _

/-- The previously open exact T03 null-position residual family is inhabited by
its primal, per-face Riesz residual. -/
def programPT04T03NullPositionRieszLocalPDEWitness :
    ProgramPT04T03NullPositionLocalPDEWitness period hPeriod plusBase minusBase
      hChart couplings data model einsteinScale interactionScale coefficients :=
  fun input =>
    programPT04T03NullPositionRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input

/-- The previously open exact T03 intrinsic residual family is inhabited by its
primal three-coefficient residual on every null face. -/
def programPT04T03NullIntrinsicRieszLocalPDEWitness :
    ProgramPT04T03NullIntrinsicLocalPDEWitness period hPeriod plusBase minusBase
      hChart couplings data model einsteinScale interactionScale coefficients :=
  fun input =>
    programPT04T03NullIntrinsicRieszResidualRepresentationAt period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input

/-- Updated honest frontier: both finite physical null blocks are available;
the coupled metric/boundary jet-PDE block remains open. -/
def programPT04T03NullFaceRieszLocalJetPDEFrontier :
    ProgramPT04T03LocalJetPDEFrontier period hPeriod plusBase minusBase hChart
      couplings data model einsteinScale interactionScale coefficients where
  metricBoundaryLocalPDE := .openFrontier .metricBoundaryGraph
  nullPositionLocalPDE := .available
    (programPT04T03NullPositionRieszLocalPDEWitness period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients)
  nullIntrinsicLocalPDE := .available
    (programPT04T03NullIntrinsicRieszLocalPDEWitness period hPeriod plusBase
      minusBase hChart couplings data model einsteinScale interactionScale
        coefficients)

/-- Exact nonlinear Helmholtz identity for two null-position directions. -/
theorem programPT04T03NullPositionHelmholtzAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model)
    (first second : NullPosition) :
    fderiv Real FullEuler input
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings first)
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings second) =
      fderiv Real FullEuler input
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings second)
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings first) := by
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysical_helmholtzJacobianOn
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse input hInput _ _

/-- Exact nonlinear Helmholtz identity for two intrinsic null-screen directions. -/
theorem programPT04T03NullIntrinsicHelmholtzAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model)
    (first second : NullIntrinsic) :
    fderiv Real FullEuler input
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings first)
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings second) =
      fderiv Real FullEuler input
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings second)
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings first) := by
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysical_helmholtzJacobianOn
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse input hInput _ _

/-- Exact mixed Helmholtz reciprocity between the null-position and intrinsic
screen blocks. -/
theorem programPT04T03NullPositionIntrinsicHelmholtzAt
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model)
    (position : NullPosition) (intrinsic : NullIntrinsic) :
    fderiv Real FullEuler input
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings position)
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings intrinsic) =
      fderiv Real FullEuler input
        (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
          hChart couplings intrinsic)
        (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
          hChart couplings position) := by
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysical_helmholtzJacobianOn
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse input hInput _ _

end

end
end P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D
end JanusFormal
