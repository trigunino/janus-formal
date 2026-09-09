import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleStrongResidualSystem4D

/-!
# Terminal T03 full Euler--Lagrange certificate

The certificate uses the finite `C²` full-BRST core already present in the
physical action.  It couples the bulk metric to GHY data, replaces the raw LL
packet by its compatible completion, and uses a faithful mobile null-face
realization.  The resulting open carrier has a covered translation atlas and
one chart-independent Frechet derivative whose zero locus is the four-block
Euler system.  On genuine smooth LL packets, its LL block is the proved
pointwise strong system.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D

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
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleStrongResidualSystem4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
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

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod Geometry
    Frame couplings

local notation "MatterInput" =>
  ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
    couplings.matterMassSquared

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "CompatibleLL" =>
  CompatibleLLCompletion period hPeriod

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod Geometry
    Frame couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod plusBase

local notation "GHYInput" => Prod GHYCore Real

local notation "AmbientInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    Geometry Frame couplings plusBase

local notation "AmbientCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphCore
    period hPeriod plusBase minusBase hChart couplings

local notation "MetricBoundaryAmbient" => OldInput × GHYInput

local notation "MetricBoundary" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore period
    hPeriod plusBase minusBase hChart couplings

local notation "CompletedCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore
    period hPeriod plusBase minusBase hChart couplings

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance terminalGHYCoreNormedAddCommGroup : NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance terminalGHYCoreNormedSpace : NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace
local instance terminalMetricBoundaryAmbientSMul :
    SMul Real MetricBoundaryAmbient := Prod.instSMul
local instance : ContinuousSMul Real MetricBoundaryAmbient := by
  apply Prod.continuousSMul
local instance : NormedSpace Real MetricBoundaryAmbient := Prod.normedSpace
local instance terminalAmbientSMul : SMul Real AmbientInput := Prod.instSMul
local instance : ContinuousSMul Real LLInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real BulkInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real GHYInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real AmbientInput := by apply Prod.continuousSMul
local instance : NormedSpace Real AmbientInput := Prod.normedSpace

local instance ambientCoupledNormedAddCommGroup :
    NormedAddCommGroup AmbientCoupled :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance ambientCoupledNormedSpace : NormedSpace Real AmbientCoupled :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance terminalMetricBoundarySMul : SMul Real MetricBoundary :=
  SetLike.smul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance metricBoundaryNormedAddCommGroup :
    NormedAddCommGroup MetricBoundary :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance metricBoundaryNormedSpace : NormedSpace Real MetricBoundary :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance terminalMetricBoundaryContinuousSMul :
    ContinuousSMul Real MetricBoundary :=
  SMulMemClass.continuousSMul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance terminalCompletedCoupledSMul : SMul Real CompletedCoupled :=
  Prod.instSMul

local instance : NormedSpace Real CompletedCoupled := Prod.normedSpace

/-! ## LL block of the coupled action -/

include hChart

/-- The LL covector obtained by restricting the coupled action is exactly the
derivative of the action on the compatible LL completion. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler_eq_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : CompletedCoupled)
    (hInput :
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
          period hPeriod plusBase minusBase hChart couplings input ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
          period hPeriod plusBase minusBase hChart couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input =
      fderiv Real (compatibleCompletedLLAction period hPeriod) input.2 := by
  apply ContinuousLinearMap.ext
  intro direction
  let current : AmbientInput :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings input)
  let delta : AmbientInput :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings (0, direction))
  have hCurrent : current =
      ((input.1.1.1,
          compatibleLLCompletionToAmbient period hPeriod input.2),
        input.1.1.2) := by
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
          period hPeriod plusBase minusBase hChart couplings input = _
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply
        period hPeriod plusBase minusBase hChart couplings input
  have hDelta : delta =
      ((0, compatibleLLCompletionToAmbient period hPeriod direction), 0) := by
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
          period hPeriod plusBase minusBase hChart couplings (0, direction) = _
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply
        period hPeriod plusBase minusBase hChart couplings (0, direction)
  change
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        Geometry Frame
          (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
            period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        couplings plusBase data einsteinScale interactionScale coefficients
          current delta =
      fderiv Real (compatibleCompletedLLAction period hPeriod) input.2 direction
  have hMobile := DFunLike.congr_fun
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_bulk_add_ghy
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        couplings plusBase data einsteinScale interactionScale coefficients
          hTransverse current (show current ∈
            finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
              hPeriod Geometry Frame
                (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
                  period hPeriod plusBase
                    (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
              couplings plusBase from hInput)) delta
  have hBulk := DFunLike.congr_fun
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        couplings interactionScale coefficients current.1
          (show current.1 ∈
            finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
              Geometry Frame
                (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
                  period hPeriod plusBase
                    (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
              couplings from hInput.1)) delta.1
  rw [hMobile]
  change
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod
          Geometry Frame
            (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
              period hPeriod plusBase
                (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
          couplings interactionScale coefficients current.1 delta.1 +
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
          period hPeriod plusBase einsteinScale current.2 delta.2 =
      fderiv Real (compatibleCompletedLLAction period hPeriod) input.2 direction
  rw [hBulk, compatibleCompletedLLAction_fderiv]
  rw [hCurrent, hDelta]
  simp [ContinuousLinearMap.comp_apply, add_apply]

/-- Hence, on every genuine smooth packet, the LL block of the coupled Euler
operator vanishes exactly when all three pointwise strong LL equations hold. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler_smooth_eq_zero_iff_strong
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (metricBoundary : MetricBoundary)
    (fields : IndependentFields period hPeriod)
    (hInput :
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
          period hPeriod plusBase minusBase hChart couplings
            (metricBoundary,
              smoothToCompatibleLLCompletion period hPeriod
                (fields.llAuxMetric, (fields.llMeasure, fields.llField))) ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
          period hPeriod plusBase minusBase hChart couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients
          (metricBoundary,
            smoothToCompatibleLLCompletion period hPeriod
              (fields.llAuxMetric, (fields.llMeasure, fields.llField))) = 0 ↔
      (forall point : EffectiveThroat period hPeriod,
        ptSymmetricLLAuxMetricStrongResidual period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields point = 0) ∧
      (forall point : EffectiveThroat period hPeriod,
        llMeasureStrongResidual period hPeriod fields point = 0) ∧
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)) fields := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler_eq_fderiv
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients hTransverse _ hInput]
  exact
    finite_frame_paired_c2_physical_maxwell_spinC_matter_LL_compatible_strong_residual_system_gate
      period hPeriod fields

/-! ## Terminal certificate -/

section

variable {NullFace : Type*} [Fintype NullFace]
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace

local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local notation "Carrier" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAdmissibleCarrier
    period hPeriod plusBase minusBase hChart couplings Model

local notation "Index" => Carrier

local instance : ContinuousSMul Real CompletedCoupled := by
  apply Prod.continuousSMul

local instance terminalPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance terminalInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

/-- Concrete terminal `T03` certificate on one coupled full-BRST field core. -/
structure ProgramPT03FullEulerLagrangeCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients) : Prop where
  fullBRST_core_identification :
    OldInput =
      (FiniteFramePairedC2FullBRSTGaugeCore period hPeriod Frame Frame Frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric ×
        MatterInput)
  domain_open :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
  domain_nonempty :
    (0 : Input) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model
  ll_smooth_dense :
    DenseRange (smoothToCompatibleLLCompletion period hPeriod)
  bulk_GHY_metric_compatible :
    forall input : CompletedCoupled,
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
          period hPeriod plusBase minusBase hChart couplings
            (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
              period hPeriod plusBase minusBase hChart couplings input).1 =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
          period hPeriod plusBase
            (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
              period hPeriod plusBase minusBase hChart couplings input).2
  null_actionDatum_injective :
    FiniteNullFaceMobileCanonicalActionFaithful faithful.realization.geometry
  action_fderiv_eq_euler :
    forall input : Input,
      input ∈
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
            period hPeriod plusBase minusBase hChart couplings Model →
        fderiv Real
            (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
              period hPeriod plusBase minusBase hChart couplings data Model
                einsteinScale interactionScale coefficients) input =
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
            period hPeriod plusBase minusBase hChart couplings data Model
              einsteinScale interactionScale coefficients input
  atlas_cover :
    forall state : Carrier,
      exists center : Index,
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
            period hPeriod plusBase minusBase hChart couplings Model center state.1 = 0 ∧
          (0 : Input) ∈
            finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
              period hPeriod plusBase minusBase hChart couplings Model center
  transition_hasFDerivAt :
    forall (first second : Index) (coordinate : Input),
      HasFDerivAt
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
          period hPeriod plusBase minusBase hChart couplings Model first second)
        (ContinuousLinearMap.id Real Input) coordinate
  transition_cocycle :
    forall first second third : Index,
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
          period hPeriod plusBase minusBase hChart couplings Model second third) ∘
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
          period hPeriod plusBase minusBase hChart couplings Model first second) =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
          period hPeriod plusBase minusBase hChart couplings Model first third
  chart_action_hasFDerivAt :
    forall (center : Index) (coordinate : Input),
      coordinate ∈
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
            period hPeriod plusBase minusBase hChart couplings Model center →
        HasFDerivAt
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
            period hPeriod plusBase minusBase hChart couplings Model data
              einsteinScale interactionScale coefficients center)
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
            period hPeriod plusBase minusBase hChart couplings Model data
              einsteinScale interactionScale coefficients center coordinate)
          coordinate
  chart_action_transition :
    forall (first second : Index) (coordinate : Input),
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
          period hPeriod plusBase minusBase hChart couplings Model data
            einsteinScale interactionScale coefficients second
            (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
              period hPeriod plusBase minusBase hChart couplings Model first second
                coordinate) =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
          period hPeriod plusBase minusBase hChart couplings Model data
            einsteinScale interactionScale coefficients first coordinate
  chart_euler_covariant :
    forall (first second : Index) (coordinate : Input),
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
          period hPeriod plusBase minusBase hChart couplings Model data
            einsteinScale interactionScale coefficients first coordinate =
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
          period hPeriod plusBase minusBase hChart couplings Model data
            einsteinScale interactionScale coefficients second
            (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
              period hPeriod plusBase minusBase hChart couplings Model first second
                coordinate)).comp (ContinuousLinearMap.id Real Input)
  criticality_iff_four_blocks :
    forall state : Carrier,
      FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical
          period hPeriod plusBase minusBase hChart couplings Model data
            einsteinScale interactionScale coefficients state ↔
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
            period hPeriod plusBase minusBase hChart couplings data einsteinScale
              interactionScale coefficients state.1.1.1 = 0 ∧
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
            period hPeriod plusBase minusBase hChart couplings data einsteinScale
              interactionScale coefficients state.1.1.1 = 0) ∧
          (finiteNullFacePhysicalPositionEuler Model state.1.2 = 0 ∧
            finiteNullFacePhysicalIntrinsicEuler Model state.1.2 = 0)
  ll_strong_residual_system :
    forall (metricBoundary : MetricBoundary)
      (fields : IndependentFields period hPeriod),
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
            period hPeriod plusBase minusBase hChart couplings
              (metricBoundary,
                smoothToCompatibleLLCompletion period hPeriod
                  (fields.llAuxMetric, (fields.llMeasure, fields.llField))) ∈
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
            period hPeriod plusBase minusBase hChart couplings →
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
            period hPeriod plusBase minusBase hChart couplings data einsteinScale
              interactionScale coefficients
              (metricBoundary,
                smoothToCompatibleLLCompletion period hPeriod
                  (fields.llAuxMetric, (fields.llMeasure, fields.llField))) = 0 ↔
          (forall point : EffectiveThroat period hPeriod,
            ptSymmetricLLAuxMetricStrongResidual period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod) fields point = 0) ∧
          (forall point : EffectiveThroat period hPeriod,
            llMeasureStrongResidual period hPeriod fields point = 0) ∧
          SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (smoothLLStrongRegularity period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)) fields)

/-- Public terminal `T03` theorem.  Every field is discharged by the concrete
coupled action, compatible completion, faithful null realization and its
covered atlas. -/
theorem program_p_t03_full_euler_lagrange_terminal_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hMinusCenter :
      finiteFramePairedC2MinusCenter period hPeriod Geometry Frame ∈
        generalMetricRelativeC2VolumeDomain period hPeriod Frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ProgramPT03FullEulerLagrangeCertificate4D period hPeriod plusBase minusBase
      hChart couplings faithful data einsteinScale interactionScale
        coefficients where
  fullBRST_core_identification := rfl
  domain_open :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings Model
  domain_nonempty :=
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
      period hPeriod plusBase minusBase hChart couplings Model hMinusCenter
        hTransverse
  ll_smooth_dense := smoothToCompatibleLLCompletion_denseRange period hPeriod
  bulk_GHY_metric_compatible :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHY_compatible
      period hPeriod plusBase minusBase hChart couplings
  null_actionDatum_injective := faithful.actionDatum_injective
  action_fderiv_eq_euler := by
    intro input hInput
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_fderiv
        period hPeriod plusBase minusBase hChart couplings data Model
          einsteinScale interactionScale coefficients hTransverse input hInput
  atlas_cover :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCanonicalAtlas_cover
      period hPeriod plusBase minusBase hChart couplings Model
  transition_hasFDerivAt :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition_hasFDerivAt
      period hPeriod plusBase minusBase hChart couplings Model
  transition_cocycle :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition_cocycle
      period hPeriod plusBase minusBase hChart couplings Model
  chart_action_hasFDerivAt := by
    intro center coordinate hCoordinate
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_hasFDerivAt
        period hPeriod plusBase minusBase hChart couplings Model data
          einsteinScale interactionScale coefficients hTransverse center
            coordinate hCoordinate
  chart_action_transition :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_transition
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients
  chart_euler_covariant :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_covariant
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients
  criticality_iff_four_blocks :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical_iff_four_blocks
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients
  ll_strong_residual_system := by
    intro metricBoundary fields hInput
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler_smooth_eq_zero_iff_strong
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients hTransverse metricBoundary fields hInput

end

end
end P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D
end JanusFormal
