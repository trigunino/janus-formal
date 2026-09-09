import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

/-!
# Exact metric-boundary Euler split for T04

This module exposes the old physical/Maxwell/SpinC and mobile GHY contributions
inside the metric-matching graph of the exact T03 core.  It isolates the precise
strong-residual obligation that remains after the two physical null blocks.
It does not reuse a covector as a residual and does not close terminal T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03MetricBoundaryEulerSplit4D

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
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
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

open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusProgramPT04T03LocalJetPDEFrontier4D

/-- Old physical/Maxwell/SpinC leg of a metric-matching graph direction. -/
def programPT04T03MetricBoundaryOldProjection : MetricBoundary →L[Real] OldInput :=
  (ContinuousLinearMap.fst Real OldInput GHYInput).comp
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL

/-- Mobile GHY leg of a metric-matching graph direction. -/
def programPT04T03MetricBoundaryGHYProjection : MetricBoundary →L[Real] GHYInput :=
  (ContinuousLinearMap.snd Real OldInput GHYInput).comp
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL

@[simp] theorem programPT04T03MetricBoundaryOldProjection_apply
    (direction : MetricBoundary) :
    programPT04T03MetricBoundaryOldProjection period hPeriod plusBase minusBase
        hChart couplings direction = direction.1.1 :=
  rfl

@[simp] theorem programPT04T03MetricBoundaryGHYProjection_apply
    (direction : MetricBoundary) :
    programPT04T03MetricBoundaryGHYProjection period hPeriod plusBase minusBase
        hChart couplings direction = direction.1.2 :=
  rfl

/-- Sum of the genuine old bulk Euler and mobile GHY Euler, both pulled back to
the metric-matching graph. -/
def programPT04T03MetricBoundaryOldGHYSplitEulerAt (input : Input) :
    MetricBoundary →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod Geometry
      Frame
      (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
        period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings interactionScale coefficients
      (programPT04T03MetricBoundaryOldProjection period hPeriod plusBase
        minusBase hChart couplings input.1.1.1)).comp
    (programPT04T03MetricBoundaryOldProjection period hPeriod plusBase minusBase
      hChart couplings) +
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler period
      hPeriod plusBase einsteinScale
      (programPT04T03MetricBoundaryGHYProjection period hPeriod plusBase
        minusBase hChart couplings input.1.1.1)).comp
    (programPT04T03MetricBoundaryGHYProjection period hPeriod plusBase minusBase
      hChart couplings)

/-- The completed metric-boundary Euler is the old physical/Maxwell/SpinC and
mobile GHY sum on each constrained direction. -/
theorem programPT04T03CompatibleMetricBoundaryEuler_eq_old_add_ghy
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input.1.1 =
      programPT04T03MetricBoundaryOldGHYSplitEulerAt period hPeriod plusBase
        minusBase hChart couplings einsteinScale interactionScale coefficients
          input := by
  apply ContinuousLinearMap.ext
  intro direction
  let current : AmbientInput :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings input.1.1)
  have hCurrent : current =
      ((input.1.1.1.1.1,
          compatibleLLCompletionToAmbient period hPeriod input.1.1.2),
        input.1.1.1.1.2) := by
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
          period hPeriod plusBase minusBase hChart couplings input.1.1 = _
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply
        period hPeriod plusBase minusBase hChart couplings input.1.1
  let delta : AmbientInput :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings
          (direction, (0 : CompatibleLL)))
  have hDelta : delta =
      ((direction.1.1,
          compatibleLLCompletionToAmbient period hPeriod (0 : CompatibleLL)),
        direction.1.2) := by
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
          period hPeriod plusBase minusBase hChart couplings
            (direction, (0 : CompatibleLL)) = _
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply
        period hPeriod plusBase minusBase hChart couplings
          (direction, (0 : CompatibleLL))
  change
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        Geometry Frame
          (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
            period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        couplings plusBase data einsteinScale interactionScale coefficients
          current delta =
      programPT04T03MetricBoundaryOldGHYSplitEulerAt period hPeriod plusBase
        minusBase hChart couplings einsteinScale interactionScale coefficients
          input direction
  have hMobile := DFunLike.congr_fun
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_bulk_add_ghy
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase data einsteinScale interactionScale coefficients
        hTransverse current hInput.1.1) delta
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
      programPT04T03MetricBoundaryOldGHYSplitEulerAt period hPeriod plusBase
        minusBase hChart couplings einsteinScale interactionScale coefficients
          input direction
  have hBulk := DFunLike.congr_fun
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings interactionScale coefficients current.1 hInput.1.1.1) delta.1
  rw [hBulk, hCurrent, hDelta]
  simp [programPT04T03MetricBoundaryOldGHYSplitEulerAt,
    ContinuousLinearMap.comp_apply, add_apply]

/-- On the exact T03 domain, the metric-boundary restriction is precisely the
sum of the old physical/Maxwell/SpinC and mobile GHY covectors on the constrained
graph. -/
theorem programPT04T03MetricBoundaryEulerRestrictionAt_eq_old_add_ghy
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input =
      programPT04T03MetricBoundaryOldGHYSplitEulerAt period hPeriod plusBase
        minusBase hChart couplings einsteinScale interactionScale coefficients
          input :=
  (programPT04T03MetricBoundaryEulerRestrictionAt_eq period hPeriod plusBase
    minusBase hChart couplings data model einsteinScale interactionScale
      coefficients input).trans
    (programPT04T03CompatibleMetricBoundaryEuler_eq_old_add_ghy period hPeriod
      plusBase minusBase hChart couplings data model einsteinScale interactionScale
        coefficients hTransverse input hInput)

/-- The remaining strong problem after the exact split: construct a residual
which separates the constrained sum of the already-defined old and GHY Euler
pairings.  Its carrier cannot be obtained by merely pairing two independent
ambient residuals, because `MetricBoundary` is the kernel of their metric
mismatch. -/
def ProgramPT04T03MetricBoundaryOldGHYGraphResidualObligationAt
    (input : Input) : Type _ :=
  SeparatingPDEResidualRepresentation
    (programPT04T03MetricBoundaryOldGHYSplitEulerAt period hPeriod plusBase
      minusBase hChart couplings einsteinScale interactionScale coefficients
        input).toLinearMap

/-- Any strong residual for the constrained Old+GHY sum transports exactly to
the T03 metric-boundary Euler restriction at an admissible input. -/
def programPT04T03MetricBoundaryResidualRepresentationAt_of_oldGHYGraph
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model)
    (representation :
      ProgramPT04T03MetricBoundaryOldGHYGraphResidualObligationAt period hPeriod
        plusBase minusBase hChart couplings einsteinScale interactionScale
          coefficients input) :
    SeparatingPDEResidualRepresentation
      (programPT04T03MetricBoundaryEulerRestrictionAt period hPeriod plusBase
        minusBase hChart couplings data model einsteinScale interactionScale
          coefficients input).toLinearMap := by
  rw [programPT04T03MetricBoundaryEulerRestrictionAt_eq_old_add_ghy period
    hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients hTransverse input hInput]
  exact representation

end

end
end P0EFTJanusProgramPT04T03MetricBoundaryEulerSplit4D
end JanusFormal

\n