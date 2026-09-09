import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D

/-!
# Covered atlas on the compatible metric/GHY/LL/null field space

This module replaces the independent mobile-GHY product by the actual linear
field space used by the finite-frame action:

* the bulk plus metric and the `C³` GHY metric have the same `C²` image;
* the LL coordinate lies in the closure of genuine smooth direct/PT packets;
* null-generator normalization and physical position/screen coordinates are
  retained as separate factors.

The exact admissible domain is open in that normed vector space.  Translation
charts therefore cover it, have affine transitions with identity derivative,
and carry a chart-independent action and Euler covector.  Stationarity splits
into the constrained metric/GHY block, the compatible LL block, and both
physical null blocks.  The normalization factor has no Euler equation.

The current strong full-BRST same-action bridge identifies values at supplied
smooth representatives, but gives no continuous map from a full-BRST core to
this field space.  The final definition records the exact fiber product that
such a map must instantiate; no full-BRST atlas coverage is claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
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
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
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

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod Geometry Frame

local notation "MatterInput" =>
  ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
    couplings.matterMassSquared

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod Geometry
    Frame couplings

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

local instance metricCoreNormedAddCommGroup : NormedAddCommGroup MetricCore :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod Frame
    plusBase.metric).normedAddCommGroup

local instance metricCoreNormedSpace : NormedSpace Real MetricCore :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod Frame plusBase.metric)

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance compatibleCoupledGHYFunctionalCoreNormedAddCommGroup :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance compatibleCoupledGHYFunctionalCoreNormedSpace :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace
local instance metricBoundaryAmbientSMul : SMul Real MetricBoundaryAmbient :=
  Prod.instSMul

local instance : ContinuousSMul Real MetricBoundaryAmbient := by
  apply Prod.continuousSMul

local instance : NormedSpace Real MetricBoundaryAmbient := Prod.normedSpace
local instance compatibleCoupledAmbientSMul : SMul Real AmbientInput := Prod.instSMul

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real AmbientInput := by
  apply Prod.continuousSMul

local instance : NormedSpace Real AmbientInput := Prod.normedSpace

local instance ambientCoupledNormedAddCommGroup :
    NormedAddCommGroup AmbientCoupled :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance ambientCoupledNormedSpace : NormedSpace Real AmbientCoupled :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

/-- The bulk/GHY mismatch after inserting zero in the LL slot.  Its kernel is
the metric-boundary graph before the independent compatible LL completion is
adjoined. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch :
    MetricBoundaryAmbient →L[Real] MetricCore :=
  ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
      period hPeriod plusBase minusBase hChart couplings).comp
      (ContinuousLinearMap.inl Real OldInput LLInput)).comp
      (ContinuousLinearMap.fst Real OldInput GHYInput) -
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
      period hPeriod plusBase).comp
      (ContinuousLinearMap.snd Real OldInput GHYInput)

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch_apply
    (input : MetricBoundaryAmbient) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
          period hPeriod plusBase minusBase hChart couplings (input.1, 0) -
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
          period hPeriod plusBase input.2 :=
  rfl

/-- Metric-matching bulk/GHY directions. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker

local notation "MetricBoundary" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore period
    hPeriod plusBase minusBase hChart couplings

local instance metricBoundarySMul : SMul Real MetricBoundary :=
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

local instance metricBoundaryContinuousSMul : ContinuousSMul Real MetricBoundary :=
  SMulMemClass.continuousSMul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

/-- Actual coupled completed mobile core: metric-matching old/GHY data and a
packet in the closure of genuine smooth LL coefficients. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore :=
  MetricBoundary × CompatibleLL

local notation "CompletedCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore
    period hPeriod plusBase minusBase hChart couplings

/-- Continuous inclusion into the former independent mobile product. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient :
    CompletedCoupled →L[Real] AmbientInput :=
  let graphInclusion : MetricBoundary →L[Real] MetricBoundaryAmbient :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
  let graphProjection : CompletedCoupled →L[Real] MetricBoundary :=
    ContinuousLinearMap.fst Real MetricBoundary CompatibleLL
  let oldProjection : CompletedCoupled →L[Real] OldInput :=
    (ContinuousLinearMap.fst Real OldInput GHYInput).comp
      (graphInclusion.comp graphProjection)
  let llProjection : CompletedCoupled →L[Real] LLInput :=
    (compatibleLLCompletionToAmbient period hPeriod).comp
      (ContinuousLinearMap.snd Real MetricBoundary CompatibleLL)
  let ghyProjection : CompletedCoupled →L[Real] GHYInput :=
    (ContinuousLinearMap.snd Real OldInput GHYInput).comp
      (graphInclusion.comp graphProjection)
  (oldProjection.prod llProjection).prod ghyProjection

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply
    (input : CompletedCoupled) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
        period hPeriod plusBase minusBase hChart couplings input =
      ((input.1.1.1,
          compatibleLLCompletionToAmbient period hPeriod input.2),
        input.1.1.2) :=
  rfl

/-- The compatible completed core lands in the pre-existing metric graph. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph :
    CompletedCoupled →L[Real] AmbientCoupled :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
    period hPeriod plusBase minusBase hChart couplings).codRestrict
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings).ker
      (fun input => by
        have hMetric := input.1.2
        change
          finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch
              period hPeriod plusBase minusBase hChart couplings input.1.1 = 0
          at hMetric
        change
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch
              period hPeriod plusBase minusBase hChart couplings
              (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
                period hPeriod plusBase minusBase hChart couplings input) = 0
        rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch_apply]
          at hMetric
        rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch_apply]
        simp only
          [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient_apply,
            finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection_apply]
        simpa only
          [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection_apply]
          using hMetric)

/-- The graph constraint is the claimed equality of the bulk and GHY metric
coordinates; the compatible LL coordinate is irrelevant to this equality. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHY_compatible
    (input : CompletedCoupled) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
        period hPeriod plusBase minusBase hChart couplings
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
            period hPeriod plusBase minusBase hChart couplings input).1 =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
        period hPeriod plusBase
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
            period hPeriod plusBase minusBase hChart couplings input).2 :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph_compatible
    period hPeriod plusBase minusBase hChart couplings
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings input)

section

variable {NullFace : Type*} [Fintype NullFace]

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPhysical" =>
  FiniteNullFacePhysicalHilbert NullFace

local notation "PriorInput" => CompletedCoupled × NullNormalization

/-- Actual coupled field space including null normalization and physical
position/screen modes. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore :=
  PriorInput × NullPhysical

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Projection to the metric/GHY/compatible-LL factor. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection :
    Input →L[Real] CompletedCoupled :=
  (ContinuousLinearMap.fst Real CompletedCoupled NullNormalization).comp
    (ContinuousLinearMap.fst Real PriorInput NullPhysical)

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection_apply
    (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection
        period hPeriod plusBase minusBase hChart couplings input = input.1.1 :=
  rfl

/-- Projection to the physical null-face factor. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection :
    Input →L[Real] NullPhysical :=
  ContinuousLinearMap.snd Real PriorInput NullPhysical

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection_apply
    (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection
        period hPeriod plusBase minusBase hChart couplings input = input.2 :=
  rfl

/-- Projection of the actual coupled field space to the finite old
physical/Maxwell/SpinC block.  This is the finite leg of the full-BRST fiber
product stated below. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledFiniteOldProjection :
    Input →L[Real] OldInput :=
  (ContinuousLinearMap.fst Real OldInput LLInput).comp
    ((ContinuousLinearMap.fst Real BulkInput GHYInput).comp
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToAmbient
        period hPeriod plusBase minusBase hChart couplings).comp
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection
          period hPeriod plusBase minusBase hChart couplings)))

/-- Product of the pulled-back coupled domain, the unrestricted normalization
factor, and the supplied physical null action domain. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
    (model : FiniteNullFacePhysicalActionModel NullFace) : Set Input :=
  (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
      period hPeriod plusBase minusBase hChart couplings) ⁻¹'
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings) ×ˢ
    Set.univ) ×ˢ model.domain

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain_isOpen
    (model : FiniteNullFacePhysicalActionModel NullFace) :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :=
  (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings).preimage
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
          period hPeriod plusBase minusBase hChart couplings).continuous).prod
    isOpen_univ).prod model.domain_isOpen

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (hMinusCenter :
      finiteFramePairedC2MinusCenter period hPeriod Geometry Frame ∈
        generalMetricRelativeC2VolumeDomain period hPeriod Frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    (0 : Input) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model := by
  refine ⟨⟨?_, Set.mem_univ _⟩, model.zero_mem_domain⟩
  simpa using
    (zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
      period hPeriod plusBase minusBase hChart couplings hMinusCenter hTransverse)

/-- The coupled mobile action plus the physical null-face action. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings input.1.1) +
    model.action input.2

/-- Euler covector on the completed metric/GHY/LL factor. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CompletedCoupled) : CompletedCoupled →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphEuler
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings input)).comp
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
      period hPeriod plusBase minusBase hChart couplings)

/-- Restriction of the completed Euler covector to compatible metric/GHY
directions, with the LL variation held at zero. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CompletedCoupled) : MetricBoundary →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients input).comp
    (ContinuousLinearMap.inl Real MetricBoundary CompatibleLL)

/-- Restriction to the corrected LL completion, with the metric/GHY direction
held at zero. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CompletedCoupled) : CompatibleLL →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients input).comp
    (ContinuousLinearMap.inr Real MetricBoundary CompatibleLL)

/-- Full Euler covector.  The normalization factor is absent because the
finite null reparametrization action is exactly invariant. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients input.1.1).comp
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection
        period hPeriod plusBase minusBase hChart couplings) +
    (finiteNullFacePhysicalEuler model input.2).comp
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection
        period hPeriod plusBase minusBase hChart couplings)

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients input)
      input := by
  have hCoupledBase :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_hasFDerivAt
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients hTransverse
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
          period hPeriod plusBase minusBase hChart couplings input.1.1)
        hInput.1.1
  have hCoupledOnCompletion := hCoupledBase.comp input.1.1
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
      period hPeriod plusBase minusBase hChart couplings).hasFDerivAt
  have hCoupled := hCoupledOnCompletion.comp input
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection
      period hPeriod plusBase minusBase hChart couplings).hasFDerivAt
  have hNullBase : HasFDerivAt model.action
      (finiteNullFacePhysicalEuler model input.2) input.2 := by
    unfold finiteNullFacePhysicalEuler
    exact
      (((model.action_contDiffOn_two.contDiffAt
        (model.domain_isOpen.mem_nhds hInput.2)).differentiableAt
          (by norm_num)).hasFDerivAt)
  have hNull := hNullBase.comp input
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection
      period hPeriod plusBase minusBase hChart couplings).hasFDerivAt
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
  apply (hCoupled.add hNull).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    fderiv Real
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
          period hPeriod plusBase minusBase hChart couplings data model
            einsteinScale interactionScale coefficients) input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients input :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_hasFDerivAt
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients hTransverse input hInput).fderiv

/-- A completed coupled covector vanishes exactly when its metric/GHY and
compatible-LL restrictions vanish. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler_eq_zero_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CompletedCoupled) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input = 0 := by
  constructor
  · intro hEuler
    constructor <;> simp
      [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler,
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler, hEuler]
  · rintro ⟨hMetricBoundary, hLL⟩
    apply ContinuousLinearMap.ext
    rintro ⟨metricBoundaryDirection, llDirection⟩
    have hMetricBoundaryValue :=
      DFunLike.congr_fun hMetricBoundary metricBoundaryDirection
    have hLLValue := DFunLike.congr_fun hLL llDirection
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input (metricBoundaryDirection, 0) = 0
      at hMetricBoundaryValue
    change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input (0, llDirection) = 0
      at hLLValue
    calc
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input (metricBoundaryDirection, llDirection) =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
            period hPeriod plusBase minusBase hChart couplings data einsteinScale
              interactionScale coefficients input
              ((metricBoundaryDirection, 0) + (0, llDirection)) := by simp
      _ = _ := map_add _ _ _
      _ = 0 + 0 := congrArg₂ (· + ·) hMetricBoundaryValue hLLValue
      _ = 0 := add_zero 0

/-- Stationarity on the actual field space has precisely three independent
blocks.  Metric and GHY variations remain coupled through their graph. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_zero_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients input = 0 ↔
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input.1.1 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input.1.1 = 0) ∧
        finiteNullFacePhysicalEuler model input.2 = 0 := by
  have hCoupledSplit :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler_eq_zero_iff
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients input.1.1
  constructor
  · intro hTotal
    have hCoupledZero :
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYEuler
            period hPeriod plusBase minusBase hChart couplings data einsteinScale
              interactionScale coefficients input.1.1 = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative (((direction, (0 : NullNormalization)),
            (0 : NullPhysical)))) hTotal
      simpa
        [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection]
        using hValue
    have hNullZero : finiteNullFacePhysicalEuler model input.2 = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative ((((0 : CompletedCoupled),
            (0 : NullNormalization)), direction))) hTotal
      simpa
        [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYProjection,
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleNullPhysicalProjection]
        using hValue
    exact ⟨hCoupledSplit.mp hCoupledZero, hNullZero⟩
  · rintro ⟨hCoupled, hNull⟩
    have hCoupledZero := hCoupledSplit.mpr hCoupled
    simp
      [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler,
        hCoupledZero, hNull]

/-- The physical null block separates further into position and intrinsic
screen-metric equations. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_zero_iff_four_blocks
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients input = 0 ↔
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input.1.1 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients input.1.1 = 0) ∧
        (finiteNullFacePhysicalPositionEuler model input.2 = 0 ∧
          finiteNullFacePhysicalIntrinsicEuler model input.2 = 0) := by
  have hTotalSplit :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_zero_iff
      period hPeriod plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients input
  have hNullSplit :=
    finiteNullFacePhysicalEuler_eq_zero_iff_position_and_intrinsic model input.2
  constructor
  · intro hEuler
    exact ⟨(hTotalSplit.mp hEuler).1, hNullSplit.mp (hTotalSplit.mp hEuler).2⟩
  · rintro ⟨hCoupled, hNull⟩
    exact hTotalSplit.mpr ⟨hCoupled, hNullSplit.mpr hNull⟩

/-- Exact admissible carrier of the actual coupled action. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAdmissibleCarrier
    (model : FiniteNullFacePhysicalActionModel NullFace) :=
  {input : Input //
    input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model}

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
end JanusFormal
