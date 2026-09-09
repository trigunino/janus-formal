import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEulerCore4D

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

local instance atlasLocalInstance1 : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance atlasLocalInstance2 : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance atlasLocalInstance3 : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance atlasLocalInstance4 : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance atlasLocalInstance5 : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance atlasLocalInstance6 : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance atlasLocalInstance7 : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance atlasLocalInstance8 : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance atlasLocalInstance9 :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance atlasLocalInstance10 : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance atlasLocalInstance11 : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance atlasLocalInstance12 : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance atlasLocalInstance13 : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
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

local instance atlasLocalInstance14 : NormedAddCommGroup MetricCore :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod Frame
    plusBase.metric).normedAddCommGroup

local instance atlasLocalInstance15 : NormedSpace Real MetricCore :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod Frame plusBase.metric)

local instance atlasLocalInstance16 : NormedSpace Real OldInput := Prod.normedSpace
local instance atlasLocalInstance17 : NormedSpace Real LLInput := Prod.normedSpace
local instance atlasLocalInstance18 : NormedSpace Real BulkInput := Prod.normedSpace

local instance atlasLocalInstance19 :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance atlasLocalInstance20 :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance atlasLocalInstance21 : NormedSpace Real GHYInput := Prod.normedSpace
local instance atlasLocalInstance22 : SMul Real MetricBoundaryAmbient :=
  Prod.instSMul

local instance atlasLocalInstance23 : ContinuousSMul Real MetricBoundaryAmbient := by
  apply Prod.continuousSMul

local instance atlasLocalInstance24 : NormedSpace Real MetricBoundaryAmbient := Prod.normedSpace
local instance atlasLocalInstance25 : SMul Real AmbientInput := Prod.instSMul

local instance atlasLocalInstance26 : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance atlasLocalInstance27 : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance atlasLocalInstance28 : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance atlasLocalInstance29 : ContinuousSMul Real AmbientInput := by
  apply Prod.continuousSMul

local instance atlasLocalInstance30 : NormedSpace Real AmbientInput := Prod.normedSpace

local instance atlasLocalInstance31 :
    NormedAddCommGroup AmbientCoupled :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance atlasLocalInstance32 : NormedSpace Real AmbientCoupled :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

/-- The bulk/GHY mismatch after inserting zero in the LL slot.  Its kernel is
the metric-boundary graph before the independent compatible LL completion is
adjoined. -/
local notation "MetricBoundary" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore period
    hPeriod plusBase minusBase hChart couplings

local instance atlasLocalInstance33 : SMul Real MetricBoundary :=
  SetLike.smul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance atlasLocalInstance34 :
    NormedAddCommGroup MetricBoundary :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance atlasLocalInstance35 : NormedSpace Real MetricBoundary :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance atlasLocalInstance36 : ContinuousSMul Real MetricBoundary :=
  SMulMemClass.continuousSMul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local notation "CompletedCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore
    period hPeriod plusBase minusBase hChart couplings

section

variable {NullFace : Type*} [Fintype NullFace]

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPhysical" =>
  FiniteNullFacePhysicalHilbert NullFace

local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (model : FiniteNullFacePhysicalActionModel NullFace)

local notation "Carrier" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAdmissibleCarrier
    period hPeriod plusBase minusBase hChart couplings model

local notation "Index" => Carrier

/-- Translation coordinate centered at an admissible state. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
    (center : Index) (input : Input) : Input :=
  input - center.1

/-- Reconstruction from a translated coordinate. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
    (center : Index) (coordinate : Input) : Input :=
  coordinate + center.1

/-- Translated copy of the exact admissible domain. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
    (center : Index) : Set Input :=
  {coordinate |
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center coordinate ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model}

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct_coordinate
    (center : Index) (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
            period hPeriod plusBase minusBase hChart couplings model center input) =
      input := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
  abel

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain_isOpen
    (center : Index) :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
        period hPeriod plusBase minusBase hChart couplings model center) := by
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings model).preimage (by
        change Continuous (fun coordinate : Input => coordinate + center.1)
        exact continuous_id.add continuous_const)

/-- Every admissible state is covered by its centered chart. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCanonicalAtlas_cover
    (state : Carrier) :
    ∃ index : Index,
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
          period hPeriod plusBase minusBase hChart couplings model index state.1 = 0 ∧
        (0 : Input) ∈
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
            period hPeriod plusBase minusBase hChart couplings model index := by
  refine ⟨state, ?_, ?_⟩
  · change state.1 - state.1 = 0
    exact sub_self state.1
  · change
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
          period hPeriod plusBase minusBase hChart couplings model state 0 ∈
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
          period hPeriod plusBase minusBase hChart couplings model
    change (0 : Input) + state.1 ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model
    rw [zero_add]
    exact state.2

/-- Affine transition between two admissible centers. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
    (first second : Index) (coordinate : Input) : Input :=
  coordinate + (first.1 - second.1)

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct_transition
    (first second : Index) (coordinate : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model second
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
            period hPeriod plusBase minusBase hChart couplings model first second
              coordinate) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model first coordinate := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
  abel

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition_coordinate
    (first second : Index) (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
        period hPeriod plusBase minusBase hChart couplings model first second
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
            period hPeriod plusBase minusBase hChart couplings model first input) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
        period hPeriod plusBase minusBase hChart couplings model second input := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
  abel

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition_hasFDerivAt
    (first second : Index) (coordinate : Input) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
        period hPeriod plusBase minusBase hChart couplings model first second)
      (ContinuousLinearMap.id Real Input) coordinate := by
  change HasFDerivAt (fun current : Input => current + (first.1 - second.1))
    (ContinuousLinearMap.id Real Input) coordinate
  exact (ContinuousLinearMap.id Real Input).hasFDerivAt.add_const
    (first.1 - second.1)

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition_cocycle
    (first second third : Index) :
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
        period hPeriod plusBase minusBase hChart couplings model second third) ∘
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
        period hPeriod plusBase minusBase hChart couplings model first second) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
        period hPeriod plusBase minusBase hChart couplings model first third := by
  funext coordinate
  unfold Function.comp
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
  abel

/-- Local action in translated coordinates. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (center : Index) (coordinate : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center coordinate)

/-- Local Euler covector in translated coordinates. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (center : Index) (coordinate : Input) : Input →L[Real] Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center coordinate)

/-- Action descended to the exact admissible carrier. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (state : Carrier) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients state.1

/-- Euler covector descended to the exact admissible carrier. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (state : Carrier) : Input →L[Real] Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients state.1

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (center : Index) (state : Carrier) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
            period hPeriod plusBase minusBase hChart couplings model center state.1) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients state := by
  simp
    [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction,
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasAction]

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (center : Index) (state : Carrier) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartCoordinate
            period hPeriod plusBase minusBase hChart couplings model center state.1) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients state := by
  simp
    [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler,
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasEuler]

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_transition
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (first second : Index) (coordinate : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients second
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
            period hPeriod plusBase minusBase hChart couplings model first second
              coordinate) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients first coordinate := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct_transition
    period hPeriod plusBase minusBase hChart couplings model first second]

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_transition
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (first second : Index) (coordinate : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients second
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
            period hPeriod plusBase minusBase hChart couplings model first second
              coordinate) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients first coordinate := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct_transition
    period hPeriod plusBase minusBase hChart couplings model first second]

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_covariant
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (first second : Index) (coordinate : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients first coordinate =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients second
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartTransition
            period hPeriod plusBase minusBase hChart couplings model first second
              coordinate)).comp
        (ContinuousLinearMap.id Real Input) := by
  simpa only [ContinuousLinearMap.comp_id] using
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_transition
      period hPeriod plusBase minusBase hChart couplings model data einsteinScale
        interactionScale coefficients first second coordinate).symm

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (center : Index) (coordinate : Input)
    (hCoordinate : coordinate ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
        period hPeriod plusBase minusBase hChart couplings model center) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center coordinate)
      coordinate := by
  change
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center coordinate ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model
    at hCoordinate
  have hGlobal :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_hasFDerivAt
      period hPeriod plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients hTransverse
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
          period hPeriod plusBase minusBase hChart couplings model center coordinate)
        hCoordinate
  have hTranslate : HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
        period hPeriod plusBase minusBase hChart couplings model center)
      (ContinuousLinearMap.id Real Input) coordinate := by
    change HasFDerivAt (fun current : Input => current + center.1)
      (ContinuousLinearMap.id Real Input) coordinate
    exact (ContinuousLinearMap.id Real Input).hasFDerivAt.add_const center.1
  have hComposed : HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
          period hPeriod plusBase minusBase hChart couplings data model einsteinScale
            interactionScale coefficients ∘
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
          period hPeriod plusBase minusBase hChart couplings model center)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartReconstruct
            period hPeriod plusBase minusBase hChart couplings model center coordinate))
      coordinate := by
    simpa only [ContinuousLinearMap.comp_id] using
      hGlobal.comp coordinate hTranslate
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
  apply hComposed.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Criticality of the descended Euler covector. -/
def FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (state : Carrier) : Prop :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasEuler
    period hPeriod plusBase minusBase hChart couplings model data einsteinScale
      interactionScale coefficients state = 0

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical_iff_four_blocks
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (state : Carrier) :
    FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients state ↔
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleMetricBoundaryEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients state.1.1.1 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleLLEuler
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients state.1.1.1 = 0) ∧
        (finiteNullFacePhysicalPositionEuler model state.1.2 = 0 ∧
          finiteNullFacePhysicalIntrinsicEuler model state.1.2 = 0) := by
  unfold
    FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasIsEulerCritical
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAtlasEuler
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_zero_iff_four_blocks
      period hPeriod plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients state.1

/-- Given a genuine full-BRST-to-finite projection, this kernel is the exact
fiber product required to adjoin that core to the covered carrier.  Existing
pointwise same-action equalities do not provide `fullBRSTProjection`. -/
def FiniteFrameCompatibleCoupledFullBRSTFiberProduct
    (FullBRSTCore : Type*)
    [NormedAddCommGroup FullBRSTCore] [NormedSpace Real FullBRSTCore]
    (fullBRSTProjection : FullBRSTCore →L[Real] OldInput) :
    Submodule Real (FullBRSTCore × Input) :=
  (fullBRSTProjection.comp
      (ContinuousLinearMap.fst Real FullBRSTCore Input) -
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledFiniteOldProjection
      period hPeriod plusBase minusBase hChart couplings).comp
      (ContinuousLinearMap.snd Real FullBRSTCore Input)).ker

theorem mem_FiniteFrameCompatibleCoupledFullBRSTFiberProduct_iff
    (FullBRSTCore : Type*)
    [NormedAddCommGroup FullBRSTCore] [NormedSpace Real FullBRSTCore]
    (fullBRSTProjection : FullBRSTCore →L[Real] OldInput)
    (pair : FullBRSTCore × Input) :
    pair ∈ FiniteFrameCompatibleCoupledFullBRSTFiberProduct
        period hPeriod plusBase minusBase hChart couplings FullBRSTCore
          fullBRSTProjection ↔
      fullBRSTProjection pair.1 =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledFiniteOldProjection
          period hPeriod plusBase minusBase hChart couplings pair.2 := by
  change
    fullBRSTProjection pair.1 -
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledFiniteOldProjection
        period hPeriod plusBase minusBase hChart couplings pair.2 = 0 ↔ _
  exact sub_eq_zero

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
end JanusFormal
