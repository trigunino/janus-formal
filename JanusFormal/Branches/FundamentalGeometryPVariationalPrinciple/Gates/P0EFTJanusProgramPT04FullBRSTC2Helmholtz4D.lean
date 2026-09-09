import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

/-!
# Full-BRST C2 Helmholtz support for T04

On the exact coupled core and open domain used by terminal T03, the action is
twice continuously differentiable, its actual gradient is the canonical Euler
covector, and that covector has a symmetric Frechet Jacobian.  The same facts
hold in every translated chart of the covered T03 atlas.

This is a functional Helmholtz support gate.  It does not claim the local
jet-PDE Helmholtz identities or close terminal T04.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D

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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Transfer the Hessian symmetry of a C2 action to any locally equal Euler
covector on an open domain. -/
theorem helmholtzJacobianOn_of_contDiffOn_two_of_eq_actionGradient
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    {domain : Set Configuration}
    (hOpen : IsOpen domain)
    (action : Configuration → Real)
    (euler : EulerOneForm Configuration)
    (hSmooth : ContDiffOn Real 2 action domain)
    (hEuler : ∀ input ∈ domain, euler input = actionGradient action input) :
    HelmholtzJacobianOn domain euler := by
  intro input hInput
  have hGradient := action_gradient_helmholtz_at action input
    (hSmooth.contDiffAt (hOpen.mem_nhds hInput))
  have hEventually : euler =ᶠ[nhds input] actionGradient action := by
    filter_upwards [hOpen.mem_nhds hInput] with current hCurrent
    exact hEuler current hCurrent
  intro first second
  rw [hEventually.fderiv_eq]
  exact hGradient first second

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

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

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

section

variable {NullFace : Type*} [Fintype NullFace]
  (model : FiniteNullFacePhysicalActionModel NullFace)

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace

local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local notation "Carrier" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAdmissibleCarrier
    period hPeriod plusBase minusBase hChart couplings model

local notation "Index" => Carrier

local instance : ContinuousSMul Real CompletedCoupled := by
  apply Prod.continuousSMul

local instance terminalPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance terminalInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

/-- The mobile action remains C2 after restriction to the metric/GHY graph. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings) := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_contDiffOn_two
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase data einsteinScale interactionScale coefficients
        hTransverse).comp
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings).ker.subtypeL.contDiff.contDiffOn)
      (by
        intro input hInput
        exact hInput)

/-- The graph action remains C2 after the compatible LL completion. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ContDiffOn Real 2
      (fun input : CompletedCoupled =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
            period hPeriod plusBase minusBase hChart couplings input))
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
          period hPeriod plusBase minusBase hChart couplings) ⁻¹'
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
          period hPeriod plusBase minusBase hChart couplings) := by
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients hTransverse).comp
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
        period hPeriod plusBase minusBase hChart couplings).contDiff.contDiffOn)
      (by
        intro input hInput
        exact hInput)

/-- The coupled part of the exact T03 action is C2 on the full admissible domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_coupledPart_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ContDiffOn Real 2
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients
          (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYToMetricGraph
            period hPeriod plusBase minusBase hChart couplings input.1.1))
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) := by
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings data einsteinScale
        interactionScale coefficients hTransverse).comp
      contDiff_fst.fst.contDiffOn
      (fun _ hInput => hInput.1.1)

/-- The physical null-face part is C2 on the full T03 admissible domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_nullPart_contDiffOn_two :
    ContDiffOn Real 2
      (fun input : Input => model.action input.2)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) := by
  exact model.action_contDiffOn_two.comp contDiff_snd.contDiffOn
    (fun _ hInput => hInput.2)

/-- The exact T03 action is C2 on its exact coupled admissible domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) := by
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_coupledPart_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings model data einsteinScale
        interactionScale coefficients hTransverse).add
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_nullPart_contDiffOn_two
        period hPeriod plusBase minusBase hChart couplings model)

/-- On the T03 domain, the canonical Euler covector is the actual gradient. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_actionGradient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients input =
      actionGradient
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
          period hPeriod plusBase minusBase hChart couplings data model
            einsteinScale interactionScale coefficients) input := by
  symm
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_fderiv
      period hPeriod plusBase minusBase hChart couplings data model einsteinScale
        interactionScale coefficients hTransverse input hInput

/-- Functional nonlinear Helmholtz symmetry on the full exact T03 domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysical_helmholtzJacobianOn
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    HelmholtzJacobianOn
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings model)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
        period hPeriod plusBase minusBase hChart couplings data model
          einsteinScale interactionScale coefficients) := by
  exact helmholtzJacobianOn_of_contDiffOn_two_of_eq_actionGradient
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings model)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
      period hPeriod plusBase minusBase hChart couplings data model
        einsteinScale interactionScale coefficients)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
      period hPeriod plusBase minusBase hChart couplings data model
        einsteinScale interactionScale coefficients)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_actionGradient
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse)

/-- Every translated T03 chart action remains C2 on its translated domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (center : Index) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
        period hPeriod plusBase minusBase hChart couplings model center) := by
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse).comp
      ((contDiff_id.add contDiff_const).contDiffOn)
      (by
        intro coordinate hCoordinate
        exact hCoordinate)

/-- In each translated chart, its canonical Euler is the actual gradient. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_eq_actionGradient
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
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center coordinate =
      actionGradient
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
          period hPeriod plusBase minusBase hChart couplings model data
            einsteinScale interactionScale coefficients center) coordinate := by
  symm
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_hasFDerivAt
      period hPeriod plusBase minusBase hChart couplings model data einsteinScale
        interactionScale coefficients hTransverse center coordinate
          hCoordinate).fderiv

/-- Functional Helmholtz symmetry in every translated chart of the T03 atlas. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChart_helmholtzJacobianOn
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (center : Index) :
    HelmholtzJacobianOn
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
        period hPeriod plusBase minusBase hChart couplings model center)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings model data
          einsteinScale interactionScale coefficients center) := by
  exact helmholtzJacobianOn_of_contDiffOn_two_of_eq_actionGradient
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings model center)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients center)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients center)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse center)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler_eq_actionGradient
      period hPeriod plusBase minusBase hChart couplings model data
        einsteinScale interactionScale coefficients hTransverse center)

end

end
end P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
end JanusFormal
