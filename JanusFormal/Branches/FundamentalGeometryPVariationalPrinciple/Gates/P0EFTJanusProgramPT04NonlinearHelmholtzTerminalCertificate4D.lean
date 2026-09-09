import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FourBlockHelmholtzReciprocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03MetricBoundaryGHYDensityJetBridge4D

/-!
# Terminal nonlinear Helmholtz certificate for T04

The terminal criterion here is the variationality of the exact T03 Euler
covector: the concrete action is C2, its Frechet derivative is the Euler
covector, and the Euler Jacobian is symmetric on the exact domain and in every
translated atlas chart.  Gate 832 supplies all ten diagonal and crossed
reciprocities of the four physical block injections.

Gates 831, 855 and 858 remain stronger local-residual and density-jet support.
A complete geometric PDE representation of the constrained metric/GHY block
is a separate objective and is not a condition of this certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04NonlinearHelmholtzTerminalCertificate4D
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
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
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
open P0EFTJanusProgramPT04T03FourBlockHelmholtzReciprocity4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPosition" => FiniteNullFacePositionHilbert NullFace
local notation "NullIntrinsic" => FiniteNullFaceIntrinsicMetricHilbert NullFace
local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace
local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local notation "Carrier" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAdmissibleCarrier
    period hPeriod plusBase minusBase hChart couplings Model

local instance terminalPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance terminalInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

local notation "FullAction" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data Model einsteinScale
      interactionScale coefficients

local notation "FullEuler" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data Model einsteinScale
      interactionScale coefficients

local notation "Domain" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
    period hPeriod plusBase minusBase hChart couplings Model

/-- Symmetry of the exact Euler Jacobian on two selected full-space directions. -/
def programPT04T03HelmholtzPairAt
    (input first second : Input) : Prop :=
  fderiv Real FullEuler input first second =
    fderiv Real FullEuler input second first

local notation "PairAt" =>
  programPT04T03HelmholtzPairAt period hPeriod plusBase minusBase hChart
    couplings faithful data einsteinScale interactionScale coefficients

/-- The ten diagonal and crossed restrictions of Helmholtz symmetry to the
metric-boundary, compatible-LL, null-position and null-intrinsic injections. -/
structure ProgramPT04T03FourBlockHelmholtzReciprocityAt
    (input : Input) : Prop where
  metric_metric : ∀ first second : MetricBoundary,
    PairAt input
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings second)
  metric_ll : ∀ first : MetricBoundary, ∀ second : CompatibleLL,
    PairAt input
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings second)
  metric_nullPosition : ∀ first : MetricBoundary, ∀ second : NullPosition,
    PairAt input
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings second)
  metric_nullIntrinsic : ∀ first : MetricBoundary, ∀ second : NullIntrinsic,
    PairAt input
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings second)
  ll_ll : ∀ first second : CompatibleLL,
    PairAt input
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings second)
  ll_nullPosition : ∀ first : CompatibleLL, ∀ second : NullPosition,
    PairAt input
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings second)
  ll_nullIntrinsic : ∀ first : CompatibleLL, ∀ second : NullIntrinsic,
    PairAt input
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings second)
  nullPosition_nullPosition : ∀ first second : NullPosition,
    PairAt input
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings second)
  nullPosition_nullIntrinsic : ∀ first : NullPosition, ∀ second : NullIntrinsic,
    PairAt input
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings second)
  nullIntrinsic_nullIntrinsic : ∀ first second : NullIntrinsic,
    PairAt input
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings first)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings second)

private def programPT04T03FourBlockHelmholtzReciprocityAt_of_gate832
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input) (hInput : input ∈ Domain) :
    ProgramPT04T03FourBlockHelmholtzReciprocityAt period hPeriod plusBase
      minusBase hChart couplings faithful data einsteinScale interactionScale
        coefficients input where
  metric_metric := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  metric_ll := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  metric_nullPosition := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  metric_nullIntrinsic := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03MetricBoundaryInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  ll_ll := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  ll_nullPosition := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  ll_nullIntrinsic := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03CompatibleLLInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  nullPosition_nullPosition := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  nullPosition_nullIntrinsic := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03NullPositionInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second
  nullIntrinsic_nullIntrinsic := by
    intro first second
    exact programPT04T03InjectedHelmholtzPairAt period hPeriod plusBase
      minusBase hChart couplings data Model einsteinScale interactionScale
        coefficients
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings)
      (programPT04T03NullIntrinsicInjection period hPeriod plusBase minusBase
        hChart couplings) hTransverse input hInput first second

/-- Terminal T04 certificate for nonlinear functional Helmholtz variationality
on the exact T03 field carrier and its covered translated atlas. -/
structure ProgramPT04NonlinearHelmholtzCertificate4D : Prop where
  exact_domain_open : IsOpen Domain
  exact_domain_nonempty : (0 : Input) ∈ Domain
  action_contDiffOn_two : ContDiffOn Real 2 FullAction Domain
  euler_eq_actionGradient : ∀ input : Input, input ∈ Domain →
    FullEuler input = actionGradient FullAction input
  global_helmholtz : HelmholtzJacobianOn Domain FullEuler
  translated_chart_helmholtz : ∀ center : Carrier,
    HelmholtzJacobianOn
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartDomain
        period hPeriod plusBase minusBase hChart couplings Model center)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChartEuler
        period hPeriod plusBase minusBase hChart couplings Model data
          einsteinScale interactionScale coefficients center)
  four_block_reciprocity : ∀ input : Input, input ∈ Domain →
    ProgramPT04T03FourBlockHelmholtzReciprocityAt period hPeriod plusBase
      minusBase hChart couplings faithful data einsteinScale interactionScale
        coefficients input

/-- Public terminal T04 theorem for nonlinear Helmholtz variationality. -/
theorem program_p_t04_nonlinear_helmholtz_terminal_gate
    (hMinusCenter :
      finiteFramePairedC2MinusCenter period hPeriod Geometry Frame ∈
        generalMetricRelativeC2VolumeDomain period hPeriod Frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ProgramPT04NonlinearHelmholtzCertificate4D period hPeriod plusBase minusBase
      hChart couplings faithful data einsteinScale interactionScale
        coefficients where
  exact_domain_open :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain_isOpen
      period hPeriod plusBase minusBase hChart couplings Model
  exact_domain_nonempty :=
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
      period hPeriod plusBase minusBase hChart couplings Model hMinusCenter
        hTransverse
  action_contDiffOn_two :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_contDiffOn_two
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients hTransverse
  euler_eq_actionGradient := by
    intro input hInput
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_actionGradient
        period hPeriod plusBase minusBase hChart couplings Model data
          einsteinScale interactionScale coefficients hTransverse input hInput
  global_helmholtz :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysical_helmholtzJacobianOn
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients hTransverse
  translated_chart_helmholtz :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalChart_helmholtzJacobianOn
      period hPeriod plusBase minusBase hChart couplings Model data
        einsteinScale interactionScale coefficients hTransverse
  four_block_reciprocity := by
    intro input hInput
    exact programPT04T03FourBlockHelmholtzReciprocityAt_of_gate832 period
      hPeriod plusBase minusBase hChart couplings faithful data einsteinScale
        interactionScale coefficients hTransverse input hInput

end

end
end P0EFTJanusProgramPT04NonlinearHelmholtzTerminalCertificate4D
end JanusFormal
