import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D

/-!
# Canonical vertical integration and evaluation

Gate 819's vertical differential moves an integrated coefficient to its
vertical generator.  This module records that identity for every Gate-833
geometric packet and refines it when the SpinC graph frontier is represented
by the genuine smooth local density from Gate 836.

For the distinguished Gate-819 Lagrangian, evaluation after `dV` is then
identified with the actual derivative of the exact T03 action.  The existing
relative first-variation formula is exposed explicitly as
`dV L = E + dH theta`.

No vertical differential on arbitrary local densities is defined.  The first
two results apply `dV` only after sectorwise integration; the physical
derivative statement is restricted to the canonical T03 Lagrangian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
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
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D.RelativeFirstVariationData
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D
open P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential

/-- Vertical-generator lift of the six values obtained by Gate-830 sectorwise
integration. -/
def programPT05GeometricIntegratedVerticalCochain
    (integrated : ProgramPT05GeometricStratifiedIntegratedAction) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 1
  | .bulk =>
      (0, (integrated.bulkDensityAction + integrated.spinCFrontierAction) +
        integrated.llAction)
  | .nonNullBoundary => (0, integrated.nonNullBoundaryAction)
  | .nullBoundary => (0, integrated.nullBoundaryAction)
  | .joint => (0, integrated.jointAction)

variable (period : Real) (hPeriod : period ≠ 0)

/-- Applying Gate 819's `dV` after Gate-833 integration is exactly the
vertical-generator lift of every separately integrated stratum.  This is an
identity after integration, not a definition of `dV` on densities. -/
theorem programPT05GeometricDensityIntegrationMap_dV_eq_integratedVertical
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05ExactT03RelativeBicomplex.dV 4 0
        (programPT05GeometricDensityIntegrationMap period hPeriod couplings
          density) =
      programPT05GeometricIntegratedVerticalCochain
        (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
          couplings density) := by
  funext stratum
  cases stratum <;>
    norm_num [programPT05ExactT03RelativeBicomplex,
      programPT05RelativeVerticalDifferential,
      programPT05GeometricDensityIntegrationMap,
      programPT05GeometricIntegratedVerticalCochain]

/-- Vertical integrated cochain for packets whose SpinC frontier has a smooth
local-density representative. -/
def programPT05SmoothSpinCGeometricIntegratedVerticalCochain
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace)
    (refinement : ProgramPT05BulkSpinCSmoothLocalDensityRefinement period
      hPeriod couplings density.spinCFrontier) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 1 :=
  let integrated :=
    programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
      couplings density
  fun
  | .bulk =>
      (0, (integrated.bulkDensityAction +
          programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
            couplings.matterMassSquared refinement.smoothState) +
        integrated.llAction)
  | .nonNullBoundary => (0, integrated.nonNullBoundaryAction)
  | .nullBoundary => (0, integrated.nullBoundaryAction)
  | .joint => (0, integrated.jointAction)

/-- On the smooth SpinC subcarrier, the full post-integration `dV` cochain is
expressed using actual local-density integrals in its bulk coefficient. -/
theorem programPT05GeometricDensityIntegrationMap_dV_eq_smoothSpinCIntegratedVertical
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace)
    (refinement : ProgramPT05BulkSpinCSmoothLocalDensityRefinement period
      hPeriod couplings density.spinCFrontier) :
    programPT05ExactT03RelativeBicomplex.dV 4 0
        (programPT05GeometricDensityIntegrationMap period hPeriod couplings
          density) =
      programPT05SmoothSpinCGeometricIntegratedVerticalCochain period hPeriod
        couplings density refinement := by
  rw [programPT05GeometricDensityIntegrationMap_dV_eq_integratedVertical]
  funext stratum
  cases stratum with
  | bulk =>
      change
        (0, ((_ +
          programPT05BulkSpinCFrontierAction period hPeriod couplings
            density.spinCFrontier) + _)) =
        (0, ((_ +
          programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
            couplings.matterMassSquared refinement.smoothState) + _))
      rw [refinement.integral_eq_frontierAction]
  | nonNullBoundary => rfl
  | nullBoundary => rfl
  | joint => rfl

/-- The exact Gate-819 relative first variation, with no additional
hypothesis. -/
theorem programPT05CanonicalRelativeFirstVariation :
    programPT05ExactT03RelativeBicomplex.dV 4 0
        programPT05RelativeLagrangian =
      programPT05RelativeEuler +
        programPT05ExactT03RelativeBicomplex.dH 3 1
          programPT05RelativeBoundaryPotential := by
  exact programPT05ExactT03RelativeFirstVariation.firstVariation

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

section

variable {NullFace : Type*} [Fintype NullFace]
  {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (model : FiniteNullFacePhysicalActionModel NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace
local notation "PriorInput" => CompletedCoupled × NullNormalization

local instance frontierPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance frontierInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

local notation "ExactAction" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients

local notation "ExactEuler" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients

local notation "Domain" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
    period hPeriod plusBase minusBase hChart couplings model

/-- On the canonical Lagrangian, differentiating its exact T03 action
evaluation commutes with applying `dV` and then evaluating the vertical
generator against the exact T03 Euler covector. -/
theorem programPT05CanonicalLagrangianEvaluation_commutes_dV
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input) (hInput : input ∈ Domain) (direction : Input) :
    fderiv Real
        (fun varied : Input ↦
          programPT05ExactT03ActionEvaluation period hPeriod plusBase
            minusBase hChart couplings data model einsteinScale
              interactionScale coefficients varied
                programPT05RelativeLagrangian)
        input direction =
      programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input direction
            (programPT05ExactT03RelativeBicomplex.dV 4 0
              programPT05RelativeLagrangian) := by
  have hEvaluation :
      (fun varied : Input ↦
        programPT05ExactT03ActionEvaluation period hPeriod plusBase minusBase
          hChart couplings data model einsteinScale interactionScale
            coefficients varied programPT05RelativeLagrangian) =
        ExactAction := by
    funext varied
    exact programPT05RelativeLagrangian_evaluates_to_exactT03Action
      period hPeriod plusBase minusBase hChart couplings data model
        einsteinScale interactionScale coefficients varied
  have hFDerivEvaluation := congrArg
    (fun action : Input → Real ↦ fderiv Real action input direction)
    hEvaluation
  have hActionFDeriv := congrArg
    (fun covector : Input →L[Real] Real ↦ covector direction)
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction_fderiv
      period hPeriod plusBase minusBase hChart couplings data model
        einsteinScale interactionScale coefficients hTransverse input hInput)
  calc
    _ = fderiv Real ExactAction input direction := hFDerivEvaluation
    _ = ExactEuler input direction := hActionFDeriv
    _ = _ :=
      (programPT05_dV_lagrangian_evaluates_to_exactT03Euler period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients input direction).symm

/-- The same commuting evaluation square with the vertical differential
replaced by the exact relative decomposition `E + dH theta`. -/
theorem programPT05CanonicalFirstVariationEvaluation_commutes
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : Input) (hInput : input ∈ Domain) (direction : Input) :
    fderiv Real
        (fun varied : Input ↦
          programPT05ExactT03ActionEvaluation period hPeriod plusBase
            minusBase hChart couplings data model einsteinScale
              interactionScale coefficients varied
                programPT05RelativeLagrangian)
        input direction =
      programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input direction
          (programPT05RelativeEuler +
            programPT05ExactT03RelativeBicomplex.dH 3 1
              programPT05RelativeBoundaryPotential) := by
  calc
    _ = programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input direction
            (programPT05ExactT03RelativeBicomplex.dV 4 0
              programPT05RelativeLagrangian) :=
      programPT05CanonicalLagrangianEvaluation_commutes_dV period hPeriod
        plusBase minusBase hChart couplings data model einsteinScale
          interactionScale coefficients hTransverse input hInput direction
    _ = _ := congrArg
      (programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
        hChart couplings data model einsteinScale interactionScale coefficients
          input direction)
      programPT05CanonicalRelativeFirstVariation

end

end
end P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D
end JanusFormal
