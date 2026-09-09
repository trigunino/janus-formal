import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D

/-!
# Dominated null-face differentiation at the T03 component

This gate supplies the missing analytic passage from the faithful pointwise null
density to the derivative of its interval integral.  The contract records only
a neighborhood, measurability, pointwise differentiability and an integrable
majorant for the norm of the actual Frechet derivative.  Mathlib's dominated
parametric interval-integral theorem then gives the facewise derivative.

Endpoint differentiability upgrades this result to the complete face action.
A finite sum identifies Gate 838's total-action jet with the sum of these
facewise derivatives and therefore gives integral formulas for both T03 Riesz
pairings.  No domination or endpoint differentiability is inferred from the
mobile geometric datum; those are the remaining analytic construction duties.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D

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

open scoped Interval
open P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D
open P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

/-- The faithful pointwise null density as a family in the physical state. -/
def programPT04T03FaithfulNullFaceDensityFamily
    (face : NullFace) (state : NullPhysical) (parameter : Real) : Real :=
  nullFaceDensity
    (faithful.realization.geometry.toFiniteNullFaceActionDatum state face)
    parameter

/-- The actual physical-state Frechet derivative of the pointwise density. -/
def programPT04T03FaithfulNullFaceDensityFDeriv
    (face : NullFace) (state : NullPhysical) (parameter : Real) :
    NullPhysical →L[Real] Real :=
  fderiv Real
    (fun current : NullPhysical =>
      programPT04T03FaithfulNullFaceDensityFamily faithful face current
        parameter)
    state

/-- Honest dominated-differentiation hypotheses for one faithful null face.
The derivative appearing here is the actual `fderiv` of the density family;
the desired integral identity is not a field of this structure. -/
structure ProgramPT04T03FaithfulNullFaceDominatedFDerivContract
    (face : NullFace) (base : NullPhysical) where
  neighborhood : Set NullPhysical
  neighborhood_mem_nhds : neighborhood ∈ 𝓝 base
  density_eventually_aeStronglyMeasurable :
    ∀ᶠ state in 𝓝 base,
      AEStronglyMeasurable
        (programPT04T03FaithfulNullFaceDensityFamily faithful face state)
        (MeasureTheory.volume.restrict
          (Ι (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter))
  density_fderiv_aeStronglyMeasurable :
    AEStronglyMeasurable
      (programPT04T03FaithfulNullFaceDensityFDeriv faithful face base)
      (MeasureTheory.volume.restrict
        (Ι (faithful.realization.geometry.interval face).initialParameter
          (faithful.realization.geometry.interval face).finalParameter))
  bound : Real → Real
  density_fderiv_norm_le :
    ∀ᵐ parameter ∂MeasureTheory.volume,
      parameter ∈
          Ι (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter →
        ∀ state ∈ neighborhood,
          ‖programPT04T03FaithfulNullFaceDensityFDeriv faithful face state
            parameter‖ ≤ bound parameter
  bound_intervalIntegrable :
    IntervalIntegrable bound MeasureTheory.volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter
  density_differentiableAt :
    ∀ parameter,
      parameter ∈
          Ι (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter →
        ∀ state ∈ neighborhood,
          DifferentiableAt Real
            (fun current : NullPhysical =>
              programPT04T03FaithfulNullFaceDensityFamily faithful face current
                parameter)
            state

/-- Endpoint differentiability is the only extra input needed to pass from
the integrated density to the complete face-plus-joints action. -/
structure ProgramPT04T03FaithfulNullFaceActionFDerivContract
    (face : NullFace) (base : NullPhysical)
    extends ProgramPT04T03FaithfulNullFaceDominatedFDerivContract faithful face
      base where
  initialJoint_differentiableAt :
    DifferentiableAt Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).initialJointAction)
      base
  finalJoint_differentiableAt :
    DifferentiableAt Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).finalJointAction)
      base

private theorem programPT04T03FaithfulNullState_mem_geometryDomain
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model) :
    input.2 ∈ faithful.realization.geometry.domain := by
  simpa only [toActionModel_domain,
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization_domain]
    using hInput.2

/-- Mathlib's dominated theorem gives the true physical-state derivative
under the oriented null-generator interval integral. -/
theorem programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (contract : ProgramPT04T03FaithfulNullFaceDominatedFDerivContract
      faithful face input.2) :
    HasFDerivAt
      (fun state : NullPhysical =>
        integratedNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
      (∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face input.2
          parameter)
      input.2 := by
  have hNull : input.2 ∈ faithful.realization.geometry.domain :=
    programPT04T03FaithfulNullState_mem_geometryDomain period hPeriod plusBase
      minusBase hChart couplings faithful input hInput
  have hDatumIntegrability :=
    faithful.realization.intervalIntegrability input.2 hNull face
  have hDensityIntegrable :
      IntervalIntegrable
        (programPT04T03FaithfulNullFaceDensityFamily faithful face input.2)
        MeasureTheory.volume
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter := by
    change IntervalIntegrable
      (fun parameter =>
        inaffinityFaceDensity
            (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2
              face) parameter +
          expansionCountertermFaceDensity
            (faithful.realization.geometry.toFiniteNullFaceActionDatum input.2
              face) parameter)
      MeasureTheory.volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter
    exact hDatumIntegrability.inaffinity.add
      hDatumIntegrability.expansionCounterterm
  have hIntegral :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := programPT04T03FaithfulNullFaceDensityFamily faithful face)
      (F' := fun state parameter =>
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face state
          parameter)
      (s := contract.neighborhood)
      (x₀ := input.2)
      (a := (faithful.realization.geometry.interval face).initialParameter)
      (b := (faithful.realization.geometry.interval face).finalParameter)
      (bound := contract.bound)
      (μ := MeasureTheory.volume)
      contract.neighborhood_mem_nhds
      contract.density_eventually_aeStronglyMeasurable
      hDensityIntegrable
      contract.density_fderiv_aeStronglyMeasurable
      contract.density_fderiv_norm_le
      contract.bound_intervalIntegrable
      (Filter.Eventually.of_forall fun parameter hParameter state hState =>
        (contract.density_differentiableAt parameter hParameter state
          hState).hasFDerivAt)
  exact hIntegral.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The face-integral `fderiv` is the interval integral of the actual
pointwise density `fderiv`. -/
theorem programPT04T03FaithfulIntegratedNullFaceAction_fderiv_eq_integral
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (contract : ProgramPT04T03FaithfulNullFaceDominatedFDerivContract
      faithful face input.2) :
    fderiv Real
        (fun state : NullPhysical =>
          integratedNullFaceAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face))
        input.2 =
      ∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face input.2
          parameter :=
  (programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt period hPeriod
    plusBase minusBase hChart couplings faithful input hInput face contract).fderiv

/-- Candidate derivative of one complete face action: the dominated density
integral plus the actual derivatives of its two endpoint joint values. -/
def programPT04T03FaithfulNullFaceActionDerivative
    (face : NullFace) (base : NullPhysical) : NullPhysical →L[Real] Real :=
  (∫ parameter in
      (faithful.realization.geometry.interval face).initialParameter..
      (faithful.realization.geometry.interval face).finalParameter,
    programPT04T03FaithfulNullFaceDensityFDeriv faithful face base parameter) +
  (fderiv Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).initialJointAction)
      base +
    fderiv Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).finalJointAction)
      base)

/-- Dominated face-density differentiation and endpoint differentiability
give the derivative of the complete finite face action. -/
theorem programPT04T03FaithfulNullFaceAction_hasFDerivAt
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (contract : ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful
      face input.2) :
    HasFDerivAt
      (fun state : NullPhysical =>
        finiteNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
      (programPT04T03FaithfulNullFaceActionDerivative faithful face input.2)
      input.2 := by
  have hIntegrated :=
    programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt period hPeriod
      plusBase minusBase hChart couplings faithful input hInput face
        contract.toProgramPT04T03FaithfulNullFaceDominatedFDerivContract
  have hInitial := contract.initialJoint_differentiableAt.hasFDerivAt
  have hFinal := contract.finalJoint_differentiableAt.hasFDerivAt
  have hSum := hIntegrated.add (hInitial.add hFinal)
  exact (hSum.congr_fderiv rfl).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Exact facewise `fderiv` formula produced by the dominated contract. -/
theorem programPT04T03FaithfulNullFaceAction_fderiv_eq
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (face : NullFace)
    (contract : ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful
      face input.2) :
    fderiv Real
        (fun state : NullPhysical =>
          finiteNullFaceAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face))
        input.2 =
      programPT04T03FaithfulNullFaceActionDerivative faithful face input.2 :=
  (programPT04T03FaithfulNullFaceAction_hasFDerivAt period hPeriod plusBase
    minusBase hChart couplings faithful input hInput face contract).fderiv

/-- The finite face sum differentiates term by term once every face carries
the honest dominated and endpoint contract. -/
theorem programPT04T03FaithfulNullTotalAction_hasFDerivAt_sum
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (contracts : ∀ face : NullFace,
      ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face input.2) :
    HasFDerivAt
      (finiteNullFaceMobileGeometricTotalAction faithful.realization.geometry)
      (∑ face : NullFace,
        programPT04T03FaithfulNullFaceActionDerivative faithful face input.2)
      input.2 := by
  change HasFDerivAt
    (fun state : NullPhysical =>
      ∑ face : NullFace,
        finiteNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
    _ input.2
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun face _ =>
    programPT04T03FaithfulNullFaceAction_hasFDerivAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput face (contracts face)

/-- The `fderiv` of the total action is the finite sum of the dominated
facewise derivatives. -/
theorem programPT04T03FaithfulNullTotalAction_fderiv_eq_sum
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (contracts : ∀ face : NullFace,
      ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face input.2) :
    fderiv Real
        (finiteNullFaceMobileGeometricTotalAction faithful.realization.geometry)
        input.2 =
      ∑ face : NullFace,
        programPT04T03FaithfulNullFaceActionDerivative faithful face input.2 :=
  (programPT04T03FaithfulNullTotalAction_hasFDerivAt_sum period hPeriod
    plusBase minusBase hChart couplings faithful input hInput contracts).fderiv

/-- Gate 838's genuine total-action jet now has a facewise dominated-integral
description of its first derivative slot. -/
theorem programPT04T03FaithfulNullTotalActionJet_firstDerivative_eq_faceSum
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (contracts : ∀ face : NullFace,
      ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face input.2) :
    (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput).firstDerivative =
      ∑ face : NullFace,
        programPT04T03FaithfulNullFaceActionDerivative faithful face input.2 := by
  calc
    (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
      minusBase hChart couplings faithful input hInput).firstDerivative =
        fderiv Real
          (finiteNullFaceMobileGeometricTotalAction
            faithful.realization.geometry) input.2 := rfl
    _ = ∑ face : NullFace,
          programPT04T03FaithfulNullFaceActionDerivative faithful face input.2 :=
      programPT04T03FaithfulNullTotalAction_fderiv_eq_sum period hPeriod
        plusBase minusBase hChart couplings faithful input hInput contracts

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

/-- The T03 position Riesz pairing is the sum of the dominated facewise
integral-plus-joint derivatives. -/
theorem programPT04T03FaithfulNullPositionRieszPairing_eq_faceSum
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (contracts : ∀ face : NullFace,
      ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face input.2)
    (direction : NullPosition) :
    inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      ∑ face : NullFace,
        programPT04T03FaithfulNullFaceActionDerivative faithful face input.2
          (direction, 0) := by
  calc
    inner Real
        (programPT04T03NullPositionRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
        minusBase hChart couplings faithful input hInput).firstDerivative
          (direction, 0) :=
      programPT04T03FaithfulNullPositionRieszPairing_eq_totalActionJet period
        hPeriod plusBase minusBase hChart couplings faithful data einsteinScale
          interactionScale coefficients input hInput direction
    _ = (∑ face : NullFace,
          programPT04T03FaithfulNullFaceActionDerivative faithful face input.2)
          (direction, 0) := by
      rw [programPT04T03FaithfulNullTotalActionJet_firstDerivative_eq_faceSum
        period hPeriod plusBase minusBase hChart couplings faithful input hInput
          contracts]
    _ = ∑ face : NullFace,
          programPT04T03FaithfulNullFaceActionDerivative faithful face input.2
            (direction, 0) := by
      simp

/-- The intrinsic-screen Riesz pairing has the analogous facewise formula. -/
theorem programPT04T03FaithfulNullIntrinsicRieszPairing_eq_faceSum
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
        period hPeriod plusBase minusBase hChart couplings Model)
    (contracts : ∀ face : NullFace,
      ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face input.2)
    (direction : NullIntrinsic) :
    inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      ∑ face : NullFace,
        programPT04T03FaithfulNullFaceActionDerivative faithful face input.2
          (0, direction) := by
  calc
    inner Real
        (programPT04T03NullIntrinsicRieszResidualAt period hPeriod plusBase
          minusBase hChart couplings data Model einsteinScale interactionScale
            coefficients input) direction =
      (programPT04T03FaithfulNullTotalActionSecondJetAt period hPeriod plusBase
        minusBase hChart couplings faithful input hInput).firstDerivative
          (0, direction) :=
      programPT04T03FaithfulNullIntrinsicRieszPairing_eq_totalActionJet period
        hPeriod plusBase minusBase hChart couplings faithful data einsteinScale
          interactionScale coefficients input hInput direction
    _ = (∑ face : NullFace,
          programPT04T03FaithfulNullFaceActionDerivative faithful face input.2)
          (0, direction) := by
      rw [programPT04T03FaithfulNullTotalActionJet_firstDerivative_eq_faceSum
        period hPeriod plusBase minusBase hChart couplings faithful input hInput
          contracts]
    _ = ∑ face : NullFace,
          programPT04T03FaithfulNullFaceActionDerivative faithful face input.2
            (0, direction) := by
      simp

end

end
end P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D
end JanusFormal
