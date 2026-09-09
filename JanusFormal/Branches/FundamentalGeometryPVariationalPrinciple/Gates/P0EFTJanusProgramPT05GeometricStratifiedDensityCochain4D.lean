import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D

/-!
# T05 geometric stratified density cochain

This module replaces the uniform integrated coefficient used by Gate 819 with
a packet whose fields live on their actual geometric strata: the effective
four-dimensional quotient, the effective throat, the non-null cut boundary,
each null-face interval and each endpoint joint.  Sectorwise integration uses
the exact bulk, LL, GHY and faithful-null evaluations already proved.

The primitive SpinC graph state has no continuous spacetime density in the
current API.  It is retained as an explicitly separate frontier field.  No
horizontal or vertical differential, incidence map, jet prolongation or
bicomplex law is introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Interval
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D
open P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance stratifiedEffectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance stratifiedEffectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance stratifiedCanonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The two zero-dimensional endpoints of an oriented null face. -/
inductive ProgramPT05NullJointEndpoint
  | initial
  | final
  deriving DecidableEq

/-- A genuinely stratified local-density packet.  Every density is carried by
its own geometric space; the SpinC graph frontier is explicitly not presented
as a spacetime density. -/
structure ProgramPT05GeometricStratifiedDensityCochain
    (period : Real) (hPeriod : period ≠ 0)
    (couplings : GlobalCandidateAActionCouplings)
    (NullFace : Type*) where
  bulkDensity : C(EffectiveQuotient period hPeriod, Real)
  spinCFrontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
    couplings.matterMassSquared
  llDensity : C(EffectiveThroat period hPeriod, Real)
  nonNullBoundaryDensity : CandidateANormalBoundaryScalarField period hPeriod
  nullFaceInterval : NullFace → OrientedNullInterval
  nullBoundaryDensity : NullFace → Real → Real
  jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Existing joint values of the faithful T03 mobile geometry, indexed by
face and endpoint. -/
def programPT05T03FaithfulJointDensity
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (face : NullFace) : ProgramPT05NullJointEndpoint → Real
  | .initial =>
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).initialJointAction
  | .final =>
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).finalJointAction

/-- Assemble the already constructed bulk/LL, GHY and faithful-null local data
without changing any of their geometric carriers. -/
def programPT05GeometricStratifiedDensityCochainOfPackets
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT05GeometricStratifiedDensityCochain period hPeriod couplings
      NullFace where
  bulkDensity := programPT05BulkSpacetimeDensity period hPeriod couplings bulk
  spinCFrontier := bulk.spinCFrontier
  llDensity := bulk.llDensity.llDensity
  nonNullBoundaryDensity := ghy.nonNullBoundaryDensity
  nullFaceInterval := fun face ↦
    (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).interval
  nullBoundaryDensity :=
    programPT05T03FaithfulNullFaceLocalDensityFamily faithful input
  jointDensity := programPT05T03FaithfulJointDensity faithful input

/-- Canonical spacetime integration of the actual bulk density. -/
def programPT05GeometricBulkDensityIntegral
    (density : C(EffectiveQuotient period hPeriod, Real)) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod density

/-- Canonical throat integration of the LL density. -/
def programPT05GeometricLLDensityIntegral
    (density : C(EffectiveThroat period hPeriod, Real)) : Real :=
  programPT05LLDensityIntegral period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ⟨density⟩

/-- First-sheet integration of the completed non-null GHY density. -/
def programPT05GeometricGHYDensityIntegral
    (density : CandidateANormalBoundaryScalarField period hPeriod) : Real :=
  programPT05GHYFirstSheetDensityIntegral period hPeriod ⟨density⟩

/-- Sum of the oriented integrals of the local null-face densities. -/
def programPT05GeometricNullBoundaryDensityIntegral
    {NullFace : Type*} [Fintype NullFace]
    (interval : NullFace → OrientedNullInterval)
    (density : NullFace → Real → Real) : Real :=
  ∑ face : NullFace,
    ∫ parameter in
      (interval face).initialParameter..(interval face).finalParameter,
      density face parameter

/-- Sum of the two zero-dimensional joint densities of every null face. -/
def programPT05GeometricJointDensityIntegral
    {NullFace : Type*} [Fintype NullFace]
    (density : NullFace → ProgramPT05NullJointEndpoint → Real) : Real :=
  ∑ face : NullFace, (density face .initial + density face .final)

/-- Values obtained by integrating each geometric stratum separately. -/
structure ProgramPT05GeometricStratifiedIntegratedAction where
  bulkDensityAction : Real
  spinCFrontierAction : Real
  llAction : Real
  nonNullBoundaryAction : Real
  nullBoundaryAction : Real
  jointAction : Real

/-- Sectorwise integration of the typed stratified packet. -/
def programPT05IntegrateGeometricStratifiedDensityCochain
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) : ProgramPT05GeometricStratifiedIntegratedAction where
  bulkDensityAction :=
    programPT05GeometricBulkDensityIntegral period hPeriod density.bulkDensity
  spinCFrontierAction :=
    programPT05BulkSpinCFrontierAction period hPeriod couplings
      density.spinCFrontier
  llAction :=
    programPT05GeometricLLDensityIntegral period hPeriod density.llDensity
  nonNullBoundaryAction :=
    programPT05GeometricGHYDensityIntegral period hPeriod
      density.nonNullBoundaryDensity
  nullBoundaryAction :=
    programPT05GeometricNullBoundaryDensityIntegral density.nullFaceInterval
      density.nullBoundaryDensity
  jointAction := programPT05GeometricJointDensityIntegral density.jointDensity

/-- The assembled packet preserves Gate 828's exact bulk/SpinC/LL evaluation. -/
theorem programPT05GeometricBulkSpinCLLIntegral_eq_evaluation
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings) :
    (programPT05GeometricBulkDensityIntegral period hPeriod
        (programPT05BulkSpacetimeDensity period hPeriod couplings bulk) +
      programPT05BulkSpinCFrontierAction period hPeriod couplings
        bulk.spinCFrontier) +
      programPT05GeometricLLDensityIntegral period hPeriod
        bulk.llDensity.llDensity =
    programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
      bulk := by
  rfl

/-- On canonical data, sectorwise bulk, SpinC-frontier and LL evaluation is
exactly the existing pre-boundary T03 action. -/
theorem programPT05CanonicalGeometricBulkSpinCLLIntegral_eq_action
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
      period hPeriod geometry frame couplings) :
    let bulk :=
      programPT05CanonicalBulkActionLocalDensityPacket period hPeriod geometry
        frame hRegular couplings interactionScale coefficients input
    (programPT05GeometricBulkDensityIntegral period hPeriod
        (programPT05BulkSpacetimeDensity period hPeriod couplings bulk) +
      programPT05BulkSpinCFrontierAction period hPeriod couplings
        bulk.spinCFrontier) +
      programPT05GeometricLLDensityIntegral period hPeriod
        bulk.llDensity.llDensity =
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
      geometry frame hRegular couplings interactionScale coefficients input := by
  dsimp only
  rw [programPT05GeometricBulkSpinCLLIntegral_eq_evaluation]
  exact programPT05CanonicalBulkActionLocalDensityEvaluation_eq_action
    period hPeriod geometry frame hRegular couplings interactionScale
      coefficients input

/-- The LL field projection integrates to its exact existing PT action. -/
theorem programPT05CanonicalGeometricLLDensityIntegral_eq_action
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (packet : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame) :
    programPT05GeometricLLDensityIntegral period hPeriod
        (programPT05CanonicalPTLLLocalDensityCochain period hPeriod frame packet).llDensity =
      regularGeneralMetricC0LLPTAction period hPeriod frame
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) packet := by
  exact programPT05CanonicalPTLLDensityIntegral_eq_action period hPeriod frame
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) packet

/-- The non-null field projection integrates to the exact completed GHY
first-sheet action. -/
theorem programPT05CanonicalGeometricGHYDensityIntegral_eq_action
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real) :
    programPT05GeometricGHYDensityIntegral period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current).nonNullBoundaryDensity =
      candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current := by
  exact programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action
    period hPeriod einsteinScale metric current

/-- The null-face field projection is the existing faithful raw density
aggregate at one physical coordinate. -/
theorem programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).interval)
        (programPT05T03FaithfulNullFaceLocalDensityFamily faithful input) =
      programPT05RealizedNullFaceDensityIntegral
        faithful.toPhysicalActionRealization input := by
  rfl

/-- The joint field projection is the existing faithful raw endpoint
aggregate at the same physical coordinate. -/
theorem programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricJointDensityIntegral
        (programPT05T03FaithfulJointDensity faithful input) =
      programPT05RealizedEndpointJointActionAggregate
        faithful.toPhysicalActionRealization input := by
  simp [programPT05GeometricJointDensityIntegral,
    programPT05T03FaithfulJointDensity,
    programPT05RealizedEndpointJointActionAggregate,
    programPT05EndpointJointActionAggregate, endpointJointAction,
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization,
    FiniteNullFaceMobileGeometricActionRealization.toPhysicalActionRealization]

/-- Zero-normalized null-face and joint sector integration. -/
def programPT05T03FaithfulRelativeNullAndJointDensityIntegral
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  (programPT05GeometricNullBoundaryDensityIntegral
      (fun face ↦
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).interval)
      (programPT05T03FaithfulNullFaceLocalDensityFamily faithful input) -
    programPT05GeometricNullBoundaryDensityIntegral
      (fun face ↦
        (faithful.realization.geometry.toFiniteNullFaceActionDatum 0 face).interval)
      (programPT05T03FaithfulNullFaceLocalDensityFamily faithful 0)) +
  (programPT05GeometricJointDensityIntegral
      (programPT05T03FaithfulJointDensity faithful input) -
    programPT05GeometricJointDensityIntegral
      (programPT05T03FaithfulJointDensity faithful 0))

/-- The normalized local null and joint strata recover the exact physical null
action model selected by T03. -/
theorem programPT05T03FaithfulRelativeNullAndJointDensityIntegral_eq_action
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulRelativeNullAndJointDensityIntegral faithful input =
      faithful.toPhysicalActionRealization.toActionModel.action input := by
  unfold programPT05T03FaithfulRelativeNullAndJointDensityIntegral
  rw [programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw faithful input,
    programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw faithful 0,
    programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw faithful input,
    programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw faithful 0]
  simpa [programPT05T03FaithfulNullFaceDensityContribution,
    programPT05T03FaithfulEndpointJointContribution,
    programPT05RealizedRelativeNullFaceDensityIntegral,
    programPT05RealizedRelativeEndpointJointActionAggregate] using
      (programPT05T03FaithfulNullAction_eq_density_add_joint
        faithful input).symm

/-- The same normalized local sectors recover the existing mobile geometric
relative action. -/
theorem programPT05T03FaithfulRelativeNullAndJointDensityIntegral_eq_geometricAction
    {NullFace : Type*} [Fintype NullFace]
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulRelativeNullAndJointDensityIntegral faithful input =
      finiteNullFaceMobileGeometricRelativeAction faithful.realization input := by
  unfold programPT05T03FaithfulRelativeNullAndJointDensityIntegral
  rw [programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw faithful input,
    programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw faithful 0,
    programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw faithful input,
    programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw faithful 0]
  simpa [programPT05T03FaithfulNullFaceDensityContribution,
    programPT05T03FaithfulEndpointJointContribution,
    programPT05RealizedRelativeNullFaceDensityIntegral,
    programPT05RealizedRelativeEndpointJointActionAggregate] using
      (programPT05T03FaithfulDensity_add_joint_eq_geometricAction
        faithful input)

end
end P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
end JanusFormal
