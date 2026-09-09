import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D

/-!
# T05 integration of geometric densities into the relative cochain

This module integrates the genuinely stratified density packet of Gate 830
into the four physical slots of Gate 819.  The bulk slot contains the
spacetime integral, the existing SpinC graph-frontier action and the LL throat
integral.  The other slots contain the GHY, null-face and joint integrals.

Because the SpinC frontier is not a local density with an available additive
carrier, this construction is a function named `integrationMap`, not a linear
map.  No commutation with either relative differential is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D
open P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

/-- Functional integration of a stratified density packet into the four
physical slots of the integrated relative cochain. -/
def programPT05GeometricDensityIntegrationMap
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 :=
  let integrated :=
    programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
      couplings density
  fun
  | .bulk =>
      ((integrated.bulkDensityAction + integrated.spinCFrontierAction) +
        integrated.llAction, 0)
  | .nonNullBoundary => (integrated.nonNullBoundaryAction, 0)
  | .nullBoundary => (integrated.nullBoundaryAction, 0)
  | .joint => (integrated.jointAction, 0)

@[simp]
theorem programPT05GeometricDensityIntegrationMap_bulk
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings density
        .bulk =
      (((programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
            couplings density).bulkDensityAction +
          (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
            couplings density).spinCFrontierAction) +
        (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
          couplings density).llAction, 0) := by
  rfl

@[simp]
theorem programPT05GeometricDensityIntegrationMap_nonNullBoundary
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings density
        .nonNullBoundary =
      ((programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings density).nonNullBoundaryAction, 0) := by
  rfl

@[simp]
theorem programPT05GeometricDensityIntegrationMap_nullBoundary
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings density
        .nullBoundary =
      ((programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings density).nullBoundaryAction, 0) := by
  rfl

@[simp]
theorem programPT05GeometricDensityIntegrationMap_joint
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings density
        .joint =
      ((programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings density).jointAction, 0) := by
  rfl

/-- On assembled packets, the bulk slot is exactly Gate 828's mixed
spacetime/SpinC/LL evaluation. -/
theorem programPT05GeometricDensityIntegrationMapOfPackets_bulk_eq_evaluation
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .bulk =
      (programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
        bulk, 0) := by
  change
    ((programPT05GeometricBulkDensityIntegral period hPeriod
        (programPT05BulkSpacetimeDensity period hPeriod couplings bulk) +
        programPT05BulkSpinCFrontierAction period hPeriod couplings
          bulk.spinCFrontier) +
      programPT05GeometricLLDensityIntegral period hPeriod
        bulk.llDensity.llDensity, 0) = _
  rw [programPT05GeometricBulkSpinCLLIntegral_eq_evaluation]

/-- A canonical Gate 828 packet gives the exact pre-boundary T03 action in
the bulk slot. -/
theorem programPT05CanonicalGeometricDensityIntegrationMap_bulk_eq_action
    {NullFace : Type*} [Fintype NullFace]
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (bulkInput : FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
      period hPeriod geometry frame couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (nullInput : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings
          (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
            geometry frame hRegular couplings interactionScale coefficients
              bulkInput)
          ghy faithful nullInput) .bulk =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
        geometry frame hRegular couplings interactionScale coefficients
          bulkInput, 0) := by
  rw [programPT05GeometricDensityIntegrationMapOfPackets_bulk_eq_evaluation,
    programPT05CanonicalBulkActionLocalDensityEvaluation_eq_action]

/-- On assembled packets, the non-null slot is the exact Gate 824 GHY
integral. -/
theorem programPT05GeometricDensityIntegrationMapOfPackets_nonNull_eq_integral
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .nonNullBoundary =
      (programPT05GHYFirstSheetDensityIntegral period hPeriod ghy, 0) := by
  rfl

/-- A canonical Gate 824 density gives the exact completed GHY action in the
non-null slot. -/
theorem programPT05CanonicalGeometricDensityIntegrationMap_nonNull_eq_action
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghyInput : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (nullInput : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale metric ghyInput)
          faithful nullInput) .nonNullBoundary =
      (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation period
        hPeriod einsteinScale metric ghyInput, 0) := by
  rw [programPT05GeometricDensityIntegrationMapOfPackets_nonNull_eq_integral,
    programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action]

/-- On faithful T03 data, the null slot is the actual raw face-density
aggregate. -/
theorem programPT05GeometricDensityIntegrationMapOfPackets_null_eq_raw
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .nullBoundary =
      (programPT05RealizedNullFaceDensityIntegral
        faithful.toPhysicalActionRealization input, 0) := by
  change
    (programPT05GeometricNullBoundaryDensityIntegral
      (fun face ↦
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input face).interval)
      (programPT05T03FaithfulNullFaceLocalDensityFamily faithful input), 0) = _
  rw [programPT05T03FaithfulGeometricNullDensityIntegral_eq_raw]

/-- On faithful T03 data, the joint slot is the actual raw endpoint
aggregate. -/
theorem programPT05GeometricDensityIntegrationMapOfPackets_joint_eq_raw
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .joint =
      (programPT05RealizedEndpointJointActionAggregate
        faithful.toPhysicalActionRealization input, 0) := by
  change
    (programPT05GeometricJointDensityIntegral
      (programPT05T03FaithfulJointDensity faithful input), 0) = _
  rw [programPT05T03FaithfulGeometricJointDensityIntegral_eq_raw]

/-- The raw null and joint slots recover the existing unnormalized finite
null-boundary action. -/
theorem programPT05GeometricDensityIntegrationMapOfPackets_null_add_joint_eq_totalAction
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .nullBoundary).1 +
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .joint).1 =
      totalFiniteNullBoundaryAction
        (faithful.toPhysicalActionRealization.toDatum input) := by
  rw [programPT05GeometricDensityIntegrationMapOfPackets_null_eq_raw,
    programPT05GeometricDensityIntegrationMapOfPackets_joint_eq_raw]
  unfold programPT05RealizedNullFaceDensityIntegral
    programPT05RealizedEndpointJointActionAggregate
  exact programPT05CanonicalNullFaceDensity_add_joint_eq_totalAction
    (faithful.toPhysicalActionRealization.toDatum input)

/-- T03 specialization: bulk and GHY use the raw integrated packet, while the
null and joint slots use Gate 829's zero-normalized density integrals. -/
def programPT05T03FaithfulGeometricDensityIntegrationMap
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 :=
  let integrated :=
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
      (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
        couplings bulk ghy faithful input)
  fun
  | .bulk => integrated .bulk
  | .nonNullBoundary => integrated .nonNullBoundary
  | .nullBoundary =>
      (programPT05T03FaithfulNullFaceDensityContribution faithful input, 0)
  | .joint =>
      (programPT05T03FaithfulEndpointJointContribution faithful input, 0)

@[simp]
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_bulk
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .bulk =
      (programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
        bulk, 0) := by
  exact programPT05GeometricDensityIntegrationMapOfPackets_bulk_eq_evaluation
    period hPeriod couplings bulk ghy faithful input

@[simp]
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_nonNullBoundary
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .nonNullBoundary =
      (programPT05GHYFirstSheetDensityIntegral period hPeriod ghy, 0) := by
  exact programPT05GeometricDensityIntegrationMapOfPackets_nonNull_eq_integral
    period hPeriod couplings bulk ghy faithful input

@[simp]
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_nullBoundary
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .nullBoundary =
      (programPT05T03FaithfulNullFaceDensityContribution faithful input, 0) := by
  rfl

@[simp]
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_joint
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .joint =
      (programPT05T03FaithfulEndpointJointContribution faithful input, 0) := by
  rfl

/-- The faithful null and joint components recover the exact T03 physical
null action. -/
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_null_add_joint_eq_action
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .nullBoundary).1 +
      (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .joint).1 =
      faithful.toPhysicalActionRealization.toActionModel.action input := by
  change
    programPT05T03FaithfulNullFaceDensityContribution faithful input +
        programPT05T03FaithfulEndpointJointContribution faithful input = _
  exact (programPT05T03FaithfulNullAction_eq_density_add_joint
    faithful input).symm

/-- The same faithful components recover the existing mobile geometric null
action. -/
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_null_add_joint_eq_geometricAction
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .nullBoundary).1 +
      (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input .joint).1 =
      finiteNullFaceMobileGeometricRelativeAction faithful.realization input := by
  change
    programPT05T03FaithfulNullFaceDensityContribution faithful input +
        programPT05T03FaithfulEndpointJointContribution faithful input = _
  exact programPT05T03FaithfulDensity_add_joint_eq_geometricAction
    faithful input

/-- Sum of the four scalar coefficients of an integrated relative cochain. -/
def programPT05IntegratedRelativeCochainActionSum
    (cochain : RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0) : Real :=
  ((cochain .bulk).1 + (cochain .nonNullBoundary).1) +
    ((cochain .nullBoundary).1 + (cochain .joint).1)

/-- The faithful integrated cochain sums exactly to the three existing sector
actions: bulk/SpinC/LL, GHY and normalized physical null. -/
theorem programPT05T03FaithfulGeometricDensityIntegrationMap_sum_eq_sectorActions
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05IntegratedRelativeCochainActionSum
        (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
          couplings bulk ghy faithful input) =
      (programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
          bulk +
        programPT05GHYFirstSheetDensityIntegral period hPeriod ghy) +
      faithful.toPhysicalActionRealization.toActionModel.action input := by
  unfold programPT05IntegratedRelativeCochainActionSum
  rw [programPT05T03FaithfulGeometricDensityIntegrationMap_bulk,
    programPT05T03FaithfulGeometricDensityIntegrationMap_nonNullBoundary,
    programPT05T03FaithfulGeometricDensityIntegrationMap_nullBoundary,
    programPT05T03FaithfulGeometricDensityIntegrationMap_joint,
    programPT05T03FaithfulNullAction_eq_density_add_joint]

/-- With canonical bulk and GHY packets, the four cochain slots sum to the
exact pre-boundary action, completed GHY action and faithful T03 null action. -/
theorem programPT05CanonicalFaithfulGeometricDensityIntegrationMap_sum_eq_actions
    {NullFace : Type*} [Fintype NullFace]
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (bulkInput : FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
      period hPeriod geometry frame couplings)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghyInput : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (nullInput : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05IntegratedRelativeCochainActionSum
        (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
          couplings
          (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
            geometry frame hRegular couplings interactionScale coefficients
              bulkInput)
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale metric ghyInput)
          faithful nullInput) =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
            bulkInput +
        candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation period
          hPeriod einsteinScale metric ghyInput) +
      faithful.toPhysicalActionRealization.toActionModel.action nullInput := by
  rw [programPT05T03FaithfulGeometricDensityIntegrationMap_sum_eq_sectorActions,
    programPT05CanonicalBulkActionLocalDensityEvaluation_eq_action,
    programPT05CanonicalGHYFirstSheetDensityIntegral_eq_action]

end
end P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
end JanusFormal
