import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D

/-!
# Geometric null-reparametrization integration naturality

This module reparametrizes the actual null-face and endpoint densities of the
geometric packet from Gate 830.  Gate 833 integration preserves the combined
null/joint action, and its joint change is the Gate-834 horizontal image of
the integrated null transgression.

Only the realized null-to-joint incidence is used.  No full geometric `dH` or
contact differential is defined here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05GeometricNullReparametrizationIntegrationNaturality4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The two actual endpoint values after the finite null-generator
reparametrization. -/
def programPT05ReparametrizedJointDensity
    (face : FiniteNullFaceActionDatum) :
    ProgramPT05NullJointEndpoint → Real
  | .initial =>
      face.initialJointAction +
        nullFaceCoefficient face *
          endpointPrimitive face.generator face.interval.initialParameter
  | .final =>
      face.finalJointAction -
        nullFaceCoefficient face *
          endpointPrimitive face.generator face.interval.finalParameter

@[simp]
theorem programPT05ReparametrizedJointDensity_sum
    (face : FiniteNullFaceActionDatum) :
    programPT05ReparametrizedJointDensity face .initial +
        programPT05ReparametrizedJointDensity face .final =
      reparametrizedEndpointJointAction face := by
  rfl

/-- The Gate-830 packet with its null density and joints replaced by their
actual finite-reparametrized values. -/
def programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
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
  nullBoundaryDensity := fun face parameter ↦
    reparametrizedNullFaceDensity
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
      parameter
  jointDensity := fun face ↦
    programPT05ReparametrizedJointDensity
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)

@[simp]
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_nullBoundary
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .nullBoundary =
      (∑ face : NullFace,
        integratedReparametrizedNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face),
        0) := by
  rfl

@[simp]
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_joint
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .joint =
      (∑ face : NullFace,
        reparametrizedEndpointJointAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face),
        0) := by
  rfl

/-- The two reparametrized geometric slots integrate to the finite sum of the
actual reparametrized face-plus-joint actions. -/
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_null_add_joint_eq_sum
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .nullBoundary).1 +
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .joint).1 =
      ∑ face : NullFace, reparametrizedFiniteNullFaceAction
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input face) := by
  rw [programPT05ReparametrizedGeometricDensityIntegrationMap_nullBoundary,
    programPT05ReparametrizedGeometricDensityIntegrationMap_joint]
  rw [← Finset.sum_add_distrib]
  rfl

/-- Finite reparametrization leaves the combined integrated null/joint part of
the actual geometric packet unchanged. -/
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_null_add_joint_invariant
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .nullBoundary).1 +
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .joint).1 =
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .nullBoundary).1 +
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .joint).1 := by
  rw [programPT05ReparametrizedGeometricDensityIntegrationMap_null_add_joint_eq_sum,
    programPT05GeometricDensityIntegrationMapOfPackets_null_add_joint_eq_totalAction]
  unfold totalFiniteNullBoundaryAction
  apply Finset.sum_congr rfl
  intro face _
  exact reparametrizedFiniteNullFaceAction_eq
    (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
    (faithful.realization.intervalIntegrability input hInput face)

/-- The scalar change of the integrated null slot is exactly the scalar
coefficient of Gate 834's finite-family source cochain. -/
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_null_difference_eq_source
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .nullBoundary).1 -
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .nullBoundary).1 =
      (programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
        faithful input .nullBoundary).1 := by
  change
    (∑ face : NullFace,
        integratedReparametrizedNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)) -
      (∑ face : NullFace,
        integratedNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)) =
      ∑ face : NullFace,
        programPT05NullBoundaryDensityIntegral
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
          (programPT05CanonicalNullJointLocalDensityCochain
            (faithful.realization.geometry.toFiniteNullFaceActionDatum input face))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro face _
  rw [integratedReparametrizedNullFaceAction_eq
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
      (faithful.realization.intervalIntegrability input hInput face),
    programPT05CanonicalNullBoundaryDensityIntegral_eq_endpoint
      (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
      (faithful.realization.intervalIntegrability input hInput face)]
  ring

/-- The change of the integrated joint slot is the finite-family target
cochain from Gate 834. -/
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_joint_difference_eq_target
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .joint).1 -
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .joint).1 =
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input .joint).1 := by
  change
    (∑ face : NullFace,
        reparametrizedEndpointJointAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)) -
      (∑ face : NullFace,
        endpointJointAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)) =
      ∑ face : NullFace,
        programPT05JointDensityEvaluation
          (programPT05CanonicalNullJointLocalDensityCochain
            (faithful.realization.geometry.toFiniteNullFaceActionDatum input face))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro face _
  exact (programPT05CanonicalJointDensityEvaluation_eq_action_change
    (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)).symm

/-- The geometric joint change is therefore the actual Gate-819 horizontal
image of the integrated geometric null transgression. -/
theorem programPT05ReparametrizedGeometricDensityIntegrationMap_joint_difference_eq_dH
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    ((programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
          period hPeriod couplings bulk ghy faithful input) .joint).1 -
      (programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
          couplings bulk ghy faithful input) .joint).1, 0) =
      (programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
          faithful input)) .joint := by
  rw [programPT05T03FaithfulNullTransgressionIntegration_commutes_dH
    faithful input hInput]
  apply Prod.ext
  · exact programPT05ReparametrizedGeometricDensityIntegrationMap_joint_difference_eq_target
      period hPeriod couplings bulk ghy faithful input
  · rfl

end
end P0EFTJanusProgramPT05GeometricNullReparametrizationIntegrationNaturality4D
end JanusFormal
