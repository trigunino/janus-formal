import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D

/-!
# Finite-null horizontal integration morphism

Gate 823 identifies the horizontal incidence for one null face at the joint
component.  This module sums the genuine local transgression over every face,
upgrades that component statement to equality of the full relative cochains,
and specializes it to the faithful mobile null geometry used by T03.

This is the null-to-joint horizontal edge only.  It does not define the full
geometric `dH`, the contact differential `dV`, or a terminal T05 certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D

variable {NullFace : Type*} [Fintype NullFace]

/-- Sum of the integrated normalization-transgression densities, supported on
the null-boundary stratum. -/
def programPT05FiniteNullTransgressionSourceIntegratedCochain
    (faces : NullFace → FiniteNullFaceActionDatum) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary =>
      (∑ face : NullFace,
        programPT05NullBoundaryDensityIntegral (faces face)
          (programPT05CanonicalNullJointLocalDensityCochain (faces face)), 0)
  | .joint => 0

/-- Sum of the corresponding oriented endpoint densities, supported on the
joint stratum. -/
def programPT05FiniteNullTransgressionTargetIntegratedCochain
    (faces : NullFace → FiniteNullFaceActionDatum) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint =>
      (∑ face : NullFace,
        programPT05JointDensityEvaluation
          (programPT05CanonicalNullJointLocalDensityCochain (faces face)), 0)

/-- The finite sum of the local FTOC identities evaluates the source on the
oriented endpoint primitives. -/
theorem programPT05FiniteNullTransgressionSource_eq_endpointSum
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    (programPT05FiniteNullTransgressionSourceIntegratedCochain faces
        .nullBoundary).1 =
      ∑ face : NullFace,
        nullFaceCoefficient (faces face) *
          (endpointPrimitive (faces face).generator
              (faces face).interval.finalParameter -
            endpointPrimitive (faces face).generator
              (faces face).interval.initialParameter) := by
  apply Finset.sum_congr rfl
  intro face _
  exact programPT05CanonicalNullBoundaryDensityIntegral_eq_endpoint
    (faces face) (contracts face)

/-- The target is the finite sum of the actual endpoint-joint action changes. -/
theorem programPT05FiniteNullTransgressionTarget_eq_jointActionChanges
    (faces : NullFace → FiniteNullFaceActionDatum) :
    (programPT05FiniteNullTransgressionTargetIntegratedCochain faces .joint).1 =
      ∑ face : NullFace,
        (reparametrizedEndpointJointAction (faces face) -
          endpointJointAction (faces face)) := by
  apply Finset.sum_congr rfl
  intro face _
  exact programPT05CanonicalJointDensityEvaluation_eq_action_change
    (faces face)

/-- The actual finite-family integration commutes with the null-to-joint edge
of Gate 819's horizontal differential, as an equality of whole cochains. -/
theorem programPT05FiniteNullTransgressionIntegration_commutes_dH
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05FiniteNullTransgressionSourceIntegratedCochain faces) =
      programPT05FiniteNullTransgressionTargetIntegratedCochain faces := by
  have hStokes :
      (∑ face : NullFace,
          programPT05NullBoundaryDensityIntegral (faces face)
            (programPT05CanonicalNullJointLocalDensityCochain (faces face))) +
        ∑ face : NullFace,
          programPT05JointDensityEvaluation
            (programPT05CanonicalNullJointLocalDensityCochain (faces face)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro face _
    exact programPT05CanonicalNullJointDensity_stokes
      (faces face) (contracts face)
  funext stratum
  cases stratum with
  | bulk => rfl
  | nonNullBoundary => rfl
  | nullBoundary => rfl
  | joint =>
      apply Prod.ext
      · change
          0 -
              (∑ face : NullFace,
                programPT05NullBoundaryDensityIntegral (faces face)
                  (programPT05CanonicalNullJointLocalDensityCochain
                    (faces face))) =
            ∑ face : NullFace,
              programPT05JointDensityEvaluation
                (programPT05CanonicalNullJointLocalDensityCochain
                  (faces face))
        linarith
      · simp [programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          programPT05FiniteNullTransgressionSourceIntegratedCochain,
          programPT05FiniteNullTransgressionTargetIntegratedCochain]

/-- Source cochain for the actual faithful T03 mobile null geometry. -/
def programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0 :=
  programPT05FiniteNullTransgressionSourceIntegratedCochain
    (fun face =>
      faithful.realization.geometry.toFiniteNullFaceActionDatum input face)

/-- Target joint cochain for the same faithful T03 mobile null geometry. -/
def programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 :=
  programPT05FiniteNullTransgressionTargetIntegratedCochain
    (fun face =>
      faithful.realization.geometry.toFiniteNullFaceActionDatum input face)

/-- On every admissible faithful T03 null input, geometric integration
commutes with the complete finite null-to-joint horizontal incidence. -/
theorem programPT05T03FaithfulNullTransgressionIntegration_commutes_dH
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
          faithful input) =
      programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input := by
  exact programPT05FiniteNullTransgressionIntegration_commutes_dH
    (faces := fun face =>
      faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
    (contracts := faithful.realization.intervalIntegrability input hInput)

end
end P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
end JanusFormal
