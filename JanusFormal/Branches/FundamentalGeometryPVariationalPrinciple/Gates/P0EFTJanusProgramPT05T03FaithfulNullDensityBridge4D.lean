import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D

/-!
# T05 faithful T03 null-density bridge

This module specializes the finite null-face density aggregate to the canonical
faithful mobile realization used by the T03 terminal theorem.  The normalized
face-density contribution and its endpoint joints recover both that exact
physical null action model and the existing mobile geometric relative action.
The face-density contribution is recorded in Gate 819's `nullBoundary` slot.

No horizontal or vertical differential, local jet variation, or new
faithfulness contract is introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D

variable {NullFace : Type*} [Fintype NullFace]

/-- Canonical local null-face densities obtained from the faithful mobile
geometry at one T03 physical null coordinate. -/
def programPT05T03FaithfulNullFaceLocalDensityFamily
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT05NullFaceLocalDensityFamily NullFace :=
  programPT05CanonicalNullFaceLocalDensityFamily
    (fun face =>
      faithful.realization.geometry.toFiniteNullFaceActionDatum input face)

@[simp]
theorem programPT05T03FaithfulNullFaceLocalDensityFamily_apply
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (face : NullFace) (parameter : Real) :
    programPT05T03FaithfulNullFaceLocalDensityFamily faithful input face
        parameter =
      nullFaceDensity
        (faithful.realization.geometry.toFiniteNullFaceActionDatum input face)
        parameter := by
  rfl

/-- Zero-normalized aggregate of the canonical face-density integrals. -/
def programPT05T03FaithfulNullFaceDensityContribution
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05RealizedRelativeNullFaceDensityIntegral
    faithful.toPhysicalActionRealization input

/-- Zero-normalized aggregate of the canonical endpoint-joint actions. -/
def programPT05T03FaithfulEndpointJointContribution
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05RealizedRelativeEndpointJointActionAggregate
    faithful.toPhysicalActionRealization input

/-- The density contribution is the difference of the actual finite sums of
oriented local face-density integrals at the input and at zero. -/
theorem programPT05T03FaithfulNullFaceDensityContribution_eq_integrals
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulNullFaceDensityContribution faithful input =
      programPT05NullFaceLocalDensityIntegral
          (fun face =>
            faithful.realization.geometry.toFiniteNullFaceActionDatum input
              face)
          (programPT05T03FaithfulNullFaceLocalDensityFamily faithful input) -
        programPT05NullFaceLocalDensityIntegral
          (fun face =>
            faithful.realization.geometry.toFiniteNullFaceActionDatum 0 face)
          (programPT05T03FaithfulNullFaceLocalDensityFamily faithful 0) := by
  rfl

/-- This is exactly the physical null action model selected in T03. -/
theorem programPT05T03FaithfulNullAction_eq_density_add_joint
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    faithful.toPhysicalActionRealization.toActionModel.action input =
      programPT05T03FaithfulNullFaceDensityContribution faithful input +
        programPT05T03FaithfulEndpointJointContribution faithful input := by
  exact programPT05PhysicalNullAction_eq_density_add_joint
    faithful.toPhysicalActionRealization input

/-- The same density-plus-joint aggregate is the existing mobile geometric
relative action. -/
theorem programPT05T03FaithfulDensity_add_joint_eq_geometricAction
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulNullFaceDensityContribution faithful input +
        programPT05T03FaithfulEndpointJointContribution faithful input =
      finiteNullFaceMobileGeometricRelativeAction faithful.realization input := by
  exact
    (programPT05T03FaithfulNullAction_eq_density_add_joint faithful input).symm.trans
      (FiniteNullFaceMobileCanonicalFaithfulActionRealization.action_eq_geometric
        faithful input)

/-- Gate 819 cochain carrying the canonical faithful null-face density
contribution in its `nullBoundary` component. -/
def programPT05T03FaithfulNullDensityIntegratedRelativeCochain
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0 :=
  programPT05PhysicalNullFaceDensityIntegratedRelativeCochain
    faithful.toPhysicalActionRealization input

@[simp]
theorem programPT05T03FaithfulNullDensityIntegratedRelativeCochain_nullBoundary
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05T03FaithfulNullDensityIntegratedRelativeCochain faithful input
        .nullBoundary =
      (programPT05T03FaithfulNullFaceDensityContribution faithful input, 0) := by
  rfl

/-- The faithful `nullBoundary` coefficient and its separately retained joints
recover the exact physical null action used by T03. -/
theorem programPT05T03FaithfulNullBoundaryComponent_add_joint_eq_action
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05T03FaithfulNullDensityIntegratedRelativeCochain faithful input
        .nullBoundary).1 +
        programPT05T03FaithfulEndpointJointContribution faithful input =
      faithful.toPhysicalActionRealization.toActionModel.action input := by
  exact programPT05PhysicalNullBoundaryComponent_add_joint_eq_action
    faithful.toPhysicalActionRealization input

/-- The same Gate 819 component-plus-joints expression evaluates to the mobile
geometric relative action. -/
theorem programPT05T03FaithfulNullBoundaryComponent_add_joint_eq_geometricAction
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05T03FaithfulNullDensityIntegratedRelativeCochain faithful input
        .nullBoundary).1 +
        programPT05T03FaithfulEndpointJointContribution faithful input =
      finiteNullFaceMobileGeometricRelativeAction faithful.realization input := by
  rw [programPT05T03FaithfulNullBoundaryComponent_add_joint_eq_action]
  exact
    FiniteNullFaceMobileCanonicalFaithfulActionRealization.action_eq_geometric
      faithful input

end
end P0EFTJanusProgramPT05T03FaithfulNullDensityBridge4D
end JanusFormal
