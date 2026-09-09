import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFacePhysicalActionRealization4D

/-!
# T05 finite null-face action density aggregate

This module aggregates the existing local null-face densities over every face
of a finite physical realization.  Their interval integrals, together with the
existing endpoint-joint actions, recover the realized physical null action
exactly, including its normalization at the zero physical coordinate.  The
integrated face-density part is placed in the `nullBoundary` slot of Gate 819.

The only available FTOC law for these data concerns the reparametrization
transgression and is already realized by Gate 823.  No bulk primitive, new
Stokes law, local jet variation, or bicomplex morphism is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators Interval
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

/-- A genuine local density on every face of a finite null boundary. -/
abbrev ProgramPT05NullFaceLocalDensityFamily
    (Face : Type*) := Face → Real → Real

/-- The combined inaffinity and expansion-counterterm density already attached
to each supplied finite null face. -/
def programPT05CanonicalNullFaceLocalDensityFamily
    {Face : Type*} (faces : Face → FiniteNullFaceActionDatum) :
    ProgramPT05NullFaceLocalDensityFamily Face :=
  fun face parameter ↦ nullFaceDensity (faces face) parameter

/-- Sum of the oriented interval integrals of a supplied density family. -/
def programPT05NullFaceLocalDensityIntegral
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum)
    (density : ProgramPT05NullFaceLocalDensityFamily Face) : Real :=
  ∑ face : Face,
    ∫ parameter in
      (faces face).interval.initialParameter..
        (faces face).interval.finalParameter,
      density face parameter

/-- Sum of the endpoint-joint actions paired with the same finite faces. -/
def programPT05EndpointJointActionAggregate
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum) : Real :=
  ∑ face : Face, endpointJointAction (faces face)

/-- Integrating the canonical local density family is exactly the sum of the
existing integrated null-face actions. -/
theorem programPT05CanonicalNullFaceLocalDensityIntegral_eq_sum
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum) :
    programPT05NullFaceLocalDensityIntegral faces
        (programPT05CanonicalNullFaceLocalDensityFamily faces) =
      ∑ face : Face, integratedNullFaceAction (faces face) := by
  rfl

/-- The aggregated local face densities and actual endpoint joints recover the
existing total finite null-boundary action. -/
theorem programPT05CanonicalNullFaceDensity_add_joint_eq_totalAction
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum) :
    programPT05NullFaceLocalDensityIntegral faces
        (programPT05CanonicalNullFaceLocalDensityFamily faces) +
        programPT05EndpointJointActionAggregate faces =
      totalFiniteNullBoundaryAction faces := by
  rw [programPT05CanonicalNullFaceLocalDensityIntegral_eq_sum]
  simp [programPT05EndpointJointActionAggregate,
    totalFiniteNullBoundaryAction, finiteNullFaceAction,
    Finset.sum_add_distrib]

/-- The existing per-face integral decomposition also aggregates over every
finite face.  Its hypothesis is precisely the source integrability contract. -/
theorem programPT05TotalFiniteNullBoundaryAction_eq_three_strata
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    totalFiniteNullBoundaryAction faces =
      (∑ face : Face, integratedInaffinityAction (faces face)) +
        (∑ face : Face,
          integratedExpansionCountertermAction (faces face)) +
        programPT05EndpointJointActionAggregate faces := by
  unfold totalFiniteNullBoundaryAction
  calc
    ∑ face : Face, finiteNullFaceAction (faces face) =
        ∑ face : Face,
          (integratedInaffinityAction (faces face) +
            integratedExpansionCountertermAction (faces face) +
            endpointJointAction (faces face)) := by
      apply Finset.sum_congr rfl
      intro face _
      exact integratedNullFaceAction_eq_three_strata
        (faces face) (contracts face)
    _ =
        (∑ face : Face, integratedInaffinityAction (faces face)) +
          (∑ face : Face,
            integratedExpansionCountertermAction (faces face)) +
          programPT05EndpointJointActionAggregate faces := by
      simp [programPT05EndpointJointActionAggregate,
        Finset.sum_add_distrib]

variable {NullFace : Type*} [Fintype NullFace]

/-- Integrated canonical null-face density of a supplied physical realization
at one physical coordinate. -/
def programPT05RealizedNullFaceDensityIntegral
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05NullFaceLocalDensityIntegral (realization.toDatum input)
    (programPT05CanonicalNullFaceLocalDensityFamily
      (realization.toDatum input))

/-- Aggregate endpoint-joint action of the same physical realization. -/
def programPT05RealizedEndpointJointActionAggregate
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05EndpointJointActionAggregate (realization.toDatum input)

/-- Zero-normalized integrated null-face density contribution. -/
def programPT05RealizedRelativeNullFaceDensityIntegral
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05RealizedNullFaceDensityIntegral realization input -
    programPT05RealizedNullFaceDensityIntegral realization 0

/-- Zero-normalized endpoint-joint contribution. -/
def programPT05RealizedRelativeEndpointJointActionAggregate
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  programPT05RealizedEndpointJointActionAggregate realization input -
    programPT05RealizedEndpointJointActionAggregate realization 0

/-- The induced physical null action is exactly the sum of the normalized
local face-density and endpoint-joint contributions. -/
theorem programPT05PhysicalNullAction_eq_density_add_joint
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    realization.toActionModel.action input =
      programPT05RealizedRelativeNullFaceDensityIntegral realization input +
        programPT05RealizedRelativeEndpointJointActionAggregate realization
          input := by
  rw [toActionModel_action_eq_realized_finiteNullBoundaryAction]
  unfold programPT05RealizedRelativeNullFaceDensityIntegral
    programPT05RealizedRelativeEndpointJointActionAggregate
    programPT05RealizedNullFaceDensityIntegral
    programPT05RealizedEndpointJointActionAggregate
  rw [← programPT05CanonicalNullFaceDensity_add_joint_eq_totalAction
      (realization.toDatum input),
    ← programPT05CanonicalNullFaceDensity_add_joint_eq_totalAction
      (realization.toDatum 0)]
  ring

/-- Support extension of the normalized integrated face-density contribution
to Gate 819's null-boundary slot.  Endpoint joints remain separate. -/
def programPT05PhysicalNullFaceDensityIntegratedRelativeCochain
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary =>
      (programPT05RealizedRelativeNullFaceDensityIntegral realization input, 0)
  | .joint => 0

@[simp]
theorem programPT05PhysicalNullFaceDensityIntegratedRelativeCochain_nullBoundary
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    programPT05PhysicalNullFaceDensityIntegratedRelativeCochain realization
        input .nullBoundary =
      (programPT05RealizedRelativeNullFaceDensityIntegral realization input,
        0) := by
  rfl

/-- The null-boundary coefficient plus its separately retained endpoint-joint
contribution is exactly the physical null action used by the induced model. -/
theorem programPT05PhysicalNullBoundaryComponent_add_joint_eq_action
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05PhysicalNullFaceDensityIntegratedRelativeCochain realization
        input .nullBoundary).1 +
        programPT05RealizedRelativeEndpointJointActionAggregate realization
          input =
      realization.toActionModel.action input := by
  change
    programPT05RealizedRelativeNullFaceDensityIntegral realization input +
        programPT05RealizedRelativeEndpointJointActionAggregate realization
          input =
      realization.toActionModel.action input
  exact (programPT05PhysicalNullAction_eq_density_add_joint
    realization input).symm

end
end P0EFTJanusProgramPT05NullFaceActionDensityAggregate4D
end JanusFormal
