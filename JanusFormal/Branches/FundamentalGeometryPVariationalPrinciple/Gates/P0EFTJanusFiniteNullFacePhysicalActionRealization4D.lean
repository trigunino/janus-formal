import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D

/-! # Realization of finite null-face physical coordinates

`FiniteNullFaceActionDatum` stores the reduced functions `area`, `inaffinity`
and `expansion`, together with endpoint-joint values.  It has no native field
for a null-face position or a two-dimensional screen metric.  Consequently a
map from the position/screen coordinates introduced by the preceding gate
cannot be extracted from that datum.

This gate records the missing information as an explicit typed realization.
Only the resulting finite null-boundary action is required to be `C²`; the
target datum itself has no topology.  The induced normalized action model is
then proved to agree with the existing finite null-face action, and its Euler
covector is the derivative of that realized action.

This is an interface for a later geometric construction.  It does not assert
that the reduced null-face datum already contains an embedding or an intrinsic
screen metric.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteNullFacePhysicalActionRealization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- A supplied realization sends every finite position/screen coordinate to
the reduced action datum of every null face. -/
abbrev FiniteNullFacePhysicalRealizationMap
    (NullFace : Type*) [Fintype NullFace] :=
  FiniteNullFacePhysicalHilbert NullFace →
    NullFace → FiniteNullFaceActionDatum

/-- Existing finite null-boundary action evaluated on a supplied realization. -/
def realizedTotalFiniteNullBoundaryAction
    {NullFace : Type*} [Fintype NullFace]
    (realize : FiniteNullFacePhysicalRealizationMap NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  totalFiniteNullBoundaryAction (realize input)

/-- Normalization at the zero physical coordinate removes the irrelevant
additive constant. -/
def realizedRelativeFiniteNullBoundaryAction
    {NullFace : Type*} [Fintype NullFace]
    (realize : FiniteNullFacePhysicalRealizationMap NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  realizedTotalFiniteNullBoundaryAction realize input -
    realizedTotalFiniteNullBoundaryAction realize 0

/-- Typed realization contract for the finite physical null-face coordinates.

The scalar composite is the strongest regularity statement currently
available: `FiniteNullFaceActionDatum` is a collection of supplied functions
and proofs and carries no ambient topological vector-space structure. -/
structure FiniteNullFacePhysicalActionRealization
    (NullFace : Type*) [Fintype NullFace] where
  toDatum : FiniteNullFacePhysicalRealizationMap NullFace
  domain : Set (FiniteNullFacePhysicalHilbert NullFace)
  domain_isOpen : IsOpen domain
  zero_mem_domain : (0 : FiniteNullFacePhysicalHilbert NullFace) ∈ domain
  totalAction_contDiffOn_two :
    ContDiffOn Real 2 (realizedTotalFiniteNullBoundaryAction toDatum) domain

/-- The physical null-face action model canonically induced by a supplied
realization into the existing reduced null-face action data. -/
def FiniteNullFacePhysicalActionRealization.toActionModel
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace) :
    FiniteNullFacePhysicalActionModel NullFace where
  domain := realization.domain
  action := realizedRelativeFiniteNullBoundaryAction realization.toDatum
  domain_isOpen := realization.domain_isOpen
  zero_mem_domain := realization.zero_mem_domain
  action_zero := by
    simp [realizedRelativeFiniteNullBoundaryAction]
  action_contDiffOn_two := by
    exact realization.totalAction_contDiffOn_two.sub contDiffOn_const

@[simp] theorem toActionModel_domain
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace) :
    realization.toActionModel.domain = realization.domain :=
  rfl

/-- Exact action agreement with the pre-existing finite null-face action. -/
theorem toActionModel_action_eq_realized_finiteNullBoundaryAction
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    realization.toActionModel.action input =
      totalFiniteNullBoundaryAction (realization.toDatum input) -
        totalFiniteNullBoundaryAction (realization.toDatum 0) :=
  rfl

/-- The normalized realized action has the same derivative as the existing
finite null-boundary action composed with the realization map. -/
theorem toActionModel_action_hasFDerivAt_realizedTotal
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.domain) :
    HasFDerivAt realization.toActionModel.action
      (fderiv Real
        (realizedTotalFiniteNullBoundaryAction realization.toDatum) input)
      input := by
  have hTotal : HasFDerivAt
      (realizedTotalFiniteNullBoundaryAction realization.toDatum)
      (fderiv Real
        (realizedTotalFiniteNullBoundaryAction realization.toDatum) input)
      input :=
    (((realization.totalAction_contDiffOn_two.contDiffAt
      (realization.domain_isOpen.mem_nhds hInput)).differentiableAt
        (by norm_num)).hasFDerivAt)
  change HasFDerivAt
    (fun current =>
      realizedTotalFiniteNullBoundaryAction realization.toDatum current -
        realizedTotalFiniteNullBoundaryAction realization.toDatum 0)
    _ input
  exact hTotal.sub_const
    (realizedTotalFiniteNullBoundaryAction realization.toDatum 0)

/-- Euler agreement: the physical null Euler block is exactly the derivative
of the already-defined finite face-plus-joints action after realization. -/
theorem finiteNullFacePhysicalEuler_toActionModel_eq_realizedTotal_fderiv
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.domain) :
    finiteNullFacePhysicalEuler realization.toActionModel input =
      fderiv Real
        (realizedTotalFiniteNullBoundaryAction realization.toDatum) input :=
  (toActionModel_action_hasFDerivAt_realizedTotal realization input hInput).fderiv

/-- Realized physical null stationarity is precisely stationarity of the
existing finite face-plus-joints action along the supplied coordinates. -/
theorem finiteNullFacePhysicalEuler_toActionModel_eq_zero_iff
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFacePhysicalActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.domain) :
    finiteNullFacePhysicalEuler realization.toActionModel input = 0 ↔
      fderiv Real
        (fun current : FiniteNullFacePhysicalHilbert NullFace =>
          totalFiniteNullBoundaryAction (realization.toDatum current)) input = 0 := by
  rw [finiteNullFacePhysicalEuler_toActionModel_eq_realizedTotal_fderiv
    realization input hInput]
  rfl

end
end P0EFTJanusFiniteNullFacePhysicalActionRealization4D
end JanusFormal
