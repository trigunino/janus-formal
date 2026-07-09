namespace JanusFormal
namespace P0EFTJanusZ4PhotonBaryonHierarchyTarget

set_option autoImplicit false

structure PhotonBaryonHierarchyTarget where
  photonContinuityDeclared : Prop
  photonEulerDeclared : Prop
  baryonContinuityDeclared : Prop
  baryonEulerDeclared : Prop
  thomsonCouplingDeclared : Prop
  z4MetricSourceCoupled : Prop
  recombinationVisibilityCoupled : Prop
  coefficientsDerivedFromAction : Prop

def hierarchyTargetReady (h : PhotonBaryonHierarchyTarget) : Prop :=
  h.photonContinuityDeclared /\
  h.photonEulerDeclared /\
  h.baryonContinuityDeclared /\
  h.baryonEulerDeclared /\
  h.thomsonCouplingDeclared /\
  h.z4MetricSourceCoupled /\
  h.recombinationVisibilityCoupled

def hierarchyPhysicalReady (h : PhotonBaryonHierarchyTarget) : Prop :=
  hierarchyTargetReady h /\
  h.coefficientsDerivedFromAction

theorem hierarchy_target_does_not_imply_physical_coefficients
    (h : PhotonBaryonHierarchyTarget)
    (_ready : hierarchyTargetReady h)
    (hMissing : Not h.coefficientsDerivedFromAction) :
    Not (hierarchyPhysicalReady h) := by
  intro hp
  exact hMissing hp.right

end P0EFTJanusZ4PhotonBaryonHierarchyTarget
end JanusFormal
