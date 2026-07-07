namespace JanusFormal
namespace P0EFTJanusZ2AlphaTwoHardRoutesGate

set_option autoImplicit false

structure AlphaTwoHardRoutesGate where
  thetaPTReady : Prop
  thetaPTZero : Prop
  nonzeroKKSDensityDerived : Prop
  minisuperspaceLagrangianReady : Prop
  onShellActionAlphaDerived : Prop
  finiteBoundaryPrescriptionDerived : Prop
  uniqueMinimumDerived : Prop

def ptHolonomyPhaseReady (g : AlphaTwoHardRoutesGate) : Prop :=
  g.thetaPTReady /\ (Not g.thetaPTZero \/ g.nonzeroKKSDensityDerived)

def vAlphaSelectorReady (g : AlphaTwoHardRoutesGate) : Prop :=
  g.minisuperspaceLagrangianReady /\
  g.onShellActionAlphaDerived /\
  g.finiteBoundaryPrescriptionDerived /\
  g.uniqueMinimumDerived

def alphaGeneratedByHardRoutes (g : AlphaTwoHardRoutesGate) : Prop :=
  ptHolonomyPhaseReady g \/ vAlphaSelectorReady g

theorem zero_theta_and_no_kks_blocks_pt_holonomy
    (g : AlphaTwoHardRoutesGate)
    (hZero : g.thetaPTZero)
    (hNoKKS : Not g.nonzeroKKSDensityDerived) :
    Not (ptHolonomyPhaseReady g) := by
  intro h
  rcases h.right with hNonzero | hKKS
  · exact hNonzero hZero
  · exact hNoKKS hKKS

theorem no_onshell_action_blocks_v_alpha
    (g : AlphaTwoHardRoutesGate)
    (hMissing : Not g.onShellActionAlphaDerived) :
    Not (vAlphaSelectorReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusZ2AlphaTwoHardRoutesGate
end JanusFormal
