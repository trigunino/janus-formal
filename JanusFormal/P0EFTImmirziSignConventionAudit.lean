namespace JanusFormal
namespace P0EFTImmirziSignConventionAudit

set_option autoImplicit false

structure ImmirziSignConventionAudit where
  momentumAnchorPresent : Prop
  slipAnchorPresent : Prop
  baryonBackreactionAnchorPresent : Prop
  signConventionsChecked : Prop

def signAuditReady (a : ImmirziSignConventionAudit) : Prop :=
  a.momentumAnchorPresent /\
  a.slipAnchorPresent /\
  a.baryonBackreactionAnchorPresent /\
  a.signConventionsChecked

def neutralPatchAllowed (a : ImmirziSignConventionAudit) : Prop :=
  signAuditReady a

theorem anchors_and_signs_allow_neutral_patch
    (a : ImmirziSignConventionAudit)
    (hMomentum : a.momentumAnchorPresent)
    (hSlip : a.slipAnchorPresent)
    (hBackreaction : a.baryonBackreactionAnchorPresent)
    (hSigns : a.signConventionsChecked) :
    neutralPatchAllowed a := by
  exact And.intro hMomentum (And.intro hSlip (And.intro hBackreaction hSigns))

end P0EFTImmirziSignConventionAudit
end JanusFormal
