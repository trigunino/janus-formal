import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BackgroundClosure

namespace JanusFormal
namespace P0EFTJanusZ4BackgroundBianchiIdentity

set_option autoImplicit false

structure BackgroundBianchiIdentity where
  friedmannConstraintUsed : Prop
  masterContinuityUsed : Prop
  accelerationConstraintRecovered : Prop
  determinantMasterDensityUsed : Prop
  noExtraBackgroundFluidIntroduced : Prop
  coefficientsFromFullAction : Prop

def backgroundBianchiIdentityReady (b : BackgroundBianchiIdentity) : Prop :=
  b.friedmannConstraintUsed /\
  b.masterContinuityUsed /\
  b.accelerationConstraintRecovered /\
  b.determinantMasterDensityUsed /\
  b.noExtraBackgroundFluidIntroduced

def backgroundFullyDerived (b : BackgroundBianchiIdentity) : Prop :=
  backgroundBianchiIdentityReady b /\
  b.coefficientsFromFullAction

theorem bianchi_identity_preserves_no_extra_fluid
    (b : BackgroundBianchiIdentity)
    (h : backgroundBianchiIdentityReady b) :
    b.noExtraBackgroundFluidIntroduced := by
  exact h.right.right.right.right

theorem bianchi_identity_does_not_replace_action_derivation
    (b : BackgroundBianchiIdentity)
    (_h : backgroundBianchiIdentityReady b)
    (hMissing : Not b.coefficientsFromFullAction) :
    Not (backgroundFullyDerived b) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4BackgroundBianchiIdentity
end JanusFormal
