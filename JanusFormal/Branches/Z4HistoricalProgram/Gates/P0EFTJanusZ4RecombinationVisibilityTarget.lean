namespace JanusFormal
namespace P0EFTJanusZ4RecombinationVisibilityTarget

set_option autoImplicit false

structure RecombinationVisibilityTarget where
  opticalDepthDerivativeDeclared : Prop
  visibilityFunctionDeclared : Prop
  ionizationHistoryRequired : Prop
  z4BackgroundCoupled : Prop
  thomsonNormalizationDeclared : Prop
  ionizationHistoryDerived : Prop

def visibilityTargetReady (r : RecombinationVisibilityTarget) : Prop :=
  r.opticalDepthDerivativeDeclared /\
  r.visibilityFunctionDeclared /\
  r.ionizationHistoryRequired /\
  r.z4BackgroundCoupled /\
  r.thomsonNormalizationDeclared

def visibilityPhysicalReady (r : RecombinationVisibilityTarget) : Prop :=
  visibilityTargetReady r /\
  r.ionizationHistoryDerived

theorem visibility_target_does_not_derive_ionization_history
    (r : RecombinationVisibilityTarget)
    (_ready : visibilityTargetReady r)
    (hMissing : Not r.ionizationHistoryDerived) :
    Not (visibilityPhysicalReady r) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4RecombinationVisibilityTarget
end JanusFormal
