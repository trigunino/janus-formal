namespace JanusFormal
namespace P0EFTJanusZ2SigmaHardTheoremTargetRegistry

set_option autoImplicit false

structure Z2SigmaHardTheoremTargetRegistry where
  rp4PinTargetDeclared : Prop
  rp4PinAcceptanceCriteriaDeclared : Prop
  projectiveTunnelRatioTargetDeclared : Prop
  projectiveTunnelRatioCriteriaDeclared : Prop
  sigmaBoundaryActionTargetDeclared : Prop
  sigmaBoundaryActionCriteriaDeclared : Prop
  importedTheoremMayReplaceOnlyMatchingTarget : Prop
  noFitPromotionRequiresAllTargetsClosed : Prop
  registryComplete : Prop

def z2SigmaHardTargetsDeclared
    (r : Z2SigmaHardTheoremTargetRegistry) : Prop :=
  r.rp4PinTargetDeclared /\
  r.rp4PinAcceptanceCriteriaDeclared /\
  r.projectiveTunnelRatioTargetDeclared /\
  r.projectiveTunnelRatioCriteriaDeclared /\
  r.sigmaBoundaryActionTargetDeclared /\
  r.sigmaBoundaryActionCriteriaDeclared

def z2SigmaHardRegistryReady
    (r : Z2SigmaHardTheoremTargetRegistry) : Prop :=
  z2SigmaHardTargetsDeclared r /\
  r.importedTheoremMayReplaceOnlyMatchingTarget /\
  r.noFitPromotionRequiresAllTargetsClosed /\
  r.registryComplete

theorem missing_sigma_boundary_target_blocks_registry
    (r : Z2SigmaHardTheoremTargetRegistry)
    (hMissing : Not r.sigmaBoundaryActionTargetDeclared) :
    Not (z2SigmaHardRegistryReady r) := by
  intro h
  exact hMissing h.1.2.2.2.2.1

theorem z2_sigma_registry_ready_enforces_no_fit_guard
    (r : Z2SigmaHardTheoremTargetRegistry)
    (h : z2SigmaHardRegistryReady r) :
    r.noFitPromotionRequiresAllTargetsClosed := by
  exact h.2.2.1

end P0EFTJanusZ2SigmaHardTheoremTargetRegistry
end JanusFormal
