import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4APSIndexPackageObligationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4OrbifoldCoverRatioObligationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NonlinearELResidualObligationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NonlinearBoundaryVariationObligationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4WardAtomicClosureGate

namespace JanusFormal
namespace P0EFTJanusZ4HardExternalTheoremTargetRegistry

set_option autoImplicit false

structure HardExternalTheoremTargetRegistry where
  apsPinExternalTargetDeclared : Prop
  apsPinAcceptanceCriteriaDeclared : Prop
  orbifoldExternalTargetDeclared : Prop
  orbifoldAcceptanceCriteriaDeclared : Prop
  actionExternalTargetDeclared : Prop
  actionAcceptanceCriteriaDeclared : Prop
  importedTheoremMayReplaceOnlyMatchingTarget : Prop
  noFitPromotionRequiresAllTargetsClosed : Prop
  registryComplete : Prop

def hardExternalTargetsDeclared
    (r : HardExternalTheoremTargetRegistry) : Prop :=
  r.apsPinExternalTargetDeclared /\
  r.apsPinAcceptanceCriteriaDeclared /\
  r.orbifoldExternalTargetDeclared /\
  r.orbifoldAcceptanceCriteriaDeclared /\
  r.actionExternalTargetDeclared /\
  r.actionAcceptanceCriteriaDeclared

def hardExternalRegistryReady
    (r : HardExternalTheoremTargetRegistry) : Prop :=
  hardExternalTargetsDeclared r /\
  r.importedTheoremMayReplaceOnlyMatchingTarget /\
  r.noFitPromotionRequiresAllTargetsClosed /\
  r.registryComplete

theorem missing_action_target_blocks_registry
    (r : HardExternalTheoremTargetRegistry)
    (hMissing : Not r.actionExternalTargetDeclared) :
    Not (hardExternalRegistryReady r) := by
  intro h
  exact hMissing h.left.right.right.right.right.left

theorem registry_ready_enforces_no_fit_guard
    (r : HardExternalTheoremTargetRegistry)
    (h : hardExternalRegistryReady r) :
    r.noFitPromotionRequiresAllTargetsClosed := by
  exact h.right.right.left

end P0EFTJanusZ4HardExternalTheoremTargetRegistry
end JanusFormal
