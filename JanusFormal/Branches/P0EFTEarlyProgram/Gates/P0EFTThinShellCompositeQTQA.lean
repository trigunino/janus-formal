import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTThinShellJumpSymbolic

namespace JanusFormal
namespace P0EFTThinShellCompositeQTQA

set_option autoImplicit false

structure CompositeShellMatrix where
  qTNonzero : Prop
  qANonzero : Prop
  traceOnlyNoGo : Prop
  chiralCliffordGeneratorPresent : Prop
  idempotenceEquationsDerived : Prop
  shellNormalizationDerived : Prop
  normalizedChiralProjector : Prop

def compositeCanSupportChiralProjector (m : CompositeShellMatrix) : Prop :=
  m.qTNonzero /\
  m.qANonzero /\
  m.chiralCliffordGeneratorPresent /\
  m.idempotenceEquationsDerived

def compositeClosesProjector (m : CompositeShellMatrix) : Prop :=
  compositeCanSupportChiralProjector m /\
  m.shellNormalizationDerived /\
  m.normalizedChiralProjector

theorem axial_term_is_required_for_chiral_clifford_split
    (m : CompositeShellMatrix)
    (hQT : m.qTNonzero)
    (hQA : m.qANonzero)
    (hC : m.chiralCliffordGeneratorPresent)
    (hIdem : m.idempotenceEquationsDerived) :
    compositeCanSupportChiralProjector m := by
  exact And.intro hQT
    (And.intro hQA
      (And.intro hC hIdem))

theorem missing_shell_normalization_blocks_projector_closure
    (m : CompositeShellMatrix)
    (hMissing : Not m.shellNormalizationDerived) :
    Not (compositeClosesProjector m) := by
  intro h
  exact hMissing h.right.left

theorem normalized_composite_shell_closes_chiral_projector
    (m : CompositeShellMatrix)
    (hSupport : compositeCanSupportChiralProjector m)
    (hNorm : m.shellNormalizationDerived)
    (hProjector : m.normalizedChiralProjector) :
    compositeClosesProjector m := by
  exact And.intro hSupport (And.intro hNorm hProjector)

end P0EFTThinShellCompositeQTQA
end JanusFormal
