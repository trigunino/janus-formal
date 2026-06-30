import JanusFormal.P0EFTThinShellTetradChirality

namespace JanusFormal
namespace P0EFTThinShellJumpSymbolic

set_option autoImplicit false

structure ThinShellJump where
  traceTorsionDeltaIntegrated : Prop
  spinorJumpConditionDerived : Prop
  shellCliffordMatrixKnown : Prop
  shellMatrixIsGammaNormalGammaFive : Prop
  chiralProjectorDerived : Prop
  apsDomainPreserved : Prop

def traceTorsionGivesJumpOnly (j : ThinShellJump) : Prop :=
  j.traceTorsionDeltaIntegrated /\ j.spinorJumpConditionDerived

def jumpGivesChiralProjector (j : ThinShellJump) : Prop :=
  j.traceTorsionDeltaIntegrated /\
  j.spinorJumpConditionDerived /\
  j.shellCliffordMatrixKnown /\
  j.shellMatrixIsGammaNormalGammaFive /\
  j.chiralProjectorDerived

theorem thin_shell_delta_gives_spinor_jump
    (j : ThinShellJump)
    (hDelta : j.traceTorsionDeltaIntegrated)
    (hJump : j.spinorJumpConditionDerived) :
    traceTorsionGivesJumpOnly j := by
  exact And.intro hDelta hJump

theorem missing_clifford_matrix_blocks_chiral_projector
    (j : ThinShellJump)
    (hMissing : Not j.shellCliffordMatrixKnown) :
    Not (jumpGivesChiralProjector j) := by
  intro h
  exact hMissing h.right.right.left

theorem gamma_normal_gamma_five_shell_gives_chiral_projector
    (j : ThinShellJump)
    (hDelta : j.traceTorsionDeltaIntegrated)
    (hJump : j.spinorJumpConditionDerived)
    (hKnown : j.shellCliffordMatrixKnown)
    (hGamma5 : j.shellMatrixIsGammaNormalGammaFive)
    (hChiral : j.chiralProjectorDerived) :
    jumpGivesChiralProjector j := by
  exact And.intro hDelta
    (And.intro hJump
      (And.intro hKnown
        (And.intro hGamma5 hChiral)))

end P0EFTThinShellJumpSymbolic
end JanusFormal
