import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTDiracCartanAPSPTReduction

namespace JanusFormal
namespace P0EFTThinShellTetradChirality

set_option autoImplicit false

structure OrbifoldTetradSoldering where
  z2IsometryAcrossSigma : Prop
  cartanSolderFormInvariant : Prop
  normalReversalUnderPT : Prop
  tetradSignTransition : Prop

structure TraceTorsionThinShell where
  qTIsOne : Prop
  radionGradientHasDeltaSigma : Prop
  diracCartanThinShellIntegrated : Prop
  spinorJumpConditionDerived : Prop
  chiralBoundaryProjectorDerived : Prop
  chiralProjectorPreservesAPSDomain : Prop

def tetradSignFromSoldering (s : OrbifoldTetradSoldering) : Prop :=
  s.z2IsometryAcrossSigma /\
  s.cartanSolderFormInvariant /\
  s.normalReversalUnderPT /\
  s.tetradSignTransition

def chiralityFromTraceTorsionShell (shell : TraceTorsionThinShell) : Prop :=
  shell.qTIsOne /\
  shell.radionGradientHasDeltaSigma /\
  shell.diracCartanThinShellIntegrated /\
  shell.spinorJumpConditionDerived /\
  shell.chiralBoundaryProjectorDerived /\
  shell.chiralProjectorPreservesAPSDomain

theorem soldering_conditions_give_tetrad_sign
    (s : OrbifoldTetradSoldering)
    (hZ2 : s.z2IsometryAcrossSigma)
    (hSolder : s.cartanSolderFormInvariant)
    (hNormal : s.normalReversalUnderPT)
    (hSign : s.tetradSignTransition) :
    tetradSignFromSoldering s := by
  exact And.intro hZ2
    (And.intro hSolder
      (And.intro hNormal hSign))

theorem trace_torsion_shell_gives_chirality_and_aps_domain
    (shell : TraceTorsionThinShell)
    (hQT : shell.qTIsOne)
    (hDelta : shell.radionGradientHasDeltaSigma)
    (hIntegrated : shell.diracCartanThinShellIntegrated)
    (hJump : shell.spinorJumpConditionDerived)
    (hChiral : shell.chiralBoundaryProjectorDerived)
    (hAPS : shell.chiralProjectorPreservesAPSDomain) :
    chiralityFromTraceTorsionShell shell := by
  exact And.intro hQT
    (And.intro hDelta
      (And.intro hIntegrated
        (And.intro hJump
          (And.intro hChiral hAPS))))

theorem thin_shell_and_soldering_feed_pt_reduction
    (s : OrbifoldTetradSoldering)
    (shell : TraceTorsionThinShell)
    (hSolder : tetradSignFromSoldering s)
    (hShell : chiralityFromTraceTorsionShell shell) :
    s.tetradSignTransition /\ shell.chiralProjectorPreservesAPSDomain := by
  exact And.intro hSolder.right.right.right hShell.right.right.right.right.right

end P0EFTThinShellTetradChirality
end JanusFormal
