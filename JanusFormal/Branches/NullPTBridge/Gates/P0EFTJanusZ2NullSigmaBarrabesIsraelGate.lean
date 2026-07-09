namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaBarrabesIsraelGate

set_option autoImplicit false

structure NullSigmaBarrabesIsraelGate where
  ptJointTermReady : Prop
  plusSideTransverseCurvatureComputed : Prop
  minusSideTransverseCurvatureDerived : Prop
  transverseCurvatureJumpDerived : Prop
  freeOrientationSignChosen : Prop
  nullShellStressMappingReady : Prop
  regularHKPipelineAllowed : Prop
  nullJunctionBalanceReady : Prop

def localBarrabesDataReady
    (g : NullSigmaBarrabesIsraelGate) : Prop :=
  g.ptJointTermReady /\
  g.plusSideTransverseCurvatureComputed /\
  Not g.freeOrientationSignChosen

def stressMappingPrerequisites
    (g : NullSigmaBarrabesIsraelGate) : Prop :=
  g.minusSideTransverseCurvatureDerived /\
  g.transverseCurvatureJumpDerived

theorem stress_mapping_requires_curvature_jump
    (g : NullSigmaBarrabesIsraelGate)
    (hStress : g.nullShellStressMappingReady)
    (hNeeds : g.nullShellStressMappingReady -> stressMappingPrerequisites g) :
    stressMappingPrerequisites g := by
  exact hNeeds hStress

theorem null_junction_requires_shell_stress_mapping
    (g : NullSigmaBarrabesIsraelGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeeds : g.nullJunctionBalanceReady -> g.nullShellStressMappingReady) :
    g.nullShellStressMappingReady := by
  exact hNeeds hBalance

end P0EFTJanusZ2NullSigmaBarrabesIsraelGate
end JanusFormal
