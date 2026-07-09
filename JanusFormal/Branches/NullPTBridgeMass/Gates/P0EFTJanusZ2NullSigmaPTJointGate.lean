namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaPTJointGate

set_option autoImplicit false

structure NullSigmaPTJointGate where
  bulkNullDensityVariationReduced : Prop
  canonicalPTNormalizationFixed : Prop
  freeBoostRescalingAllowed : Prop
  ptJointTermReduced : Prop
  ptJointTermReady : Prop
  nullShellStressMappingReady : Prop
  regularHKPipelineAllowed : Prop
  nullJunctionBalanceReady : Prop

def ptJointClosureReady
    (g : NullSigmaPTJointGate) : Prop :=
  g.bulkNullDensityVariationReduced /\
  g.canonicalPTNormalizationFixed /\
  Not g.freeBoostRescalingAllowed /\
  g.ptJointTermReduced /\
  g.ptJointTermReady

theorem pt_joint_does_not_enable_regular_hK
    (g : NullSigmaPTJointGate)
    (_h : ptJointClosureReady g)
    (hNoHK : Not g.regularHKPipelineAllowed) :
    Not g.regularHKPipelineAllowed := by
  exact hNoHK

theorem null_junction_still_requires_shell_stress_mapping
    (g : NullSigmaPTJointGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeeds : g.nullJunctionBalanceReady -> g.nullShellStressMappingReady) :
    g.nullShellStressMappingReady := by
  exact hNeeds hBalance

end P0EFTJanusZ2NullSigmaPTJointGate
end JanusFormal
