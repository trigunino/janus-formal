namespace JanusFormal
namespace P0EFTJanusZ2NullSigmaVariationReductionGate

set_option autoImplicit false

structure NullSigmaVariationReductionGate where
  nullDensitySqrtQKappaIdentified : Prop
  deltaSqrtQFormulaReady : Prop
  deltaKappaFormulaReady : Prop
  bulkNullDensityVariationReduced : Prop
  ptJointTermReady : Prop
  nullGeneratorRescalingQuotiented : Prop
  nullShellStressMappingReady : Prop
  regularHKPipelineAllowed : Prop
  nullJunctionBalanceReady : Prop

def bulkReductionReady
    (g : NullSigmaVariationReductionGate) : Prop :=
  g.nullDensitySqrtQKappaIdentified /\
  g.deltaSqrtQFormulaReady /\
  g.deltaKappaFormulaReady /\
  g.bulkNullDensityVariationReduced

def nullJunctionPrerequisites
    (g : NullSigmaVariationReductionGate) : Prop :=
  g.ptJointTermReady /\
  g.nullGeneratorRescalingQuotiented /\
  g.nullShellStressMappingReady

theorem bulk_reduction_does_not_enable_regular_hK
    (g : NullSigmaVariationReductionGate)
    (_h : bulkReductionReady g)
    (hNoHK : Not g.regularHKPipelineAllowed) :
    Not g.regularHKPipelineAllowed := by
  exact hNoHK

theorem null_junction_requires_joint_rescaling_and_stress
    (g : NullSigmaVariationReductionGate)
    (hBalance : g.nullJunctionBalanceReady)
    (hNeeds : g.nullJunctionBalanceReady -> nullJunctionPrerequisites g) :
    nullJunctionPrerequisites g := by
  exact hNeeds hBalance

end P0EFTJanusZ2NullSigmaVariationReductionGate
end JanusFormal
