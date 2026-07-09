import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTGrowthKinkSolverTarget

namespace JanusFormal
namespace P0EFTGrowthKinkMuFunctions

set_option autoImplicit false

structure GrowthKinkMuFunctions where
  skinkFormulaEncoded : Prop
  skinkCoefficientDerived : Prop
  muFormEncoded : Prop
  meff2ConditionallyClosed : Prop
  alphaJanusDerivedFromActiveStress : Prop
  growthSolverReady : Prop
  fsigma8PredictionReady : Prop

def growthFunctionsPartial (g : GrowthKinkMuFunctions) : Prop :=
  g.skinkFormulaEncoded /\
  g.muFormEncoded /\
  g.meff2ConditionallyClosed

def growthFunctionsClosed (g : GrowthKinkMuFunctions) : Prop :=
  growthFunctionsPartial g /\
  g.skinkCoefficientDerived /\
  g.alphaJanusDerivedFromActiveStress /\
  g.growthSolverReady /\
  g.fsigma8PredictionReady

theorem meff_and_mu_form_start_growth_functions
    (g : GrowthKinkMuFunctions)
    (hS : g.skinkFormulaEncoded)
    (hMu : g.muFormEncoded)
    (hM : g.meff2ConditionallyClosed) :
    growthFunctionsPartial g := by
  exact And.intro hS (And.intro hMu hM)

theorem missing_alpha_blocks_growth_prediction
    (g : GrowthKinkMuFunctions)
    (hMissing : Not g.alphaJanusDerivedFromActiveStress) :
    Not (growthFunctionsClosed g) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_skink_coefficient_blocks_growth_prediction
    (g : GrowthKinkMuFunctions)
    (hMissing : Not g.skinkCoefficientDerived) :
    Not (growthFunctionsClosed g) := by
  intro h
  exact hMissing h.right.left

end P0EFTGrowthKinkMuFunctions
end JanusFormal
