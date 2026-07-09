import JanusFormal.Legacy.P0EFT.Gates.P0EFTKinkLensingGrowthBridge

namespace JanusFormal
namespace P0EFTGrowthKinkSolverTarget

set_option autoImplicit false

structure GrowthKinkSolverTarget where
  growthStateDefined : Prop
  bulkGrowthEquationDefined : Prop
  deltaContinuityAcrossKink : Prop
  deltaPrimeJumpConditionDefined : Prop
  geffDerivedFromActiveStress : Prop
  skinkDerivedFromSlipJump : Prop
  growthSolverImplemented : Prop
  fsigma8PredictionReady : Prop

def kinkGrowthSystemDefined (g : GrowthKinkSolverTarget) : Prop :=
  g.growthStateDefined /\
  g.bulkGrowthEquationDefined /\
  g.deltaContinuityAcrossKink /\
  g.deltaPrimeJumpConditionDefined

def kinkGrowthPredictionReady (g : GrowthKinkSolverTarget) : Prop :=
  kinkGrowthSystemDefined g /\
  g.geffDerivedFromActiveStress /\
  g.skinkDerivedFromSlipJump /\
  g.growthSolverImplemented /\
  g.fsigma8PredictionReady

theorem kink_jump_system_is_well_posed_target
    (g : GrowthKinkSolverTarget)
    (hState : g.growthStateDefined)
    (hBulk : g.bulkGrowthEquationDefined)
    (hCont : g.deltaContinuityAcrossKink)
    (hJump : g.deltaPrimeJumpConditionDefined) :
    kinkGrowthSystemDefined g := by
  exact And.intro hState (And.intro hBulk (And.intro hCont hJump))

theorem missing_geff_blocks_growth_prediction
    (g : GrowthKinkSolverTarget)
    (hMissing : Not g.geffDerivedFromActiveStress) :
    Not (kinkGrowthPredictionReady g) := by
  intro h
  exact hMissing h.right.left

theorem missing_skink_blocks_growth_prediction
    (g : GrowthKinkSolverTarget)
    (hMissing : Not g.skinkDerivedFromSlipJump) :
    Not (kinkGrowthPredictionReady g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTGrowthKinkSolverTarget
end JanusFormal
