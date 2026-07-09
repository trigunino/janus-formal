import JanusFormal.Legacy.P0EFT.Gates.P0EFTECNormalizationBranch
import JanusFormal.Legacy.P0EFT.Gates.P0EFTGrowthKinkMuFunctions

namespace JanusFormal
namespace P0EFTGrowthSolverECBranch

set_option autoImplicit false

structure GrowthSolverECBranch where
  muIsoECBranchClosed : Prop
  growthSolverEquationsClosedSymbolically : Prop
  omegaTorsionBackgroundSpecified : Prop
  skinkClosed : Prop
  growthSolverImplemented : Prop
  fsigma8CurveGenerated : Prop

def growthECEquationsReady (g : GrowthSolverECBranch) : Prop :=
  g.muIsoECBranchClosed /\
  g.growthSolverEquationsClosedSymbolically

def growthECReadyToIntegrate (g : GrowthSolverECBranch) : Prop :=
  growthECEquationsReady g /\
  g.omegaTorsionBackgroundSpecified /\
  g.skinkClosed

def growthECPredictionReady (g : GrowthSolverECBranch) : Prop :=
  growthECReadyToIntegrate g /\
  g.growthSolverImplemented /\
  g.fsigma8CurveGenerated

theorem ec_mu_closes_symbolic_growth_equations
    (g : GrowthSolverECBranch)
    (hMu : g.muIsoECBranchClosed)
    (hEq : g.growthSolverEquationsClosedSymbolically) :
    growthECEquationsReady g := by
  exact And.intro hMu hEq

theorem missing_background_blocks_growth_integration
    (g : GrowthSolverECBranch)
    (hMissing : Not g.omegaTorsionBackgroundSpecified) :
    Not (growthECReadyToIntegrate g) := by
  intro h
  exact hMissing h.right.left

theorem missing_skink_blocks_growth_integration
    (g : GrowthSolverECBranch)
    (hMissing : Not g.skinkClosed) :
    Not (growthECReadyToIntegrate g) := by
  intro h
  exact hMissing h.right.right

end P0EFTGrowthSolverECBranch
end JanusFormal
