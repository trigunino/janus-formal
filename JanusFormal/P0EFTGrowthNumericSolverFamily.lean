import JanusFormal.P0EFTGrowthSolverECBranch

namespace JanusFormal
namespace P0EFTGrowthNumericSolverFamily

set_option autoImplicit false

structure GrowthNumericSolverFamily where
  numericSolverFamilySpecified : Prop
  piecewiseKickIntegrationSpecified : Prop
  omegaTorsionBackgroundDerivedFromJanus : Prop
  skinkAmplitudeDerived : Prop
  fsigma8FamilyReady : Prop
  fsigma8PredictionNoFitReady : Prop

def fsigma8FamilyReady (g : GrowthNumericSolverFamily) : Prop :=
  g.numericSolverFamilySpecified /\
  g.piecewiseKickIntegrationSpecified /\
  g.fsigma8FamilyReady

def fsigma8NoFitReady (g : GrowthNumericSolverFamily) : Prop :=
  fsigma8FamilyReady g /\
  g.omegaTorsionBackgroundDerivedFromJanus /\
  g.skinkAmplitudeDerived /\
  g.fsigma8PredictionNoFitReady

theorem numeric_family_can_be_prepared_before_final_background
    (g : GrowthNumericSolverFamily)
    (hSolver : g.numericSolverFamilySpecified)
    (hKick : g.piecewiseKickIntegrationSpecified)
    (hFamily : g.fsigma8FamilyReady) :
    fsigma8FamilyReady g := by
  exact And.intro hSolver (And.intro hKick hFamily)

theorem missing_janus_background_blocks_no_fit_prediction
    (g : GrowthNumericSolverFamily)
    (hMissing : Not g.omegaTorsionBackgroundDerivedFromJanus) :
    Not (fsigma8NoFitReady g) := by
  intro h
  exact hMissing h.right.left

theorem missing_skink_blocks_no_fit_prediction
    (g : GrowthNumericSolverFamily)
    (hMissing : Not g.skinkAmplitudeDerived) :
    Not (fsigma8NoFitReady g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTGrowthNumericSolverFamily
end JanusFormal
