import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTPhysicalBranchScan

namespace JanusFormal
namespace P0EFTGrowthMasterBranchExport

set_option autoImplicit false

structure GrowthMasterBranchExport where
  physicalBranchSelected : Prop
  friedmannMatterPositive : Prop
  z0ToZ2CurveExported : Prop
  plotExported : Prop
  observationalFSigma8TableLoaded : Prop
  directSurveyComparisonDone : Prop
  fullCosmologyPredictionReady : Prop

def masterBranchCurveReady (g : GrowthMasterBranchExport) : Prop :=
  g.physicalBranchSelected /\
  g.friedmannMatterPositive /\
  g.z0ToZ2CurveExported /\
  g.plotExported

def surveyComparisonReady (g : GrowthMasterBranchExport) : Prop :=
  masterBranchCurveReady g /\
  g.observationalFSigma8TableLoaded /\
  g.directSurveyComparisonDone

def fullPredictionReadyAfterSurveyComparison (g : GrowthMasterBranchExport) : Prop :=
  surveyComparisonReady g /\ g.fullCosmologyPredictionReady

theorem selected_physical_branch_exports_curve
    (g : GrowthMasterBranchExport)
    (hBranch : g.physicalBranchSelected)
    (hMatter : g.friedmannMatterPositive)
    (hCurve : g.z0ToZ2CurveExported)
    (hPlot : g.plotExported) :
    masterBranchCurveReady g := by
  exact And.intro hBranch (And.intro hMatter (And.intro hCurve hPlot))

theorem missing_observational_table_blocks_survey_comparison
    (g : GrowthMasterBranchExport)
    (hMissing : Not g.observationalFSigma8TableLoaded) :
    Not (surveyComparisonReady g) := by
  intro h
  exact hMissing h.right.left

end P0EFTGrowthMasterBranchExport
end JanusFormal
