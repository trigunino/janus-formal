import JanusFormal.Legacy.P0EFT.Gates.P0EFTJBgBackgroundDerivation
import JanusFormal.Legacy.P0EFT.Gates.P0EFTGrowthNumericSolverFamily

namespace JanusFormal
namespace P0EFTGrowthNoFitNumericalExport

set_option autoImplicit false

structure GrowthNoFitNumericalExport where
  orientationUnitsSelectedForBranch : Prop
  atanhDomainChecked : Prop
  chiInfinityExported : Prop
  lambdaJExported : Prop
  omegaTProfileGenerated : Prop
  growthCurveGenerated : Prop
  fsigma8PredictionNoFitReadyConditionally : Prop
  observationalMatterBackgroundFixed : Prop
  fullCosmologyPredictionReady : Prop

def noFitNumericalExportConditional (g : GrowthNoFitNumericalExport) : Prop :=
  g.orientationUnitsSelectedForBranch /\
  g.atanhDomainChecked /\
  g.chiInfinityExported /\
  g.lambdaJExported /\
  g.omegaTProfileGenerated /\
  g.growthCurveGenerated /\
  g.fsigma8PredictionNoFitReadyConditionally

def fullCosmologyReadyAfterMatterBackground (g : GrowthNoFitNumericalExport) : Prop :=
  noFitNumericalExportConditional g /\
  g.observationalMatterBackgroundFixed /\
  g.fullCosmologyPredictionReady

theorem branch_constants_export_conditional_growth_curve
    (g : GrowthNoFitNumericalExport)
    (hBranch : g.orientationUnitsSelectedForBranch)
    (hBound : g.atanhDomainChecked)
    (hChi : g.chiInfinityExported)
    (hLambda : g.lambdaJExported)
    (hOmega : g.omegaTProfileGenerated)
    (hCurve : g.growthCurveGenerated)
    (hReady : g.fsigma8PredictionNoFitReadyConditionally) :
    noFitNumericalExportConditional g := by
  exact And.intro hBranch
    (And.intro hBound
      (And.intro hChi
        (And.intro hLambda
          (And.intro hOmega
            (And.intro hCurve hReady)))))

theorem missing_matter_background_blocks_full_cosmology_ready
    (g : GrowthNoFitNumericalExport)
    (hMissing : Not g.observationalMatterBackgroundFixed) :
    Not (fullCosmologyReadyAfterMatterBackground g) := by
  intro h
  exact hMissing h.right.left

end P0EFTGrowthNoFitNumericalExport
end JanusFormal
