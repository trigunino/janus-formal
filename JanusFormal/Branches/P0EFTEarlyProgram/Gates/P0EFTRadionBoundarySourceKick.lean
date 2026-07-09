import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTRadionBackgroundDynamics
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryRun1CombinedClosure

namespace JanusFormal
namespace P0EFTRadionBoundarySourceKick

set_option autoImplicit false

structure RadionBoundarySourceKick where
  sourceDefinedAsBoundaryVariation : Prop
  lambdaSourceClosed : Prop
  kappaSourceClosed : Prop
  betaDeltaChiVariedAsResponseProduct : Prop
  betaResponseProductHasNoLocalRadionForce : Prop
  betaConstantBranchRejectedForNoFit : Prop
  sourceKickFormulaEncoded : Prop
  orientationConventionFixed : Prop
  bulkPotentialFixedFromJanusAction : Prop
  omegaTNoFitReady : Prop

def boundarySourceKickStructured (s : RadionBoundarySourceKick) : Prop :=
  s.sourceDefinedAsBoundaryVariation /\
  s.lambdaSourceClosed /\
  s.kappaSourceClosed /\
  s.betaDeltaChiVariedAsResponseProduct /\
  s.betaResponseProductHasNoLocalRadionForce /\
  s.betaConstantBranchRejectedForNoFit /\
  s.sourceKickFormulaEncoded

def radionNoFitBackgroundReady (s : RadionBoundarySourceKick) : Prop :=
  boundarySourceKickStructured s /\
  s.orientationConventionFixed /\
  s.bulkPotentialFixedFromJanusAction /\
  s.omegaTNoFitReady

theorem run1_boundary_variation_structures_radion_kick
    (s : RadionBoundarySourceKick)
    (hVar : s.sourceDefinedAsBoundaryVariation)
    (hLambda : s.lambdaSourceClosed)
    (hKappa : s.kappaSourceClosed)
    (hBetaProduct : s.betaDeltaChiVariedAsResponseProduct)
    (hBetaNoForce : s.betaResponseProductHasNoLocalRadionForce)
    (hRejectConst : s.betaConstantBranchRejectedForNoFit)
    (hKick : s.sourceKickFormulaEncoded) :
    boundarySourceKickStructured s := by
  exact And.intro hVar
    (And.intro hLambda
      (And.intro hKappa
        (And.intro hBetaProduct
          (And.intro hBetaNoForce
            (And.intro hRejectConst hKick)))))

theorem missing_orientation_blocks_numeric_kick
    (s : RadionBoundarySourceKick)
    (hMissing : Not s.orientationConventionFixed) :
    Not (radionNoFitBackgroundReady s) := by
  intro h
  exact hMissing h.right.left

theorem missing_bulk_potential_still_blocks_no_fit_omegaT
    (s : RadionBoundarySourceKick)
    (hMissing : Not s.bulkPotentialFixedFromJanusAction) :
    Not (radionNoFitBackgroundReady s) := by
  intro h
  exact hMissing h.right.right.left

theorem no_fit_background_ready_after_source_orientation_and_potential
    (s : RadionBoundarySourceKick)
    (hSource : boundarySourceKickStructured s)
    (hOrient : s.orientationConventionFixed)
    (hPotential : s.bulkPotentialFixedFromJanusAction)
    (hOmega : s.omegaTNoFitReady) :
    radionNoFitBackgroundReady s := by
  exact And.intro hSource (And.intro hOrient (And.intro hPotential hOmega))

end P0EFTRadionBoundarySourceKick
end JanusFormal
