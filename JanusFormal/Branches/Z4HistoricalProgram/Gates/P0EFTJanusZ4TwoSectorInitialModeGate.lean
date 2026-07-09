import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TwoSectorConservationBianchiGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorInitialModeGate

set_option autoImplicit false

structure TwoSectorInitialModeGate where
  conservationBianchiGatePassed : Prop
  modeBasisDeclared : Prop
  modeIndependencePassed : Prop
  plusAdiabaticModeDeclared : Prop
  minusAdiabaticModeDeclared : Prop
  symmetricTwoSectorModeDeclared : Prop
  antisymmetricZ4ModeDeclared : Prop
  relativeIsocurvatureModeDeclared : Prop
  projectionModeDeclared : Prop
  modeNormalizationDeclared : Prop
  superhorizonRegular : Prop
  constraintCompatibleModes : Prop
  bianchiCompatibleInitialConditions : Prop
  projectionConsistentInitialConditions : Prop
  gaugeConventionDeclared : Prop
  grLimitModeRecovered : Prop
  grLimitPlusModeMatchesStandard : Prop
  minusSectorModeNotCollapsedIntoRhoEff : Prop
  standardCambAdiabaticForcingForbidden : Prop
  singleSectorAdiabaticOnly : Prop
  rhoEffInitialCondition : Prop
  hiddenSectorForcedToPlusSector : Prop
  arbitraryRelativeIsocurvatureAmplitude : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def initialModesReady (g : TwoSectorInitialModeGate) : Prop :=
  g.conservationBianchiGatePassed /\
  g.modeBasisDeclared /\
  g.modeIndependencePassed /\
  g.plusAdiabaticModeDeclared /\
  g.minusAdiabaticModeDeclared /\
  g.symmetricTwoSectorModeDeclared /\
  g.antisymmetricZ4ModeDeclared /\
  g.relativeIsocurvatureModeDeclared /\
  g.projectionModeDeclared /\
  g.modeNormalizationDeclared /\
  g.superhorizonRegular /\
  g.constraintCompatibleModes /\
  g.bianchiCompatibleInitialConditions /\
  g.projectionConsistentInitialConditions /\
  g.gaugeConventionDeclared /\
  g.grLimitModeRecovered /\
  g.grLimitPlusModeMatchesStandard /\
  g.minusSectorModeNotCollapsedIntoRhoEff /\
  g.standardCambAdiabaticForcingForbidden /\
  Not g.singleSectorAdiabaticOnly /\
  Not g.rhoEffInitialCondition /\
  Not g.hiddenSectorForcedToPlusSector /\
  Not g.arbitraryRelativeIsocurvatureAmplitude /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem two_sector_initial_modes_block_single_camb_mode
    (g : TwoSectorInitialModeGate)
    (hPolicy : initialModesReady g -> g.gatePassed)
    (h : initialModesReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorInitialModeGate
end JanusFormal
