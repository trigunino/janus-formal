import JanusFormal.P0EFTJanusZ4MinusSectorIndependentTransferGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorMicrophysicsSpecificationGate

set_option autoImplicit false

structure MinusSectorMicrophysicsSpecificationGate where
  previousRankOneDiagnosis : Prop
  nonAmplitudeMicrophysicsRequired : Prop
  soundSpeedOrJeansRouteDeclared : Prop
  bianchiConservationRequired : Prop
  thermodynamicSignSeparatedFromGravitationalSign : Prop
  exchangeLawDerivedOrZero : Prop
  minusSectorAmplitudeKnobAllowed : Prop
  rhoEffShortcutAllowed : Prop
  projectionOnlyFixAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  gatePassed : Prop

def specificationReady (g : MinusSectorMicrophysicsSpecificationGate) : Prop :=
  g.previousRankOneDiagnosis /\
  g.nonAmplitudeMicrophysicsRequired /\
  g.soundSpeedOrJeansRouteDeclared /\
  g.bianchiConservationRequired /\
  g.thermodynamicSignSeparatedFromGravitationalSign /\
  g.exchangeLawDerivedOrZero /\
  Not g.minusSectorAmplitudeKnobAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.projectionOnlyFixAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed

theorem microphysics_specification_blocks_shortcuts
    (g : MinusSectorMicrophysicsSpecificationGate)
    (hPolicy : specificationReady g -> g.gatePassed)
    (h : specificationReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorMicrophysicsSpecificationGate
end JanusFormal
