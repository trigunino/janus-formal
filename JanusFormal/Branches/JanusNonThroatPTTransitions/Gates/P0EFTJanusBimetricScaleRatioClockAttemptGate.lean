namespace JanusFormal
namespace P0EFTJanusBimetricScaleRatioClockAttemptGate

set_option autoImplicit false

structure BimetricScaleRatioClockAttemptGate where
  TwoScaleFactorsAvailable : Prop
  PublishedRatioSignalAvailable : Prop
  DeterminantRatioFieldEquationsAvailable : Prop
  OmegaDefinedAsBimetricRatio : Prop
  RatioEvolutionThroughPredragDerived : Prop
  RatioSelectsPhysicalVisibleClock : Prop

def BimetricRatioClockClosed
    (g : BimetricScaleRatioClockAttemptGate) : Prop :=
  g.TwoScaleFactorsAvailable /\
  g.PublishedRatioSignalAvailable /\
  g.DeterminantRatioFieldEquationsAvailable /\
  g.OmegaDefinedAsBimetricRatio /\
  g.RatioEvolutionThroughPredragDerived /\
  g.RatioSelectsPhysicalVisibleClock

def BimetricRatioClockFrontier
    (g : BimetricScaleRatioClockAttemptGate) : Prop :=
  g.TwoScaleFactorsAvailable /\
  g.PublishedRatioSignalAvailable /\
  g.DeterminantRatioFieldEquationsAvailable /\
  Not g.OmegaDefinedAsBimetricRatio /\
  Not g.RatioEvolutionThroughPredragDerived /\
  Not g.RatioSelectsPhysicalVisibleClock

theorem bimetric_ratio_inputs_do_not_define_clock
    (g : BimetricScaleRatioClockAttemptGate)
    (hFrontier : BimetricRatioClockFrontier g) :
    Not (BimetricRatioClockClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusBimetricScaleRatioClockAttemptGate
end JanusFormal
