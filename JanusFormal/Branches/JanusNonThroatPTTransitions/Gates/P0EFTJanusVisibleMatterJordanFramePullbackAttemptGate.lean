namespace JanusFormal
namespace P0EFTJanusVisibleMatterJordanFramePullbackAttemptGate

set_option autoImplicit false

structure VisibleMatterJordanFramePullbackAttemptGate where
  PositiveSectorGeodesicRuleAvailable : Prop
  VisiblePhotonsFollowGPlus : Prop
  VisibleMatterClockFixedByGPlus : Prop
  WeylGaugeFixedForVisibleObservers : Prop
  GPlusPullbackToWeylCuspDerived : Prop
  OmegaEvolutionFromBimetricEquationsDerived : Prop
  RedshiftMapThroughPTBoundaryDerived : Prop

def VisibleClockFixed
    (g : VisibleMatterJordanFramePullbackAttemptGate) : Prop :=
  g.PositiveSectorGeodesicRuleAvailable /\
  g.VisiblePhotonsFollowGPlus /\
  g.VisibleMatterClockFixedByGPlus /\
  g.WeylGaugeFixedForVisibleObservers

def VisibleJordanCuspPredictive
    (g : VisibleMatterJordanFramePullbackAttemptGate) : Prop :=
  VisibleClockFixed g /\
  g.GPlusPullbackToWeylCuspDerived /\
  g.OmegaEvolutionFromBimetricEquationsDerived /\
  g.RedshiftMapThroughPTBoundaryDerived

def VisibleJordanCuspFrontier
    (g : VisibleMatterJordanFramePullbackAttemptGate) : Prop :=
  VisibleClockFixed g /\
  Not g.GPlusPullbackToWeylCuspDerived /\
  Not g.OmegaEvolutionFromBimetricEquationsDerived /\
  Not g.RedshiftMapThroughPTBoundaryDerived

theorem visible_clock_fixed_still_needs_cusp_pullback
    (g : VisibleMatterJordanFramePullbackAttemptGate)
    (hFrontier : VisibleJordanCuspFrontier g) :
    Not (VisibleJordanCuspPredictive g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusVisibleMatterJordanFramePullbackAttemptGate
end JanusFormal
