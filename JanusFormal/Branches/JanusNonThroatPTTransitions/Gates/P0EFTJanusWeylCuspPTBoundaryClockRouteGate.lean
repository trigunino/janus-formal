namespace JanusFormal
namespace P0EFTJanusWeylCuspPTBoundaryClockRouteGate

set_option autoImplicit false

structure WeylCuspPTBoundaryClockRouteGate where
  FiniteSigmaRadiusRemoved : Prop
  PhysicalVolumeCanVanish : Prop
  ConformalBoundaryDataFinite : Prop
  PreDragRedshiftDomainAvailable : Prop
  LateCoshZmaxObstructionRemoved : Prop
  WeylGaugeFixedByActionOrMatterClock : Prop
  PhysicalClockLawDerived : Prop
  ConformalFriedmannEquationDerived : Prop
  LateSNMatchingLawDerived : Prop

def WeylCuspDomainSolved
    (g : WeylCuspPTBoundaryClockRouteGate) : Prop :=
  g.FiniteSigmaRadiusRemoved /\
  g.PhysicalVolumeCanVanish /\
  g.ConformalBoundaryDataFinite /\
  g.PreDragRedshiftDomainAvailable /\
  g.LateCoshZmaxObstructionRemoved

def WeylCuspPredictiveClosed
    (g : WeylCuspPTBoundaryClockRouteGate) : Prop :=
  WeylCuspDomainSolved g /\
  g.WeylGaugeFixedByActionOrMatterClock /\
  g.PhysicalClockLawDerived /\
  g.ConformalFriedmannEquationDerived /\
  g.LateSNMatchingLawDerived

def WeylCuspFrontier
    (g : WeylCuspPTBoundaryClockRouteGate) : Prop :=
  WeylCuspDomainSolved g /\
  Not g.WeylGaugeFixedByActionOrMatterClock /\
  Not g.PhysicalClockLawDerived /\
  Not g.ConformalFriedmannEquationDerived /\
  Not g.LateSNMatchingLawDerived

theorem weyl_cusp_solves_domain_but_not_predictive_clock
    (g : WeylCuspPTBoundaryClockRouteGate)
    (hFrontier : WeylCuspFrontier g) :
    Not (WeylCuspPredictiveClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusWeylCuspPTBoundaryClockRouteGate
end JanusFormal
