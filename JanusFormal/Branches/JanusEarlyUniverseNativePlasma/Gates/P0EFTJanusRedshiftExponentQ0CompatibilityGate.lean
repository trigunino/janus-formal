namespace JanusFormal
namespace P0EFTJanusRedshiftExponentQ0CompatibilityGate

set_option autoImplicit false

structure RedshiftExponentQ0CompatibilityGate where
  targetRedshiftDeclared : Prop
  q0PublishedBandDeclared : Prop
  lowPowerMapsForceQ0NearZero : Prop
  occupationVolumeMapOutsideBand : Prop
  fourPowerMapClosestToPublishedBand : Prop
  fourPowerMapNotDerived : Prop
  sourceDerivedRedshiftRequiredBeforeObservation : Prop

def redshiftQ0CompatibilityReady
    (g : RedshiftExponentQ0CompatibilityGate) : Prop :=
  g.targetRedshiftDeclared /\
  g.q0PublishedBandDeclared /\
  g.lowPowerMapsForceQ0NearZero /\
  g.occupationVolumeMapOutsideBand /\
  g.fourPowerMapClosestToPublishedBand /\
  g.fourPowerMapNotDerived /\
  g.sourceDerivedRedshiftRequiredBeforeObservation

theorem q0_compatibility_points_to_derived_four_power_or_new_branch
    (g : RedshiftExponentQ0CompatibilityGate)
    (hReady : redshiftQ0CompatibilityReady g) :
    g.fourPowerMapClosestToPublishedBand /\
      g.sourceDerivedRedshiftRequiredBeforeObservation := by
  exact And.intro hReady.2.2.2.2.1 hReady.2.2.2.2.2.2

end P0EFTJanusRedshiftExponentQ0CompatibilityGate
end JanusFormal
