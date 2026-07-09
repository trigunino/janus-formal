namespace JanusFormal
namespace P0EFTJanusAdiabaticRadiationFirstLawGate

set_option autoImplicit false

structure AdiabaticRadiationFirstLawGate where
  plusSectorPhotonStressConserved : Prop
  radiationTracefree : Prop
  visibleVolumeScalesAsA3 : Prop
  eq40HcScalesAsA : Prop
  thermalEnergyTemperatureScalesAsAminus1 : Prop
  occupationExponentA3Derived : Prop
  promotedAsUnconditional : Prop

def conditionalOccupationClosure (g : AdiabaticRadiationFirstLawGate) : Prop :=
  g.plusSectorPhotonStressConserved /\
  g.radiationTracefree /\
  g.visibleVolumeScalesAsA3 /\
  g.eq40HcScalesAsA /\
  g.thermalEnergyTemperatureScalesAsAminus1 /\
  g.occupationExponentA3Derived /\
  Not g.promotedAsUnconditional

theorem first_law_closes_only_conditionally
    (g : AdiabaticRadiationFirstLawGate)
    (h : conditionalOccupationClosure g) :
    Not g.promotedAsUnconditional := by
  exact h.2.2.2.2.2.2

end P0EFTJanusAdiabaticRadiationFirstLawGate
end JanusFormal
