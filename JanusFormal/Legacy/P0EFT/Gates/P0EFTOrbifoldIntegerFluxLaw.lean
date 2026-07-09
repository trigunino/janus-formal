import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldFluxIntegerTheorem
import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldNormalizedFluxInteger

namespace JanusFormal
namespace P0EFTOrbifoldIntegerFluxLaw

set_option autoImplicit false

structure IntegerFluxLaw where
  singularCycleDefined : Prop
  normalizedFluxIntegerAvailable : Prop
  z2HolonomyPeriodInteger : Prop

def integerFluxLawDerived (l : IntegerFluxLaw) : Prop :=
  l.singularCycleDefined /\
  l.normalizedFluxIntegerAvailable /\
  l.z2HolonomyPeriodInteger

theorem integer_flux_law_supplies_integer_flux_data
    (l : IntegerFluxLaw)
    (t : P0EFTOrbifoldFluxIntegerTheorem.OrbifoldFluxIntegerTheorem)
    (_hLaw : integerFluxLawDerived l)
    (hCycle : t.singularCycleDefined)
    (hFlux : t.normalizedSpinConnectionFluxDefined)
    (hInteger : t.integerFluxLawProved) :
    P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed t := by
  unfold P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed
  exact And.intro hCycle (And.intro hFlux hInteger)

theorem missing_z2_period_blocks_integer_flux_law
    (l : IntegerFluxLaw)
    (hMissing : Not l.z2HolonomyPeriodInteger) :
    Not (integerFluxLawDerived l) := by
  intro h
  exact hMissing h.right.right

end P0EFTOrbifoldIntegerFluxLaw
end JanusFormal
