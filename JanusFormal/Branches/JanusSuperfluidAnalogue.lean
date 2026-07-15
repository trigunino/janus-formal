import JanusFormal.Branches.JanusSuperfluidAnalogue.Gates.P0EFTJanusSF01InteractionStability
import JanusFormal.Branches.JanusSuperfluidAnalogue.Gates.P0EFTJanusSF02SF03Bogoliubov
import JanusFormal.Branches.JanusSuperfluidAnalogue.Gates.P0EFTJanusSF04Scattering

namespace JanusFormal
namespace JanusSuperfluidAnalogue

structure ProgramStatus where
  sf01StableBackground : Prop
  sf02InterfaceAndHealingScales : Prop
  sf03BogoliubovSpectrum : Prop
  sf04FluxConservingScattering : Prop
  fundamentalJanusEquivalence : Prop

def analogueProgramClosed (s : ProgramStatus) : Prop :=
  s.sf01StableBackground ∧
  s.sf02InterfaceAndHealingScales ∧
  s.sf03BogoliubovSpectrum ∧
  s.sf04FluxConservingScattering

end JanusSuperfluidAnalogue
end JanusFormal
