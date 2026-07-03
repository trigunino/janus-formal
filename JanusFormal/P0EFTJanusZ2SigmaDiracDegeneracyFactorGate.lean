import JanusFormal.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate
import JanusFormal.P0EFTJanusZ2SigmaSpinorBundleProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaFermionRouteSelectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracDegeneracyFactorGate

set_option autoImplicit false

structure DiracDegeneracyFactorGate where
  spinDegeneracyBibliographyChecked : Prop
  diracInternalDegreesDeclared : Prop
  plusMinusSpinorBundleDataGateDeclared : Prop
  spinorBundleProjectionGateDeclared : Prop
  fermionRouteSelectionGateDeclared : Prop
  plusDegeneracyFactorDeclared : Prop
  minusDegeneracyFactorDeclared : Prop
  z2SigmaProjectedDegeneracyDeclared : Prop
  noDegeneracyFit : Prop
  observationalFitForbidden : Prop
  plusSpinorBundleReady : Prop
  minusSpinorBundleReady : Prop
  diracRouteSelected : Prop
  spinorProjectionReady : Prop
  plusDegeneracyFactorDerived : Prop
  minusDegeneracyFactorDerived : Prop
  projectedDegeneracyFactorReady : Prop

def diracDegeneracyFactorLedgerDeclared
    (g : DiracDegeneracyFactorGate) : Prop :=
  g.spinDegeneracyBibliographyChecked /\
  g.diracInternalDegreesDeclared /\
  g.plusMinusSpinorBundleDataGateDeclared /\
  g.spinorBundleProjectionGateDeclared /\
  g.fermionRouteSelectionGateDeclared /\
  g.plusDegeneracyFactorDeclared /\
  g.minusDegeneracyFactorDeclared /\
  g.z2SigmaProjectedDegeneracyDeclared /\
  g.noDegeneracyFit /\
  g.observationalFitForbidden

def diracDegeneracyFactorReady
    (g : DiracDegeneracyFactorGate) : Prop :=
  diracDegeneracyFactorLedgerDeclared g /\
  g.plusSpinorBundleReady /\
  g.minusSpinorBundleReady /\
  g.diracRouteSelected /\
  g.spinorProjectionReady /\
  g.plusDegeneracyFactorDerived /\
  g.minusDegeneracyFactorDerived /\
  g.projectedDegeneracyFactorReady

theorem degeneracy_factor_requires_spinor_bundles
    (g : DiracDegeneracyFactorGate)
    (hReady : diracDegeneracyFactorReady g) :
    g.plusSpinorBundleReady /\ g.minusSpinorBundleReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaDiracDegeneracyFactorGate
end JanusFormal
