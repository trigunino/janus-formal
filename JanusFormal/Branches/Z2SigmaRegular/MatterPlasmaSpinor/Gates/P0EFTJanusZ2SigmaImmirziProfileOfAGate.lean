import JanusFormal.Basic
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaImmirziProfileOfAGate

set_option autoImplicit false

structure ImmirziProfileOfAGate where
  immirziBibliographyChecked : Prop
  barberoImmirziScalarFieldImported : Prop
  niehYanCouplingImported : Prop
  immirziBulkBoundaryEquationGateDeclared : Prop
  sigmaBoundaryConditionRequired : Prop
  activeHolstNiehYanVariationRequired : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  bulkImmirziEquationReady : Prop
  sigmaBoundaryConditionReady : Prop
  plusImmirziProfileOfAReady : Prop
  minusImmirziProfileOfAReady : Prop
  projectedImmirziProfileOfAReady : Prop
  immirziProfileOfAReady : Prop

def immirziProfileLedgerDeclared
    (g : ImmirziProfileOfAGate) : Prop :=
  g.immirziBibliographyChecked /\
  g.barberoImmirziScalarFieldImported /\
  g.niehYanCouplingImported /\
  g.immirziBulkBoundaryEquationGateDeclared /\
  g.sigmaBoundaryConditionRequired /\
  g.activeHolstNiehYanVariationRequired /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def immirziProfileReady
    (g : ImmirziProfileOfAGate) : Prop :=
  immirziProfileLedgerDeclared g /\
  g.bulkImmirziEquationReady /\
  g.sigmaBoundaryConditionReady /\
  g.plusImmirziProfileOfAReady /\
  g.minusImmirziProfileOfAReady /\
  g.projectedImmirziProfileOfAReady /\
  g.immirziProfileOfAReady

theorem immirzi_profile_requires_bulk_and_sigma_boundary
    (g : ImmirziProfileOfAGate)
    (hReady : immirziProfileReady g) :
    g.bulkImmirziEquationReady /\ g.sigmaBoundaryConditionReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaImmirziProfileOfAGate
end JanusFormal
