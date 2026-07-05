import JanusFormal.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermSymbolicLocalPrimitiveGate

set_option autoImplicit false

structure CountertermSymbolicLocalPrimitiveGate where
  sigmaNonlinearResidualClosureImported : Prop
  localDensityBasisImported : Prop
  fieldSpacePrimitiveFormulaDeclared : Prop
  noRadialValueClaimed : Prop
  noFittedCountertermCoefficient : Prop
  sigmaFullBoundaryActionClosed : Prop
  localDensityBasisComplete : Prop
  symbolicPrimitiveExists : Prop
  coefficientExpansionExplicit : Prop
  radialProfileReady : Prop

def symbolicLocalPrimitiveReady
    (g : CountertermSymbolicLocalPrimitiveGate) : Prop :=
  g.sigmaNonlinearResidualClosureImported /\
  g.localDensityBasisImported /\
  g.fieldSpacePrimitiveFormulaDeclared /\
  g.noRadialValueClaimed /\
  g.noFittedCountertermCoefficient /\
  g.sigmaFullBoundaryActionClosed /\
  g.localDensityBasisComplete /\
  g.symbolicPrimitiveExists

def radialProfileUsable
    (g : CountertermSymbolicLocalPrimitiveGate) : Prop :=
  symbolicLocalPrimitiveReady g /\
  g.coefficientExpansionExplicit /\
  g.radialProfileReady

theorem symbolic_ready_gives_primitive
    (g : CountertermSymbolicLocalPrimitiveGate)
    (hReady : symbolicLocalPrimitiveReady g) :
    g.symbolicPrimitiveExists := by
  exact hReady.2.2.2.2.2.2.2

theorem missing_coefficient_expansion_blocks_radial_profile_use
    (g : CountertermSymbolicLocalPrimitiveGate)
    (hMissing : Not g.coefficientExpansionExplicit) :
    Not (radialProfileUsable g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusZ2SigmaCountertermSymbolicLocalPrimitiveGate
end JanusFormal
