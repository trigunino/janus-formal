import JanusFormal.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.P0EFTJanusZ2SigmaBoundaryStressExtractionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermFLRWObligationGate

set_option autoImplicit false

structure CountertermFLRWObligationGate where
  boundaryCountertermBibliographyChecked : Prop
  sigmaSupportedCountertermUnique : Prop
  countertermVariationCancelsResidual : Prop
  countertermActionDensityDeclared : Prop
  inducedMetricVariationDeclared : Prop
  z2OrientationSignDeclared : Prop
  countertermStressFormulaReady : Prop
  countertermFLRWStressReduced : Prop
  countertermRhoPOfAReady : Prop

def countertermMethodReady
    (g : CountertermFLRWObligationGate) : Prop :=
  g.boundaryCountertermBibliographyChecked /\
  g.sigmaSupportedCountertermUnique /\
  g.countertermVariationCancelsResidual /\
  g.countertermActionDensityDeclared /\
  g.inducedMetricVariationDeclared /\
  g.z2OrientationSignDeclared /\
  g.countertermStressFormulaReady

def countertermFLRWClosureReady
    (g : CountertermFLRWObligationGate) : Prop :=
  countertermMethodReady g /\
  g.countertermFLRWStressReduced /\
  g.countertermRhoPOfAReady

theorem counterterm_closure_requires_flrw_stress_reduction
    (g : CountertermFLRWObligationGate)
    (hReady : countertermFLRWClosureReady g) :
    g.countertermFLRWStressReduced := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCountertermFLRWObligationGate
end JanusFormal
