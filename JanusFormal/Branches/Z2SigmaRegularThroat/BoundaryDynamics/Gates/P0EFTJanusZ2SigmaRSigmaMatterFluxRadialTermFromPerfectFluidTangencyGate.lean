namespace JanusFormal
namespace P0EFTJanusZ2SigmaRSigmaMatterFluxRadialTermFromPerfectFluidTangencyGate

set_option autoImplicit false

structure RSigmaMatterFluxRadialTermFromPerfectFluidTangencyGate where
  perfectFluidTangentialFluxZeroReady : Prop
  aGridReady : Prop
  activeSigmaTransparencyClaimed : Prop
  eMatterFluxZeroFromPerfectFluidTangencyWritten : Prop
  observationalFitForbidden : Prop

def ready (g : RSigmaMatterFluxRadialTermFromPerfectFluidTangencyGate) : Prop :=
  g.perfectFluidTangentialFluxZeroReady /\
  g.aGridReady /\
  Not g.activeSigmaTransparencyClaimed /\
  g.eMatterFluxZeroFromPerfectFluidTangencyWritten /\
  g.observationalFitForbidden

theorem ready_does_not_claim_full_transparency
    (g : RSigmaMatterFluxRadialTermFromPerfectFluidTangencyGate)
    (h : ready g) :
    Not g.activeSigmaTransparencyClaimed := by
  exact h.2.2.1

end P0EFTJanusZ2SigmaRSigmaMatterFluxRadialTermFromPerfectFluidTangencyGate
end JanusFormal
