import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4CobayaPlanckChannelGate

namespace JanusFormal
namespace P0EFTJanusZ4ShapeDiagnostic

set_option autoImplicit false

structure ShapeDiagnostic where
  nativeZ4ProviderUsed : Prop
  compressedLCDMParametersNotUsed : Prop
  lowTTBandDeclared : Prop
  lowEBandDeclared : Prop
  highlTTBandDeclared : Prop
  highlTEEEBandsDeclared : Prop
  lensingBandDeclared : Prop
  officialPlanckLikelihoodNotClaimed : Prop

def shapeDiagnosticReady (d : ShapeDiagnostic) : Prop :=
  d.nativeZ4ProviderUsed /\
  d.compressedLCDMParametersNotUsed /\
  d.lowTTBandDeclared /\
  d.lowEBandDeclared /\
  d.highlTTBandDeclared /\
  d.highlTEEEBandsDeclared /\
  d.lensingBandDeclared /\
  d.officialPlanckLikelihoodNotClaimed

theorem shape_diagnostic_is_not_planck_verdict
    (d : ShapeDiagnostic)
    (h : shapeDiagnosticReady d) :
    d.officialPlanckLikelihoodNotClaimed := by
  exact h.right.right.right.right.right.right.right

end P0EFTJanusZ4ShapeDiagnostic
end JanusFormal
