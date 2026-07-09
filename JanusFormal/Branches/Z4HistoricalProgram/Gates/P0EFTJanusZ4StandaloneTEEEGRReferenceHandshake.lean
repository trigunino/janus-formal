import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4StandaloneTEEEHandshakeGate

namespace JanusFormal
namespace P0EFTJanusZ4StandaloneTEEEGRReferenceHandshake

set_option autoImplicit false

structure GRReferenceHandshake where
  clVsDlConventionChecked : Prop
  unitsChecked : Prop
  teSignChecked : Prop
  ellIndexingChecked : Prop
  nuisanceVectorChecked : Prop
  foregroundHandlingChecked : Prop
  grReferenceSanityChecked : Prop
  frozenCandidateNotEvaluated : Prop
  highlDecompositionTrialAllowedAfterReport : Prop

def passed (g : GRReferenceHandshake) : Prop :=
  g.clVsDlConventionChecked /\
  g.unitsChecked /\
  g.teSignChecked /\
  g.ellIndexingChecked /\
  g.nuisanceVectorChecked /\
  g.foregroundHandlingChecked /\
  g.grReferenceSanityChecked /\
  g.frozenCandidateNotEvaluated

theorem passed_allows_highl_decomposition_trial
    (g : GRReferenceHandshake)
    (hPolicy : passed g -> g.highlDecompositionTrialAllowedAfterReport)
    (h : passed g) :
    g.highlDecompositionTrialAllowedAfterReport := by
  exact hPolicy h

end P0EFTJanusZ4StandaloneTEEEGRReferenceHandshake
end JanusFormal
