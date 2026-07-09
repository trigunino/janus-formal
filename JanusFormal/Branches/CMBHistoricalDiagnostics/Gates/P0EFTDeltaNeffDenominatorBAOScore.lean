namespace JanusFormal
namespace P0EFTDeltaNeffDenominatorBAOScore

set_option autoImplicit false

structure DeltaNeffDenominatorBAOScore where
  denominatorCandidatesScored : Prop
  denominatorFortyEightPassesBAOGate : Prop
  denominatorFortyEightDerived : Prop

def denominatorBAODiagnosticReady (d : DeltaNeffDenominatorBAOScore) : Prop :=
  d.denominatorCandidatesScored /\
  d.denominatorFortyEightPassesBAOGate

def denominatorBAONoFitReady (d : DeltaNeffDenominatorBAOScore) : Prop :=
  denominatorBAODiagnosticReady d /\
  d.denominatorFortyEightDerived

theorem denominator_48_can_be_used_as_derivation_target
    (d : DeltaNeffDenominatorBAOScore)
    (hScored : d.denominatorCandidatesScored)
    (hPass : d.denominatorFortyEightPassesBAOGate) :
    denominatorBAODiagnosticReady d := by
  exact And.intro hScored hPass

theorem missing_denominator_48_derivation_blocks_no_fit
    (d : DeltaNeffDenominatorBAOScore)
    (hMissing : Not d.denominatorFortyEightDerived) :
    Not (denominatorBAONoFitReady d) := by
  intro h
  exact hMissing h.right

end P0EFTDeltaNeffDenominatorBAOScore
end JanusFormal
