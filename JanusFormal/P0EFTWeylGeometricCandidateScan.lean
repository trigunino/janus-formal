namespace JanusFormal
namespace P0EFTWeylGeometricCandidateScan

set_option autoImplicit false

structure WeylGeometricCandidateScan where
  rationalCandidatesRun : Prop
  oneOverThirtySixTested : Prop
  oneOverThirtySixViable : Prop
  oneOverThirtySixDerived : Prop

def geometricCandidateWindowOpen (s : WeylGeometricCandidateScan) : Prop :=
  s.rationalCandidatesRun /\
  s.oneOverThirtySixTested /\
  s.oneOverThirtySixViable

def noFitWeylCandidateReady (s : WeylGeometricCandidateScan) : Prop :=
  geometricCandidateWindowOpen s /\
  s.oneOverThirtySixDerived

theorem viable_candidate_still_needs_derivation
    (s : WeylGeometricCandidateScan)
    (_hOpen : geometricCandidateWindowOpen s)
    (hMissing : Not s.oneOverThirtySixDerived) :
    Not (noFitWeylCandidateReady s) := by
  intro h
  exact hMissing h.right

theorem rejected_one_over_thirty_six_blocks_no_fit
    (s : WeylGeometricCandidateScan)
    (hRejected : Not s.oneOverThirtySixViable) :
    Not (noFitWeylCandidateReady s) := by
  intro h
  exact hRejected h.left.right.right

end P0EFTWeylGeometricCandidateScan
end JanusFormal
