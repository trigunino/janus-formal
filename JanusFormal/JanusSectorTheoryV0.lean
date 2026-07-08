import JanusFormal.P0EFTJanusSectorTheoryV0Gate

namespace JanusFormal
namespace JanusSectorTheoryV0

set_option autoImplicit false

structure Status where
  matrixBuilt : Prop
  observationSmokeTested : Prop
  alphaPredictedNoFit : Prop

def usefulButNotClosed (s : Status) : Prop :=
  s.matrixBuilt /\ s.observationSmokeTested /\ Not s.alphaPredictedNoFit

theorem sector_v0_still_requires_state_law
    (s : Status)
    (h : usefulButNotClosed s) :
    Not s.alphaPredictedNoFit := by
  exact h.right.right

end JanusSectorTheoryV0
end JanusFormal
