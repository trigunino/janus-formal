namespace JanusFormal
namespace P0EFTJanusAlphaSuperselectionSectorProgramGate

set_option autoImplicit false

structure AlphaSuperselectionProgramGate where
  alphaDeclaredGlobalStateSector : Prop
  noTopologyAlphaPredictionClaim : Prop
  observationalCalibrationAllowed : Prop
  noFitClaimForbidden : Prop
  snBaoEndpointDeclared : Prop
  fullProgramClosedAsSectorTheory : Prop

def honestSectorProgramReady (g : AlphaSuperselectionProgramGate) : Prop :=
  g.alphaDeclaredGlobalStateSector /\
  g.noTopologyAlphaPredictionClaim /\
  g.observationalCalibrationAllowed /\
  g.noFitClaimForbidden /\
  g.snBaoEndpointDeclared /\
  g.fullProgramClosedAsSectorTheory

theorem sector_program_is_not_no_fit_prediction
    (g : AlphaSuperselectionProgramGate)
    (h : honestSectorProgramReady g) :
    g.noFitClaimForbidden := by
  exact h.right.right.right.left

end P0EFTJanusAlphaSuperselectionSectorProgramGate
end JanusFormal
