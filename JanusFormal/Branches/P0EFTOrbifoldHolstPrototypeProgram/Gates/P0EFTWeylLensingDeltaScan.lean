namespace JanusFormal
namespace P0EFTWeylLensingDeltaScan

set_option autoImplicit false

structure WeylLensingDeltaScan where
  rawPlanckLikelihoodUsed : Prop
  deltaChi2Calibrated : Prop
  acceptedDeltaPointFound : Prop
  weylLensingFactorsDerived : Prop

def deltaWindowOpen (s : WeylLensingDeltaScan) : Prop :=
  s.rawPlanckLikelihoodUsed /\
  s.deltaChi2Calibrated /\
  s.acceptedDeltaPointFound

def weylLensingNoFitReady (s : WeylLensingDeltaScan) : Prop :=
  deltaWindowOpen s /\
  s.weylLensingFactorsDerived

theorem accepted_delta_still_needs_geometric_derivation
    (s : WeylLensingDeltaScan)
    (_hOpen : deltaWindowOpen s)
    (hMissing : Not s.weylLensingFactorsDerived) :
    Not (weylLensingNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTWeylLensingDeltaScan
end JanusFormal
