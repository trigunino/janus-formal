namespace JanusFormal
namespace P0EFTWeylLensingDeltaDecision

set_option autoImplicit false

structure WeylLensingDeltaDecision where
  totalDeltaWindowFound : Prop
  lensingClosedAtBestTotal : Prop
  balancedWindowFound : Prop
  geometricRelationDerived : Prop

def phenomenologyWindowOpen (d : WeylLensingDeltaDecision) : Prop :=
  d.totalDeltaWindowFound /\
  d.balancedWindowFound

def noFitWeylLensingReady (d : WeylLensingDeltaDecision) : Prop :=
  phenomenologyWindowOpen d /\
  d.lensingClosedAtBestTotal /\
  d.geometricRelationDerived

theorem geometric_relation_still_required
    (d : WeylLensingDeltaDecision)
    (_hOpen : phenomenologyWindowOpen d)
    (hMissing : Not d.geometricRelationDerived) :
    Not (noFitWeylLensingReady d) := by
  intro h
  exact hMissing h.right.right

end P0EFTWeylLensingDeltaDecision
end JanusFormal
