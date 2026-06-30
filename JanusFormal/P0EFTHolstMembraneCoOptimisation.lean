namespace JanusFormal
namespace P0EFTHolstMembraneCoOptimisation

set_option autoImplicit false

structure HolstMembraneCoOptimisation where
  etaGridScored : Prop
  zSigmaGridScored : Prop
  physicalNodesFound : Prop
  acceptedNodeFound : Prop
  zSigmaDerivedGeometrically : Prop
  etaHolstDerivedGeometrically : Prop

def coOptimisationComputed (c : HolstMembraneCoOptimisation) : Prop :=
  c.etaGridScored /\ c.zSigmaGridScored /\ c.physicalNodesFound

def coOptimisedNoFitReady (c : HolstMembraneCoOptimisation) : Prop :=
  coOptimisationComputed c /\
  c.acceptedNodeFound /\
  c.zSigmaDerivedGeometrically /\
  c.etaHolstDerivedGeometrically

theorem holst_membrane_co_optimisation_is_computed
    (c : HolstMembraneCoOptimisation)
    (hEta : c.etaGridScored)
    (hZ : c.zSigmaGridScored)
    (hPhysical : c.physicalNodesFound) :
    coOptimisationComputed c := by
  exact And.intro hEta (And.intro hZ hPhysical)

theorem missing_geometric_zsigma_blocks_no_fit
    (c : HolstMembraneCoOptimisation)
    (hMissing : Not c.zSigmaDerivedGeometrically) :
    Not (coOptimisedNoFitReady c) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTHolstMembraneCoOptimisation
end JanusFormal
