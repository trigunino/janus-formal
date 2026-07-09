import JanusFormal.Legacy.P0EFT.Gates.P0EFTOrbifoldVolumeCoverClassification

namespace JanusFormal
namespace P0EFTOrbifoldVolumeDerivation

set_option autoImplicit false

structure OrbifoldVolumeDerivation where
  quotientM5ByZ2Defined : Prop
  janusMembraneFixedSetRegular : Prop
  spinConnectionFluxQuantized : Prop
  eulerSurfaceClassComputed : Prop
  asymmetricSheetMultiplicityTwoToOne : Prop

def orbifoldTopologicalDataClosed (d : OrbifoldVolumeDerivation) : Prop :=
  d.quotientM5ByZ2Defined /\
  d.janusMembraneFixedSetRegular /\
  d.spinConnectionFluxQuantized /\
  d.eulerSurfaceClassComputed

def orbifoldVolumeRatioTwoToOneDerived (d : OrbifoldVolumeDerivation) : Prop :=
  orbifoldTopologicalDataClosed d /\ d.asymmetricSheetMultiplicityTwoToOne

theorem orbifold_topology_derives_cover_classification
    (d : OrbifoldVolumeDerivation)
    (c : P0EFTOrbifoldVolumeCoverClassification.OrbifoldVolumeCoverClassification)
    (_hDer : orbifoldVolumeRatioTwoToOneDerived d)
    (hZ2 : c.janusZ2CoverDefined)
    (hMembrane : c.membraneFixedSetDefined)
    (hEuler : c.globalEulerHolonomyClassComputed)
    (hRatio : c.volumeCoverRatioTwoToOne) :
    P0EFTOrbifoldVolumeCoverClassification.globalCoverRatioDerived c := by
  unfold P0EFTOrbifoldVolumeCoverClassification.globalCoverRatioDerived
  exact And.intro hZ2 (And.intro hMembrane (And.intro hEuler hRatio))

theorem missing_flux_quantization_blocks_volume_ratio
    (d : OrbifoldVolumeDerivation)
    (hMissing : Not d.spinConnectionFluxQuantized) :
    Not (orbifoldVolumeRatioTwoToOneDerived d) := by
  intro h
  exact hMissing h.left.right.right.left

theorem missing_sheet_multiplicity_blocks_volume_ratio
    (d : OrbifoldVolumeDerivation)
    (hMissing : Not d.asymmetricSheetMultiplicityTwoToOne) :
    Not (orbifoldVolumeRatioTwoToOneDerived d) := by
  intro h
  exact hMissing h.right

end P0EFTOrbifoldVolumeDerivation
end JanusFormal
