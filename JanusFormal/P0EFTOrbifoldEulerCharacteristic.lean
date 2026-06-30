import JanusFormal.P0EFTOrbifoldVolumeDerivation

namespace JanusFormal
namespace P0EFTOrbifoldEulerCharacteristic

set_option autoImplicit false

structure OrbifoldEulerCharacteristic where
  asymmetricGaugeComplexDefined : Prop
  inducedSurfaceMetricDefined : Prop
  z2CoverProjectionDefined : Prop
  branchLocusMultiplicityComputed : Prop
  positiveSheetMultiplicityTwo : Prop
  negativeSheetMultiplicityOne : Prop

def coverMultiplicityTwoToOne (e : OrbifoldEulerCharacteristic) : Prop :=
  e.z2CoverProjectionDefined /\
  e.branchLocusMultiplicityComputed /\
  e.positiveSheetMultiplicityTwo /\
  e.negativeSheetMultiplicityOne

def eulerCoverDataClosed (e : OrbifoldEulerCharacteristic) : Prop :=
  e.asymmetricGaugeComplexDefined /\
  e.inducedSurfaceMetricDefined /\
  coverMultiplicityTwoToOne e

theorem cover_multiplicity_derives_volume_ratio_input
    (e : OrbifoldEulerCharacteristic)
    (d : P0EFTOrbifoldVolumeDerivation.OrbifoldVolumeDerivation)
    (_hEuler : eulerCoverDataClosed e)
    (hQuotient : d.quotientM5ByZ2Defined)
    (hMembrane : d.janusMembraneFixedSetRegular)
    (hFlux : d.spinConnectionFluxQuantized)
    (hEulerClass : d.eulerSurfaceClassComputed)
    (hMultiplicity : d.asymmetricSheetMultiplicityTwoToOne) :
    P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived d := by
  unfold P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived
  unfold P0EFTOrbifoldVolumeDerivation.orbifoldTopologicalDataClosed
  exact And.intro
    (And.intro hQuotient (And.intro hMembrane (And.intro hFlux hEulerClass)))
    hMultiplicity

theorem missing_branch_multiplicity_blocks_cover_data
    (e : OrbifoldEulerCharacteristic)
    (hMissing : Not e.branchLocusMultiplicityComputed) :
    Not (eulerCoverDataClosed e) := by
  intro h
  rcases h with ⟨_, _, hCover⟩
  rcases hCover with ⟨_, hBranch, _, _⟩
  exact hMissing hBranch

theorem missing_positive_sheet_two_blocks_cover_ratio
    (e : OrbifoldEulerCharacteristic)
    (hMissing : Not e.positiveSheetMultiplicityTwo) :
    Not (coverMultiplicityTwoToOne e) := by
  intro h
  rcases h with ⟨_, _, hPositive, _⟩
  exact hMissing hPositive

end P0EFTOrbifoldEulerCharacteristic
end JanusFormal
