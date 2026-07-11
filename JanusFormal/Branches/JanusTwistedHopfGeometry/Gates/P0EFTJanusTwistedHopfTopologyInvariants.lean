import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedHopfTopologyInvariants

set_option autoImplicit false

def topCellBoundary (n : ℤ) : ℤ := 2 * n

theorem top_cell_boundary_has_trivial_kernel
    (n : ℤ)
    (h : topCellBoundary n = 0) :
    n = 0 := by
  unfold topCellBoundary at h
  omega

theorem top_cell_boundary_image_iff_even
    (m : ℤ) :
    (∃ n : ℤ, topCellBoundary n = m) ↔ Even m := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by unfold topCellBoundary; ring⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold topCellBoundary
    nlinarith

def degreeThreeTorsionClass (n : ℤ) : ZMod 2 := n

@[simp] theorem twice_degree_three_class_vanishes
    (n : ℤ) :
    degreeThreeTorsionClass (2 * n) = 0 := by
  change (2 : ZMod 2) * (n : ZMod 2) = 0
  norm_num

def twistedHopfEulerCharacteristic : ℤ :=
  1 - 1 - 1 + 1

@[simp] theorem twisted_hopf_euler_characteristic_zero :
    twistedHopfEulerCharacteristic = 0 := by
  norm_num [twistedHopfEulerCharacteristic]

def orientedCoverEulerCharacteristic : ℤ :=
  (1 - 1) * (1 - 1)

@[simp] theorem oriented_cover_euler_characteristic_zero :
    orientedCoverEulerCharacteristic = 0 := by
  norm_num [orientedCoverEulerCharacteristic]

structure TwistedHopfInvariantPackage where
  compactSmoothFourManifoldConstructed : Prop
  nonorientable : Prop
  fundamentalGroupInfiniteCyclic : Prop
  orientationCharacterIsParity : Prop
  orientationDoubleCoverS3TimesS1 : Prop
  deckGroupZ2 : Prop
  ordinaryH0IsZ : Prop
  ordinaryH1IsZ : Prop
  ordinaryH2Vanishes : Prop
  ordinaryH3IsZ2 : Prop
  ordinaryH4Vanishes : Prop
  twistedTopClassIsZ : Prop
  eulerCharacteristicZero : Prop
  locallyConformallyFlatMetricDescends : Prop


def invariantPackageClosed (s : TwistedHopfInvariantPackage) : Prop :=
  s.compactSmoothFourManifoldConstructed /\
  s.nonorientable /\
  s.fundamentalGroupInfiniteCyclic /\
  s.orientationCharacterIsParity /\
  s.orientationDoubleCoverS3TimesS1 /\
  s.deckGroupZ2 /\
  s.ordinaryH0IsZ /\
  s.ordinaryH1IsZ /\
  s.ordinaryH2Vanishes /\
  s.ordinaryH3IsZ2 /\
  s.ordinaryH4Vanishes /\
  s.twistedTopClassIsZ /\
  s.eulerCharacteristicZero /\
  s.locallyConformallyFlatMetricDescends

end P0EFTJanusTwistedHopfTopologyInvariants
end JanusFormal
