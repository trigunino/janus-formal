import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedHopfTopologyInvariants

set_option autoImplicit false

/--
Cellular top boundary of the mapping torus of an orientation-reversing
reflection of `S3`. On the top cell the monodromy contributes `1 - (-1) = 2`.
-/
def topCellBoundary (n : ℤ) : ℤ := 2 * n

/-- The nonorientable four-manifold has no ordinary integral top cycle. -/
theorem top_cell_boundary_has_trivial_kernel
    (n : ℤ)
    (h : topCellBoundary n = 0) :
    n = 0 := by
  unfold topCellBoundary at h
  omega

/-- The image of the top boundary consists exactly of the even integers. -/
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

/-- The residual degree-three cellular class is therefore mod two. -/
def degreeThreeTorsionClass (n : ℤ) : ZMod 2 := n

@[simp] theorem twice_degree_three_class_vanishes
    (n : ℤ) :
    degreeThreeTorsionClass (2 * n) = 0 := by
  simp [degreeThreeTorsionClass]

/--
The minimal CW signature has one cell in degrees `0,1,3,4`, hence Euler
characteristic zero.
-/
def twistedHopfEulerCharacteristic : ℤ :=
  1 - 1 - 1 + 1

@[simp] theorem twisted_hopf_euler_characteristic_zero :
    twistedHopfEulerCharacteristic = 0 := by
  norm_num [twistedHopfEulerCharacteristic]

/-- The oriented double cover `S3 x S1` also has Euler characteristic zero. -/
def orientedCoverEulerCharacteristic : ℤ :=
  (1 - 1) * (1 - 1)

@[simp] theorem oriented_cover_euler_characteristic_zero :
    orientedCoverEulerCharacteristic = 0 := by
  norm_num [orientedCoverEulerCharacteristic]

/--
Invariant package of the proposed resolved Janus manifold

`J4 = (R4 \ {0}) / <x ↦ lambda * rho(x)>`,

where `rho` is an orientation-reversing reflection. The package records the
mathematical targets to be replaced by genuine manifold constructions.
-/
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
