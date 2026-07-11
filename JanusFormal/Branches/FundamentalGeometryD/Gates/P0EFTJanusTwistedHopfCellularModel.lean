import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedHopfCellularModel

set_option autoImplicit false

/-- Top cellular boundary for an orientation-reversing degree `-1` map of `S3`. -/
def topBoundary (n : ℤ) : ℤ := 2 * n

/-- The top boundary has trivial kernel. -/
theorem top_boundary_kernel_trivial
    (n : ℤ)
    (h : topBoundary n = 0) :
    n = 0 := by
  unfold topBoundary at h
  omega

/-- Its image is exactly the subgroup of even integers. -/
theorem top_boundary_image_iff_even
    (m : ℤ) :
    (∃ n : ℤ, topBoundary n = m) ↔ Even m := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by unfold topBoundary; ring⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold topBoundary
    nlinarith

/-- The residual degree-three class is represented by parity. -/
def degreeThreeParityClass (n : ℤ) : ZMod 2 := n

@[simp] theorem top_boundary_has_zero_parity
    (n : ℤ) :
    degreeThreeParityClass (topBoundary n) = 0 := by
  change (((2 * n : ℤ) : ZMod 2)) = 0
  push_cast
  norm_num

/-- The minimal cellular model has no degree-two cell. -/
abbrev DegreeTwoModTwoCochain := Fin 0 → ZMod 2

/-- Consequently every degree-two mod-two cellular cochain vanishes. -/
theorem every_degree_two_mod_two_cochain_vanishes
    (c : DegreeTwoModTwoCochain) :
    c = 0 := by
  funext i
  exact Fin.elim0 i

/-- In particular a cellular representative of `w1^2` must vanish. -/
theorem cellular_w1_square_vanishes
    (w1Square : DegreeTwoModTwoCochain) :
    w1Square = 0 :=
  every_degree_two_mod_two_cochain_vanishes w1Square

/-- Likewise a cellular representative of `w2` must vanish. -/
theorem cellular_w2_vanishes
    (w2 : DegreeTwoModTwoCochain) :
    w2 = 0 :=
  every_degree_two_mod_two_cochain_vanishes w2

/-- Cell ranks `1,1,0,1,1` give Euler characteristic zero. -/
def cellularEulerCharacteristic : ℤ :=
  1 - 1 + 0 - 1 + 1

@[simp] theorem cellular_euler_characteristic_zero :
    cellularEulerCharacteristic = 0 := by
  norm_num [cellularEulerCharacteristic]

/--
The remaining theorem is geometric: construct this CW model for the actual
mapping torus and identify its cellular boundary with `1-degree(rho)=2`.
-/
structure CellularModelRealizationStatus where
  mappingTorusCWConstructed : Prop
  oneCellInDegreesZeroOneThreeFour : Prop
  noDegreeTwoCellProved : Prop
  topBoundaryComputedAsTwo : Prop
  cellularHomologyComparedToSingularHomology : Prop
  modTwoCohomologyComparedToSWClasses : Prop


def cellularModelRealized
    (s : CellularModelRealizationStatus) : Prop :=
  s.mappingTorusCWConstructed /\
  s.oneCellInDegreesZeroOneThreeFour /\
  s.noDegreeTwoCellProved /\
  s.topBoundaryComputedAsTwo /\
  s.cellularHomologyComparedToSingularHomology /\
  s.modTwoCohomologyComparedToSWClasses

end P0EFTJanusTwistedHopfCellularModel
end JanusFormal
