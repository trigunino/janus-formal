import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusMinimalZ4AnomalyContent

namespace JanusFormal
namespace P0EFTJanusPrimitiveIndexFiveSelection

set_option autoImplicit false

open P0EFTJanusMinimalZ4AnomalyContent
open P0EFTJanusPeriodicQuarterCompetition

/-- Index bookkeeping for a rank-`r` fermion multiplet coupled to a monopole line. -/
structure FlavorMonopoleIndexData where
  flavorRank : ℕ
  monopoleNumber : ℤ
  totalIndex : ℤ
  indexLaw : totalIndex = (flavorRank : ℤ) * monopoleNumber

/-- Number of chiral zero-mode towers supplied by the index magnitude. -/
def quarterTowerMultiplicity
    (s : FlavorMonopoleIndexData) : ℕ :=
  s.totalIndex.natAbs

/-- A primitive monopole gives one chiral tower per flavor component. -/
theorem primitive_index_multiplicity_eq_flavor_rank
    (s : FlavorMonopoleIndexData)
    (hPrimitive : s.monopoleNumber.natAbs = 1) :
    quarterTowerMultiplicity s = s.flavorRank := by
  unfold quarterTowerMultiplicity
  rw [s.indexLaw, Int.natAbs_mul, hPrimitive]
  simp

/-- One flavor producing five indexed towers requires monopole magnitude five. -/
theorem one_flavor_five_towers_forces_charge_five
    (s : FlavorMonopoleIndexData)
    (hOneFlavor : s.flavorRank = 1)
    (hFiveTowers : quarterTowerMultiplicity s = 5) :
    s.monopoleNumber.natAbs = 5 := by
  have hIndex := s.indexLaw
  rw [hOneFlavor] at hIndex
  norm_num at hIndex
  unfold quarterTowerMultiplicity at hFiveTowers
  rw [hIndex] at hFiveTowers
  exact hFiveTowers

/-- A one-flavor five-tower explanation is incompatible with primitive flux. -/
theorem one_flavor_five_towers_are_not_primitive
    (s : FlavorMonopoleIndexData)
    (hOneFlavor : s.flavorRank = 1)
    (hFiveTowers : quarterTowerMultiplicity s = 5) :
    s.monopoleNumber.natAbs ≠ 1 := by
  have hCharge := one_flavor_five_towers_forces_charge_five
    s hOneFlavor hFiveTowers
  omega

/-- Primitive flux and exactly five indexed towers force flavor rank five. -/
theorem primitive_five_towers_force_rank_five
    (s : FlavorMonopoleIndexData)
    (hPrimitive : s.monopoleNumber.natAbs = 1)
    (hFiveTowers : quarterTowerMultiplicity s = 5) :
    s.flavorRank = 5 := by
  calc
    s.flavorRank = quarterTowerMultiplicity s :=
      (primitive_index_multiplicity_eq_flavor_rank s hPrimitive).symm
    _ = 5 := hFiveTowers

/-- Primitive rank below five cannot satisfy the old same-sign stationarity law. -/
theorem primitive_rank_below_five_cannot_stabilize
    (s : FlavorMonopoleIndexData)
    (hPrimitive : s.monopoleNumber.natAbs = 1)
    (hBelow : s.flavorRank < 5)
    (radial : ℝ) :
    stationarityPolynomial 1
        (quarterTowerMultiplicity s : ℝ) radial ≠ 0 := by
  rw [primitive_index_multiplicity_eq_flavor_rank s hPrimitive]
  exact below_five_modes_cannot_stabilize
    s.flavorRank hBelow radial

/-- Primitive rank five reaches the arithmetic root `r=1/3`. -/
theorem primitive_rank_five_has_one_third_root
    (s : FlavorMonopoleIndexData)
    (hPrimitive : s.monopoleNumber.natAbs = 1)
    (hRank : s.flavorRank = 5) :
    stationarityPolynomial 1
        (quarterTowerMultiplicity s : ℝ) (1 / 3) = 0 := by
  rw [primitive_index_multiplicity_eq_flavor_rank s hPrimitive,
    hRank]
  exact third_is_one_to_five_stationary

/-- Odd multiplicity `2*k+1` leaves the minimal positive half-level at bare level `-k`. -/
theorem odd_multiplicity_minimal_positive_half_level
    (k : ℤ) :
    positiveFoldDoubledLevel (-k) (2 * k + 1) = 1 := by
  unfold positiveFoldDoubledLevel
  ring

/-- The PT-related fold carries the opposite half-level. -/
theorem odd_multiplicity_minimal_negative_half_level
    (k : ℤ) :
    negativeFoldDoubledLevel (-k) (2 * k + 1) = -1 := by
  unfold negativeFoldDoubledLevel
  ring

/-- Primitive rank five gives five towers and the `+/-1/2` PT anomaly pair. -/
theorem primitive_rank_five_index_anomaly_matrix
    (s : FlavorMonopoleIndexData)
    (hPrimitive : s.monopoleNumber.natAbs = 1)
    (hRank : s.flavorRank = 5) :
    quarterTowerMultiplicity s = 5 /\
    positiveFoldDoubledLevel (-2)
        (quarterTowerMultiplicity s : ℤ) = 1 /\
    negativeFoldDoubledLevel (-2)
        (quarterTowerMultiplicity s : ℤ) = -1 /\
    positiveFoldDoubledLevel (-2)
        (quarterTowerMultiplicity s : ℤ) +
      negativeFoldDoubledLevel (-2)
        (quarterTowerMultiplicity s : ℤ) = 0 := by
  have hMultiplicity : quarterTowerMultiplicity s = 5 := by
    rw [primitive_index_multiplicity_eq_flavor_rank s hPrimitive,
      hRank]
  constructor
  · exact hMultiplicity
  · rw [hMultiplicity]
    exact ⟨five_mode_positive_fold_level,
      five_mode_negative_fold_level,
      five_mode_pt_pair_is_globally_level_zero⟩

/-- Physical obligations behind the primitive rank-five candidate. -/
structure PrimitiveRankFivePhysicalStatus where
  globalRankFiveFermionBundleConstructed : Prop
  primitiveMonopoleIndexTheoremApplied : Prop
  exactlyFiveLightZeroModeTowersProved : Prop
  quarterHolonomyDerivedFromPinLift : Prop
  parityAnomalyRegularized : Prop
  determinantSignsIncluded : Prop
  statisticsSignNoGoExited : Prop
  higherModesControlled : Prop
  finiteCountertermsFixedMicroscopically : Prop


def primitiveRankFivePhysicalClosure
    (s : PrimitiveRankFivePhysicalStatus) : Prop :=
  s.globalRankFiveFermionBundleConstructed /\
  s.primitiveMonopoleIndexTheoremApplied /\
  s.exactlyFiveLightZeroModeTowersProved /\
  s.quarterHolonomyDerivedFromPinLift /\
  s.parityAnomalyRegularized /\
  s.determinantSignsIncluded /\
  s.statisticsSignNoGoExited /\
  s.higherModesControlled /\
  s.finiteCountertermsFixedMicroscopically

end P0EFTJanusPrimitiveIndexFiveSelection
end JanusFormal
