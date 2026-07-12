import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusTwoFoldBosonicZ4Representation

namespace JanusFormal
namespace P0EFTJanusQuarterPlaneDeterminantMultiplicity

set_option autoImplicit false

open P0EFTJanusTwoFoldBosonicZ4Representation

/-- A real order-four representation built entirely from two-dimensional quarter-turn planes. -/
structure RealQuarterModule where
  realRank : ℕ
  quarterPlaneCount : ℕ
  rankLaw : realRank = 2 * quarterPlaneCount

/-- One real quarter-turn plane supplies one phase-paired determinant unit. -/
def determinantQuarterWeight (s : RealQuarterModule) : ℕ :=
  s.quarterPlaneCount

/-- Real rank ten means five quarter-turn planes, not ten determinant units. -/
theorem rank_ten_forces_five_quarter_planes
    (s : RealQuarterModule)
    (hRank : s.realRank = 10) :
    s.quarterPlaneCount = 5 := by
  have hLaw := s.rankLaw
  rw [hRank] at hLaw
  omega

/-- Hence a rank-ten real quarter module has effective quarter weight five. -/
theorem rank_ten_has_determinant_weight_five
    (s : RealQuarterModule)
    (hRank : s.realRank = 10) :
    determinantQuarterWeight s = 5 := by
  unfold determinantQuarterWeight
  exact rank_ten_forces_five_quarter_planes s hRank

/-- A determinant weight of ten requires real rank twenty. -/
theorem determinant_weight_ten_forces_rank_twenty
    (s : RealQuarterModule)
    (hWeight : determinantQuarterWeight s = 10) :
    s.realRank = 20 := by
  unfold determinantQuarterWeight at hWeight
  rw [s.rankLaw, hWeight]
  norm_num

/-- Rank ten and quarter determinant weight ten are incompatible. -/
theorem no_rank_ten_weight_ten_quarter_module
    (s : RealQuarterModule)
    (hRank : s.realRank = 10) :
    determinantQuarterWeight s ≠ 10 := by
  rw [rank_ten_has_determinant_weight_five s hRank]
  norm_num

/-- External duplication of an already defined real quarter module. -/
def externalDoubleCopy (s : RealQuarterModule) : RealQuarterModule where
  realRank := 2 * s.realRank
  quarterPlaneCount := 2 * s.quarterPlaneCount
  rankLaw := by
    rw [s.rankLaw]
    ring

/-- A genuine external copy doubles both the real rank and determinant weight. -/
theorem external_copy_doubles_weight
    (s : RealQuarterModule) :
    determinantQuarterWeight (externalDoubleCopy s) =
      2 * determinantQuarterWeight s := by
  rfl

/-- The explicit two-fold five-component construction is rank ten with five planes. -/
def explicitTwoFoldFiveComponentModule : RealQuarterModule where
  realRank := doubledFivePlaneDecomposition.realDimension
  quarterPlaneCount := doubledFivePlaneDecomposition.quarterPlaneCount
  rankLaw := doubledFivePlaneDecomposition.dimensionLaw

@[simp] theorem explicit_two_fold_real_rank :
    explicitTwoFoldFiveComponentModule.realRank = 10 := by
  rfl

@[simp] theorem explicit_two_fold_quarter_weight :
    determinantQuarterWeight explicitTwoFoldFiveComponentModule = 5 := by
  rfl

/-- To obtain weight ten from this construction one must add a second independent rank-ten copy. -/
theorem explicit_external_double_copy_has_rank_twenty_weight_ten :
    (externalDoubleCopy explicitTwoFoldFiveComponentModule).realRank = 20 /\
    determinantQuarterWeight
      (externalDoubleCopy explicitTwoFoldFiveComponentModule) = 10 := by
  norm_num [externalDoubleCopy, explicitTwoFoldFiveComponentModule,
    determinantQuarterWeight, doubledFivePlaneDecomposition]

/--
The fold exchange used to define the quarter-turn complex structure is already
inside the rank-ten real module.  Multiplying its determinant weight by two once
more is double counting unless an additional independent rank-ten field is
actually present.
-/
structure QuarterMultiplicityPhysicalStatus where
  realFieldContentDerived : Prop
  quarterPlaneDecompositionDerived : Prop
  gaussianRealityConditionHandled : Prop
  phasePairedDeterminantComputed : Prop
  foldExchangeAlreadyIncluded : Prop
  independentCopiesCounted : Prop
  noPTDoubleCountingProved : Prop
  effectiveQuarterWeightDerived : Prop


def quarterMultiplicityPhysicalClosure
    (s : QuarterMultiplicityPhysicalStatus) : Prop :=
  s.realFieldContentDerived /\
  s.quarterPlaneDecompositionDerived /\
  s.gaussianRealityConditionHandled /\
  s.phasePairedDeterminantComputed /\
  s.foldExchangeAlreadyIncluded /\
  s.independentCopiesCounted /\
  s.noPTDoubleCountingProved /\
  s.effectiveQuarterWeightDerived

end P0EFTJanusQuarterPlaneDeterminantMultiplicity
end JanusFormal
