import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D

namespace JanusFormal
namespace P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff Topology
open Set TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

def equatorialSphericalBandSpacetimeOpen : Opens (UnitThreeSphere × Real) :=
  ⟨EquatorialSphericalBand ×ˢ Set.univ,
    equatorialSphericalBandOpen.2.prod isOpen_univ⟩

def equatorialBandSpacetimeParameter
    (input : equatorialSphericalBandSpacetimeOpen) :
    equatorialSphericalBandOpen × Real :=
  (⟨input.1.1, input.2.1⟩, input.1.2)

theorem equatorialBandSpacetimeParameter_contMDiff :
    ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      ∞ equatorialBandSpacetimeParameter := by
  have hSpaceVal : ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real EuclideanR3) ∞
      (fun input : equatorialSphericalBandSpacetimeOpen => input.1.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  have hSpace : ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real EuclideanR3) ∞
      (fun input : equatorialSphericalBandSpacetimeOpen =>
        (⟨input.1.1, input.2.1⟩ : equatorialSphericalBandOpen)) := by
    rw [← ContMDiff.subtypeVal_comp_iff equatorialSphericalBandOpen]
    exact hSpaceVal
  have hTime : ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun input : equatorialSphericalBandSpacetimeOpen => input.1.2) :=
    contMDiff_snd.comp contMDiff_subtype_val
  exact hSpace.prodMk hTime

def equatorialBandSpacetimeScalarCurrentDensity
    (field test : SmoothQuotientField period hPeriod Real)
    (input : equatorialSphericalBandSpacetimeOpen) : Real :=
  equatorialBandScalarCurrentDensity period hPeriod field test
    (equatorialBandSpacetimeParameter input)

theorem equatorialBandSpacetimeScalarCurrentDensity_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (equatorialBandSpacetimeScalarCurrentDensity period hPeriod field test) :=
  (equatorialBandScalarCurrentDensity_contMDiff period hPeriod field test).comp
    equatorialBandSpacetimeParameter_contMDiff

def equatorialBandScalarCurrentZeroExtension
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real) : Real := by
  classical
  exact if hInput : input.1 ∈ EquatorialSphericalBand then
      equatorialBandScalarCurrentDensity period hPeriod field test
        (⟨input.1, hInput⟩, input.2)
    else
      0

theorem equatorialBandScalarCurrentZeroExtension_eq_on_band
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real)
    (hInput : input.1 ∈ EquatorialSphericalBand) :
    equatorialBandScalarCurrentZeroExtension period hPeriod field test input =
      equatorialBandScalarCurrentDensity period hPeriod field test
        (⟨input.1, hInput⟩, input.2) := by
  simp [equatorialBandScalarCurrentZeroExtension, hInput]

theorem sin_one_lt_one : Real.sin 1 < 1 := by
  have hOne : (1 : Real) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hPi : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  simpa using Real.strictMonoOn_sin hOne hPi (by linarith [Real.pi_gt_three])

theorem one_lt_abs_arcsin_of_sin_one_lt_abs
    {coordinate : Real}
    (hBand : |coordinate| < 1)
    (hCoordinate : Real.sin 1 < |coordinate|) :
    1 < |Real.arcsin coordinate| := by
  have hOne : (1 : Real) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hCoordinateRange : coordinate ∈ Set.Icc (-1 : Real) 1 := by
    exact ⟨(abs_lt.mp hBand).1.le, (abs_lt.mp hBand).2.le⟩
  by_cases hNonneg : 0 ≤ coordinate
  · rw [abs_of_nonneg hNonneg] at hCoordinate
    have hArc : 1 < Real.arcsin coordinate :=
      (Real.lt_arcsin_iff_sin_lt hOne hCoordinateRange).2 hCoordinate
    rw [abs_of_pos (hArc.trans' zero_lt_one)]
    exact hArc
  · have hNeg : coordinate < 0 := lt_of_not_ge hNonneg
    have hNegRange : -coordinate ∈ Set.Icc (-1 : Real) 1 := by
      constructor <;> linarith [hCoordinateRange.1, hCoordinateRange.2]
    rw [abs_of_neg hNeg] at hCoordinate
    have hArcNeg : 1 < Real.arcsin (-coordinate) :=
      (Real.lt_arcsin_iff_sin_lt hOne hNegRange).2 hCoordinate
    rw [Real.arcsin_neg] at hArcNeg
    rw [abs_of_neg (by linarith : Real.arcsin coordinate < 0)]
    linarith

theorem equatorialBandScalarCurrentDensity_eq_zero_of_sin_one_lt_abs
    (field test : SmoothQuotientField period hPeriod Real)
    (input : equatorialSphericalBandOpen × Real)
    (hCoordinate : Real.sin 1 < |input.1.1.1 0|) :
    equatorialBandScalarCurrentDensity period hPeriod field test input = 0 := by
  apply jointCutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs
  rw [equatorialBandCanonicalParameter]
  change 1 ≤ |(equatorialTubularSmoothInverse input.1).2.1|
  rw [show (equatorialTubularSmoothInverse input.1).2 =
      equatorialTubularNormalSmooth input.1 from rfl,
    equatorialTubularNormalSmooth_eq_bandNormal]
  exact (one_lt_abs_arcsin_of_sin_one_lt_abs input.1.2 hCoordinate).le

theorem equatorialBandScalarCurrentZeroExtension_eq_on_spacetime_band
    (field test : SmoothQuotientField period hPeriod Real)
    (input : equatorialSphericalBandSpacetimeOpen) :
    equatorialBandScalarCurrentZeroExtension period hPeriod field test input.1 =
      equatorialBandSpacetimeScalarCurrentDensity period hPeriod field test input := by
  rw [equatorialBandScalarCurrentZeroExtension_eq_on_band period hPeriod field test
    input.1 input.2.1]
  rfl

theorem equatorialBandScalarCurrentZeroExtension_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (equatorialBandScalarCurrentZeroExtension period hPeriod field test) := by
  intro current
  by_cases hCurrent : current.1 ∈ EquatorialSphericalBand
  · let bandCurrent : equatorialSphericalBandSpacetimeOpen :=
      ⟨current, hCurrent, Set.mem_univ current.2⟩
    rw [← contMDiffAt_subtype_iff (x := bandCurrent)]
    apply (equatorialBandSpacetimeScalarCurrentDensity_contMDiff
      period hPeriod field test).contMDiffAt.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun nearby =>
      equatorialBandScalarCurrentZeroExtension_eq_on_spacetime_band
        period hPeriod field test nearby
  · have hOutside : 1 ≤ |current.1.1 0| := le_of_not_gt hCurrent
    have hThreshold : Real.sin 1 < |current.1.1 0| :=
      (sin_one_lt_one.trans_le hOutside)
    have hCoordinateContinuous : Continuous
        (fun nearby : UnitThreeSphere × Real => nearby.1.1 0) :=
      (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)
    have hOpen : IsOpen
        {nearby : UnitThreeSphere × Real | Real.sin 1 < |nearby.1.1 0|} :=
      isOpen_lt continuous_const (continuous_abs.comp hCoordinateContinuous)
    have hEventuallyZero :
        equatorialBandScalarCurrentZeroExtension period hPeriod field test =ᶠ[𝓝 current]
          (fun _ => 0) := by
      filter_upwards [hOpen.mem_nhds hThreshold] with nearby hNearby
      by_cases hNearbyBand : nearby.1 ∈ EquatorialSphericalBand
      · rw [equatorialBandScalarCurrentZeroExtension_eq_on_band
          period hPeriod field test nearby hNearbyBand]
        exact equatorialBandScalarCurrentDensity_eq_zero_of_sin_one_lt_abs
          period hPeriod field test (⟨nearby.1, hNearbyBand⟩, nearby.2) hNearby
      · simp [equatorialBandScalarCurrentZeroExtension, hNearbyBand]
    exact contMDiffAt_const.congr_of_eventuallyEq hEventuallyZero

theorem equatorialBandScalarCurrentZeroExtension_eq_zero_of_sin_one_lt_abs
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real)
    (hCoordinate : Real.sin 1 < |input.1.1 0|) :
    equatorialBandScalarCurrentZeroExtension period hPeriod field test input = 0 := by
  by_cases hInput : input.1 ∈ EquatorialSphericalBand
  · rw [equatorialBandScalarCurrentZeroExtension_eq_on_band
      period hPeriod field test input hInput]
    exact equatorialBandScalarCurrentDensity_eq_zero_of_sin_one_lt_abs
      period hPeriod field test (⟨input.1, hInput⟩, input.2) hCoordinate
  · simp [equatorialBandScalarCurrentZeroExtension, hInput]

theorem support_equatorialBandScalarCurrentZeroExtension_subset_spatialCylinder
    (field test : SmoothQuotientField period hPeriod Real) :
    Function.support
      (equatorialBandScalarCurrentZeroExtension period hPeriod field test) ⊆
      {input : UnitThreeSphere × Real | |input.1.1 0| ≤ Real.sin 1} := by
  intro input hSupport
  by_contra hOutside
  apply hSupport
  exact equatorialBandScalarCurrentZeroExtension_eq_zero_of_sin_one_lt_abs
    period hPeriod field test input (lt_of_not_ge hOutside)

end
end P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
end JanusFormal
