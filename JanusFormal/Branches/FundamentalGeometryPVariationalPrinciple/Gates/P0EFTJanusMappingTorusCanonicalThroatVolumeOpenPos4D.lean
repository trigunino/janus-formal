import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.DenselyOrdered
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-!
# Full support of the canonical throat volume

This gate keeps the topological-support proof downstream of the foundational
canonical H1 construction.  It uses the same defining sphere/time pushforward,
integer reduction into the half-open fundamental interval and positivity of
the round-sphere/Lebesgue product measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev StandardThroatSphere := Metric.sphere (0 : EuclideanR3) 1

local instance openPosEffectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance openPosEffectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

private def openPosFundamentalTimeInterval : Set Real :=
  Set.Ioc (min 0 period) (max 0 period)

private def openPosCanonicalThroatProductMeasure :
    Measure (StandardThroatSphere × Real) :=
  ((volume : Measure EuclideanR3).toSphere).prod
    (volume.restrict (openPosFundamentalTimeInterval period))

private def openPosCanonicalThroatFundamentalDomainMap
    (point : StandardThroatSphere × Real) :
    EffectiveThroat period hPeriod :=
  mappingTorusMk (throatData period hPeriod)
    ((coverHomeomorphProd (throatData period hPeriod)).symm
      (equatorialTwoSphereHomeomorph.symm point.1, point.2))

private theorem intrinsicCanonicalThroatVolumeMeasure_eq_openPosPresentation :
    intrinsicCanonicalThroatVolumeMeasure period hPeriod =
      (openPosCanonicalThroatProductMeasure period).map
        (openPosCanonicalThroatFundamentalDomainMap period hPeriod) := by
  rfl

private theorem openPosCanonicalThroatFundamentalDomainMap_continuous :
    Continuous
      (openPosCanonicalThroatFundamentalDomainMap period hPeriod) := by
  have hProduct : Continuous
      (fun point : StandardThroatSphere × Real =>
        (equatorialTwoSphereHomeomorph.symm point.1, point.2)) :=
    (equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (throatData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (throatData period hPeriod)).symm.continuous.comp hProduct)

private theorem openPosCanonicalThroatFundamentalDomainMap_surjective :
    Function.Surjective
      (openPosCanonicalThroatFundamentalDomainMap period hPeriod) := by
  intro quotientPoint
  obtain ⟨anchor, hAnchor⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) quotientPoint
  refine ⟨(equatorialTwoSphereHomeomorph anchor.fiber, anchor.time), ?_⟩
  simpa [openPosCanonicalThroatFundamentalDomainMap] using hAnchor

private theorem openPosCanonicalThroatFundamentalDomainMap_timeShift
    (point : StandardThroatSphere × Real) (winding : Int) :
    openPosCanonicalThroatFundamentalDomainMap period hPeriod
        (point.1, point.2 + (winding : Real) * period) =
      openPosCanonicalThroatFundamentalDomainMap period hPeriod point := by
  unfold openPosCanonicalThroatFundamentalDomainMap
  rw [mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · rw [vadd_fiber]
    change ((Homeomorph.refl EquatorialTwoSphere) ^ winding)
        (equatorialTwoSphereHomeomorph.symm point.1) =
      equatorialTwoSphereHomeomorph.symm point.1
    rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding)
          (equatorialTwoSphereHomeomorph.symm point.1) =
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv)
          (equatorialTwoSphereHomeomorph.symm point.1) from rfl,
      homeomorph_toEquiv_zpow]
    rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
      one_zpow]
    rfl
  · rw [vadd_time]
    rfl

include hPeriod in
private theorem exists_timeShift_mem_openPosFundamentalTimeInterval
    (time : Real) :
    ∃ winding : Int,
      time + (winding : Real) * period ∈
        openPosFundamentalTimeInterval period := by
  by_cases hPositive : 0 < period
  · obtain ⟨winding, hWinding, -⟩ :=
      existsUnique_add_zsmul_mem_Ioc hPositive time 0
    refine ⟨winding, ?_⟩
    rw [zsmul_eq_mul] at hWinding
    simpa [openPosFundamentalTimeInterval, min_eq_left hPositive.le,
      max_eq_right hPositive.le] using hWinding
  · have hNegative : period < 0 :=
      lt_of_le_of_ne (le_of_not_gt hPositive) hPeriod
    obtain ⟨winding, hWinding, -⟩ :=
      existsUnique_add_zsmul_mem_Ioc (neg_pos.mpr hNegative) time period
    refine ⟨-winding, ?_⟩
    rw [zsmul_eq_mul] at hWinding
    simpa [openPosFundamentalTimeInterval, min_eq_right hNegative.le,
      max_eq_left hNegative.le] using hWinding

/-- Every nonempty quotient-open set lifts into the interior of the chosen
half-open time fundamental domain. -/
private theorem openPosCanonicalThroatFundamentalDomainMap_preimage_open_meets_interior
    (subset : Set (EffectiveThroat period hPeriod))
    (hOpen : IsOpen subset) (hNonempty : subset.Nonempty) :
    ((openPosCanonicalThroatFundamentalDomainMap period hPeriod ⁻¹' subset) ∩
      (Set.univ ×ˢ Set.Ioo (min 0 period) (max 0 period))).Nonempty := by
  obtain ⟨quotientPoint, hQuotientPoint⟩ := hNonempty
  obtain ⟨point, hPoint⟩ :=
    openPosCanonicalThroatFundamentalDomainMap_surjective
      (period := period) (hPeriod := hPeriod) quotientPoint
  have hPointPreimage :
      point ∈
        openPosCanonicalThroatFundamentalDomainMap period hPeriod ⁻¹' subset := by
    change openPosCanonicalThroatFundamentalDomainMap
      period hPeriod point ∈ subset
    rw [hPoint]
    exact hQuotientPoint
  obtain ⟨winding, hWinding⟩ :=
    exists_timeShift_mem_openPosFundamentalTimeInterval
      (period := period) (hPeriod := hPeriod) point.2
  let shifted : StandardThroatSphere × Real :=
    (point.1, point.2 + (winding : Real) * period)
  have hShiftedPreimage :
      shifted ∈
        openPosCanonicalThroatFundamentalDomainMap
          period hPeriod ⁻¹' subset := by
    change openPosCanonicalThroatFundamentalDomainMap
      period hPeriod shifted ∈ subset
    rw [show openPosCanonicalThroatFundamentalDomainMap
        period hPeriod shifted =
          openPosCanonicalThroatFundamentalDomainMap
            period hPeriod point by
      exact openPosCanonicalThroatFundamentalDomainMap_timeShift
        (period := period) (hPeriod := hPeriod) point winding]
    exact hPointPreimage
  have hBounds :
      min 0 period < shifted.2 ∧ shifted.2 ≤ max 0 period := by
    simpa [shifted, openPosFundamentalTimeInterval] using hWinding
  by_cases hStrict : shifted.2 < max 0 period
  · exact ⟨shifted, hShiftedPreimage, Set.mem_prod.mpr
      ⟨Set.mem_univ _, hBounds.1, hStrict⟩⟩
  · have hEndpoint : shifted.2 = max 0 period :=
      le_antisymm hBounds.2 (le_of_not_gt hStrict)
    let liftedOpen : Set (StandardThroatSphere × Real) :=
      openPosCanonicalThroatFundamentalDomainMap
        period hPeriod ⁻¹' subset
    have hLiftedOpen : IsOpen liftedOpen :=
      hOpen.preimage
        (openPosCanonicalThroatFundamentalDomainMap_continuous
          period hPeriod)
    let timeSlice : Set Real :=
      (fun time : Real => (shifted.1, time)) ⁻¹' liftedOpen
    have hTimeSliceOpen : IsOpen timeSlice :=
      hLiftedOpen.preimage (continuous_const.prodMk continuous_id)
    have hEndpointMem : max 0 period ∈ timeSlice := by
      change (shifted.1, max 0 period) ∈ liftedOpen
      have hShiftedEq :
          shifted = (shifted.1, max 0 period) := by
        apply Prod.ext
        · rfl
        · exact hEndpoint
      rw [← hShiftedEq]
      exact hShiftedPreimage
    have hMinMax : min 0 period < max 0 period :=
      min_lt_max.mpr hPeriod.symm
    have hEndpointClosure :
        max 0 period ∈
          closure (Set.Ioo (min 0 period) (max 0 period)) := by
      rw [closure_Ioo (ne_of_lt hMinMax)]
      exact ⟨hMinMax.le, le_rfl⟩
    obtain ⟨time, hTimeSlice, hTimeInterior⟩ :=
      (mem_closure_iff.mp hEndpointClosure)
        timeSlice hTimeSliceOpen hEndpointMem
    refine ⟨(shifted.1, time), ?_, Set.mem_prod.mpr
      ⟨Set.mem_univ _, hTimeInterior⟩⟩
    exact hTimeSlice

private theorem openPosCanonicalThroatProductMeasure_open_ne_zero
    (subset : Set (StandardThroatSphere × Real))
    (hOpen : IsOpen subset)
    (hMeetsInterior :
      (subset ∩
        (Set.univ ×ˢ Set.Ioo (min 0 period) (max 0 period))).Nonempty) :
    openPosCanonicalThroatProductMeasure period subset ≠ 0 := by
  obtain ⟨⟨spherePoint, time⟩, hSubset,
      -, hTimeInterior⟩ := hMeetsInterior
  obtain ⟨sphereSet, timeSet, hSphereOpen, hTimeOpen,
      hSphereMem, hTimeMem, hRectangleSubset⟩ :=
    isOpen_prod_iff.mp hOpen spherePoint time hSubset
  let interiorTimeSet : Set Real :=
    timeSet ∩ Set.Ioo (min 0 period) (max 0 period)
  have hInteriorTimeOpen : IsOpen interiorTimeSet :=
    hTimeOpen.inter isOpen_Ioo
  have hInteriorTimeNonempty : interiorTimeSet.Nonempty :=
    ⟨time, hTimeMem, hTimeInterior⟩
  have hInteriorTimeSubset :
      interiorTimeSet ⊆ Set.Ioc (min 0 period) (max 0 period) := by
    intro value hValue
    exact ⟨hValue.2.1, hValue.2.2.le⟩
  have hSphereMeasure :
      (volume : Measure EuclideanR3).toSphere sphereSet ≠ 0 :=
    hSphereOpen.measure_ne_zero _ ⟨spherePoint, hSphereMem⟩
  have hTimeMeasure :
      (volume.restrict (openPosFundamentalTimeInterval period))
          interiorTimeSet ≠ 0 := by
    have hSubsetFundamental :
        interiorTimeSet ⊆ openPosFundamentalTimeInterval period := by
      simpa [openPosFundamentalTimeInterval] using hInteriorTimeSubset
    rw [Measure.restrict_apply hInteriorTimeOpen.measurableSet,
      Set.inter_eq_left.mpr hSubsetFundamental]
    exact hInteriorTimeOpen.measure_ne_zero volume hInteriorTimeNonempty
  have hProductMeasure :
      openPosCanonicalThroatProductMeasure period
          (sphereSet ×ˢ interiorTimeSet) ≠ 0 := by
    unfold openPosCanonicalThroatProductMeasure
    rw [Measure.prod_prod]
    exact mul_ne_zero hSphereMeasure hTimeMeasure
  intro hZero
  exact hProductMeasure
    (measure_mono_null (fun point hPoint => hRectangleSubset
      ⟨hPoint.1, hPoint.2.1⟩) hZero)

/-- The canonical round-sphere/time pushforward is positive on every nonempty
open subset of the actual throat. -/
theorem intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_openPosPresentation]
  constructor
  intro subset hOpen hNonempty
  rw [Measure.map_apply
    (openPosCanonicalThroatFundamentalDomainMap_continuous
      period hPeriod).measurable hOpen.measurableSet]
  exact openPosCanonicalThroatProductMeasure_open_ne_zero period
    (openPosCanonicalThroatFundamentalDomainMap period hPeriod ⁻¹' subset)
    (hOpen.preimage
      (openPosCanonicalThroatFundamentalDomainMap_continuous
        period hPeriod))
    (openPosCanonicalThroatFundamentalDomainMap_preimage_open_meets_interior
      period hPeriod subset hOpen hNonempty)

end

end P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
end JanusFormal
