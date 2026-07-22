import Mathlib.Algebra.Order.Floor.Ring
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D

/-!
# Density of the open Lorentz fundamental strip

Every mapping-torus orbit has a representative whose time coordinate lies in
the closed interval between `0` and the period.  This is the ordinary fractional
part construction, with the negative-period case obtained by applying the same
argument to `-time` and `-period`.

The open fundamental interval is dense in that closed interval.  Keeping the
sphere coordinate fixed and using continuity of the quotient map therefore
shows that round `S³` times the open fundamental interval has dense image in the
physical mapping torus.

Consequently the full-support datum introduced by the previous reduction is a
theorem and is no longer a genuine input.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
open P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D

private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- Every real time can be shifted by an integral number of periods into the
closed fundamental interval. -/
theorem exists_int_shift_mem_canonicalLorentzClosedTime
    (time : Real) :
    ∃ shift : Int,
      time + (shift : Real) * period ∈
        Set.Icc (min 0 period) (max 0 period) := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · let shift : Int := -⌊(-time) / (-period)⌋
    refine ⟨shift, ?_⟩
    have hScale : 0 < -period := neg_pos.mpr hNegative
    have hFraction :=
      Int.fract_div_mul_self_mem_Ico (-period) (-time) hScale
    have hDecomposition :=
      Int.fract_div_mul_self_add_zsmul_eq
        (-period) (-time) (ne_of_gt hScale)
    rw [zsmul_eq_mul] at hDecomposition
    have hShift :
        time + (shift : Real) * period =
          -(Int.fract ((-time) / (-period)) * (-period)) := by
      dsimp [shift]
      push_cast
      linarith
    rw [min_eq_right hNegative.le, max_eq_left hNegative.le, hShift]
    constructor
    · linarith [hFraction.2]
    · linarith [hFraction.1]
  · let shift : Int := -⌊time / period⌋
    refine ⟨shift, ?_⟩
    have hFraction :=
      Int.fract_div_mul_self_mem_Ico period time hPositive
    have hDecomposition :=
      Int.fract_div_mul_self_add_zsmul_eq
        period time (ne_of_gt hPositive)
    rw [zsmul_eq_mul] at hDecomposition
    have hShift :
        time + (shift : Real) * period =
          Int.fract (time / period) * period := by
      dsimp [shift]
      push_cast
      linarith
    rw [min_eq_left hPositive.le, max_eq_right hPositive.le, hShift]
    exact ⟨hFraction.1, hFraction.2.le⟩

/-- Every physical point has a round-sphere representative with time in the
closed fundamental interval. -/
theorem exists_canonicalLorentzClosedFundamentalRepresentative
    (target : EffectiveQuotient period hPeriod) :
    ∃ parameter : StandardSphere3 × Real,
      parameter.2 ∈ Set.Icc (min 0 period) (max 0 period) ∧
        canonicalLorentzFundamentalDomainMap period hPeriod parameter = target := by
  rcases mappingTorusMk_surjective (sphereData period hPeriod) target with
    ⟨cover, rfl⟩
  rcases exists_int_shift_mem_canonicalLorentzClosedTime
      period hPeriod cover.time with ⟨shift, hTime⟩
  let shiftedCover : MappingTorusCover (sphereData period hPeriod) :=
    shift +ᵥ cover
  refine ⟨(unitThreeSphereHomeomorph shiftedCover.fiber, shiftedCover.time), ?_, ?_⟩
  · simpa [shiftedCover] using hTime
  · unfold canonicalLorentzFundamentalDomainMap
    rw [unitThreeSphereHomeomorph.symm_apply_apply]
    change mappingTorusMk (sphereData period hPeriod) shiftedCover =
      mappingTorusMk (sphereData period hPeriod) cover
    exact (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod) shiftedCover cover).2 ⟨shift, rfl⟩

/-- The endpoints of the canonical fundamental interval are distinct. -/
theorem canonicalLorentzFundamentalTime_min_lt_max :
    min 0 period < max 0 period := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · simpa [min_eq_right hNegative.le, max_eq_left hNegative.le]
      using hNegative
  · simpa [min_eq_left hPositive.le, max_eq_right hPositive.le]
      using hPositive

/-- The explicit open fundamental-strip parametrization has dense physical
image. -/
theorem canonicalLorentzInteriorPhysicalMap_denseRange :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) := by
  intro target
  rcases exists_canonicalLorentzClosedFundamentalRepresentative
      period hPeriod target with ⟨parameter, hTime, hTarget⟩
  rw [← hTarget]
  let fiberLine : Real → StandardSphere3 × Real :=
    fun time => (parameter.1, time)
  have hTimeClosure :
      parameter.2 ∈ closure
        (Set.Ioo (min 0 period) (max 0 period)) := by
    rw [closure_Ioo
      (canonicalLorentzFundamentalTime_min_lt_max period hPeriod).ne]
    exact hTime
  have hParameterClosure :
      parameter ∈ closure
        (fiberLine '' Set.Ioo (min 0 period) (max 0 period)) := by
    have hImage := mem_closure_image
      ((continuous_const.prodMk continuous_id).continuousAt)
      hTimeClosure
    simpa [fiberLine] using hImage
  have hPhysicalClosure :
      canonicalLorentzFundamentalDomainMap period hPeriod parameter ∈
        closure
          (canonicalLorentzFundamentalDomainMap period hPeriod ''
            (fiberLine '' Set.Ioo (min 0 period) (max 0 period))) :=
    mem_closure_image
      ((canonicalLorentzFundamentalDomainMap_continuous
        period hPeriod).continuousAt) hParameterClosure
  apply closure_mono ?_ hPhysicalClosure
  rintro point ⟨fullParameter, ⟨time, hTimeInterior, rfl⟩, rfl⟩
  refine ⟨(parameter.1, ⟨time, hTimeInterior⟩), ?_⟩
  rfl

/-- Canonical dense-parametrization package, with no remaining topological
input. -/
def canonicalLorentzInteriorDenseRangeData :
    CanonicalLorentzInteriorDenseRangeData period hPeriod where
  denseRange := canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod

/-- Closed density/full-support certificate. -/
theorem canonicalLorentzInteriorDenseRange_certificate :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure :=
  ⟨canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod,
    (canonicalLorentzInteriorDenseRangeData period hPeriod)
      |>.toEulerDenseParametrizationData.physicalMeasureOpenPositive⟩

end
end P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
end JanusFormal
