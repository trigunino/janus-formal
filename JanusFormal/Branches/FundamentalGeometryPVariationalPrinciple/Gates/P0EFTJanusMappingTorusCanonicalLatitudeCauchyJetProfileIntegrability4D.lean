import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetProfileL2Bound4D

/-!
# Integrability of the fixed latitude Cauchy profiles

The normal coarea measure is

`cos²(ν) dν` on `(-π/2,π/2)`.

Its density is at most one, hence this measure is finite.  The value profile is a
smooth bump taking values in `[0,1]`.  The normal profile is `ν` times that bump
and is supported in `|ν| < 1`, so its absolute value is also at most one.
Therefore both profile squares are integrable.  This discharges the profile
moment hypothesis in the explicit Cauchy-jet graph estimate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Filter
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetProfileL2Bound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D

/-- The latitude Jacobian density is bounded by one. -/
theorem realLatitudeWeight_le_one (latitude : Real) :
    realLatitudeWeight latitude ≤ 1 := by
  unfold realLatitudeWeight
  have hCosSq : Real.cos latitude ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq latitude,
      sq_nonneg (Real.sin latitude)]
  simpa using ENNReal.ofReal_le_ofReal hCosSq

/-- The weighted normal coarea measure is dominated by restricted Lebesgue
measure. -/
theorem canonicalLatitudeCauchyJetNormalMeasure_le_restrictVolume :
    canonicalLatitudeCauchyJetNormalMeasure ≤
      volume.restrict
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  unfold canonicalLatitudeCauchyJetNormalMeasure
  rw [← withDensity_one]
  apply withDensity_mono
  filter_upwards [] with latitude
  exact realLatitudeWeight_le_one latitude

/-- Restricted Lebesgue measure on the latitude band is finite. -/
local instance latitudeBandFinite : IsFiniteMeasure
    (volume.restrict
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
  rw [isFiniteMeasure_restrict]
  simp

/-- The canonical normal coarea measure is finite. -/
local instance canonicalLatitudeCauchyJetNormalMeasureFinite :
    IsFiniteMeasure canonicalLatitudeCauchyJetNormalMeasure :=
  isFiniteMeasure_of_le _
    canonicalLatitudeCauchyJetNormalMeasure_le_restrictVolume

/-- The value profile lies in `[0,1]`. -/
theorem canonicalLatitudeCauchyValueProfile_nonnegative (normal : Real) :
    0 ≤ canonicalLatitudeCauchyValueProfile normal :=
  ContDiffBump.nonneg _

/-- The value profile is at most one. -/
theorem canonicalLatitudeCauchyValueProfile_le_one (normal : Real) :
    canonicalLatitudeCauchyValueProfile normal ≤ 1 :=
  ContDiffBump.le_one _

/-- The value-profile square is bounded by one. -/
theorem canonicalLatitudeCauchyValueProfile_sq_le_one (normal : Real) :
    canonicalLatitudeCauchyValueProfile normal ^ 2 ≤ 1 := by
  nlinarith [canonicalLatitudeCauchyValueProfile_nonnegative normal,
    canonicalLatitudeCauchyValueProfile_le_one normal]

/-- The normal-profile square is bounded by one. -/
theorem canonicalLatitudeCauchyNormalProfile_sq_le_one (normal : Real) :
    canonicalLatitudeCauchyNormalProfile normal ^ 2 ≤ 1 := by
  by_cases hSupport : 1 ≤ |normal|
  · rw [canonicalLatitudeCauchyNormalProfile_eq_zero_of_one_le_abs
      normal hSupport]
    norm_num
  · have hAbs : |normal| < 1 := lt_of_not_ge hSupport
    have hNormalSq : normal ^ 2 ≤ 1 := by
      have hAbsSq : |normal| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg normal]
      simpa [sq_abs] using hAbsSq
    have hCutoffNonnegative :
        0 ≤ canonicalLatitudeCauchyValueProfile normal :=
      canonicalLatitudeCauchyValueProfile_nonnegative normal
    have hCutoffSq : canonicalLatitudeCauchyValueProfile normal ^ 2 ≤ 1 :=
      canonicalLatitudeCauchyValueProfile_sq_le_one normal
    unfold canonicalLatitudeCauchyNormalProfile
    rw [mul_pow]
    exact mul_le_one₀ (sq_nonneg normal) hNormalSq
      (sq_nonneg (canonicalLatitudeCauchyValueProfile normal)) hCutoffSq

/-- Integrability of the value-profile square. -/
theorem canonicalLatitudeCauchyValueProfile_sq_integrable :
    Integrable
      (fun normal => canonicalLatitudeCauchyValueProfile normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure := by
  apply Integrable.of_bound
    (canonicalLatitudeCauchyValueProfile_contDiff.continuous.pow 2)
      |>.aestronglyMeasurable
    1
  exact Filter.Eventually.of_forall fun normal => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact canonicalLatitudeCauchyValueProfile_sq_le_one normal

/-- Integrability of the normal-profile square. -/
theorem canonicalLatitudeCauchyNormalProfile_sq_integrable :
    Integrable
      (fun normal => canonicalLatitudeCauchyNormalProfile normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure := by
  apply Integrable.of_bound
    (canonicalLatitudeCauchyNormalProfile_contDiff.continuous.pow 2)
      |>.aestronglyMeasurable
    1
  exact Filter.Eventually.of_forall fun normal => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact canonicalLatitudeCauchyNormalProfile_sq_le_one normal

/-- Canonical profile-integrability package. -/
def canonicalLatitudeCauchyJetProfileIntegrabilityData :
    CanonicalLatitudeCauchyJetProfileIntegrabilityData where
  value_sq_integrable := canonicalLatitudeCauchyValueProfile_sq_integrable
  normal_sq_integrable := canonicalLatitudeCauchyNormalProfile_sq_integrable

/-- Profile-integrability certificate. -/
theorem certificate :
    Integrable
        (fun normal => canonicalLatitudeCauchyValueProfile normal ^ 2)
        canonicalLatitudeCauchyJetNormalMeasure ∧
      Integrable
        (fun normal => canonicalLatitudeCauchyNormalProfile normal ^ 2)
        canonicalLatitudeCauchyJetNormalMeasure :=
  ⟨canonicalLatitudeCauchyValueProfile_sq_integrable,
    canonicalLatitudeCauchyNormalProfile_sq_integrable⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D
end JanusFormal
