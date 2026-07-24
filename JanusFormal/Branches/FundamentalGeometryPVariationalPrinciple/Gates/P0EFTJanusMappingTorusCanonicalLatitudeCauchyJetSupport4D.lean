import Mathlib.Analysis.Real.Pi.Bounds
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D

/-!
# Strict interior support of the latitude Cauchy jet

Both exact Cauchy profiles are supported in `|ν| < 1`.  Since `1 < π/2`, their
support lies strictly inside the genuine equatorial tubular band
`(-π/2,π/2)`.  Consequently the local Cauchy extension is identically zero on a
full neighborhood of either latitude pole.  This is the geometric separation
needed for a smooth extension by zero.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-- The value profile vanishes outside the unit normal band. -/
theorem canonicalLatitudeCauchyValueProfile_eq_zero_of_one_le_abs
    (normal : Real) (hNormal : 1 ≤ |normal|) :
    canonicalLatitudeCauchyValueProfile normal = 0 := by
  exact canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs normal hNormal

/-- The normal profile vanishes outside the unit normal band. -/
theorem canonicalLatitudeCauchyNormalProfile_eq_zero_of_one_le_abs
    (normal : Real) (hNormal : 1 ≤ |normal|) :
    canonicalLatitudeCauchyNormalProfile normal = 0 := by
  unfold canonicalLatitudeCauchyNormalProfile
  rw [canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs normal hNormal,
    mul_zero]

/-- The complete local Cauchy extension vanishes outside the unit normal band. -/
theorem canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : 1 ≤ |normal|) :
    canonicalLatitudeLocalCauchyExtension data (base, normal) = 0 := by
  unfold canonicalLatitudeLocalCauchyExtension
  rw [canonicalLatitudeCauchyValueProfile_eq_zero_of_one_le_abs normal hNormal,
    canonicalLatitudeCauchyNormalProfile_eq_zero_of_one_le_abs normal hNormal]
  ring

/-- The support of the value profile is contained in the open unit interval. -/
theorem support_canonicalLatitudeCauchyValueProfile_subset :
    Function.support canonicalLatitudeCauchyValueProfile ⊆
      Set.Ioo (-1 : Real) 1 := by
  intro normal hSupport
  rw [Function.mem_support] at hSupport
  have hAbs : |normal| < 1 := by
    by_contra hNot
    apply hSupport
    exact canonicalLatitudeCauchyValueProfile_eq_zero_of_one_le_abs
      normal (not_lt.mp hNot)
  exact (abs_lt.mp hAbs)

/-- The support of the normal profile is contained in the open unit interval. -/
theorem support_canonicalLatitudeCauchyNormalProfile_subset :
    Function.support canonicalLatitudeCauchyNormalProfile ⊆
      Set.Ioo (-1 : Real) 1 := by
  intro normal hSupport
  rw [Function.mem_support] at hSupport
  have hAbs : |normal| < 1 := by
    by_contra hNot
    apply hSupport
    exact canonicalLatitudeCauchyNormalProfile_eq_zero_of_one_le_abs
      normal (not_lt.mp hNot)
  exact (abs_lt.mp hAbs)

/-- The support of every local extension slice is contained in the unit band. -/
theorem support_canonicalLatitudeLocalCauchyExtensionSlice_subset
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    Function.support
        (canonicalLatitudeLocalCauchyExtensionSlice data base) ⊆
      Set.Ioo (-1 : Real) 1 := by
  intro normal hSupport
  rw [Function.mem_support] at hSupport
  have hAbs : |normal| < 1 := by
    by_contra hNot
    apply hSupport
    unfold canonicalLatitudeLocalCauchyExtensionSlice
    exact canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
      data base normal (not_lt.mp hNot)
  exact abs_lt.mp hAbs

/-- The unit support radius lies strictly below the latitude pole. -/
theorem one_lt_pi_div_two : (1 : Real) < Real.pi / 2 := by
  nlinarith [Real.pi_gt_three]

/-- The closed unit normal band lies inside the open tubular band. -/
theorem Icc_neg_one_one_subset_latitudeBand :
    Set.Icc (-1 : Real) 1 ⊆
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  intro normal hNormal
  constructor
  · exact lt_of_lt_of_le (neg_lt_neg one_lt_pi_div_two) hNormal.1
  · exact hNormal.2.trans_lt one_lt_pi_div_two

/-- The closure of each profile support stays inside the genuine tubular band. -/
theorem closure_support_canonicalLatitudeCauchyValueProfile_subset_latitudeBand :
    closure (Function.support canonicalLatitudeCauchyValueProfile) ⊆
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  refine Set.Subset.trans ?_ Icc_neg_one_one_subset_latitudeBand
  apply closure_minimal
  · intro normal hNormal
    have hOpen :=
      support_canonicalLatitudeCauchyValueProfile_subset hNormal
    exact ⟨hOpen.1.le, hOpen.2.le⟩
  · exact isClosed_Icc

/-- The closure of the normal-profile support also stays inside the genuine
 tubular band. -/
theorem closure_support_canonicalLatitudeCauchyNormalProfile_subset_latitudeBand :
    closure (Function.support canonicalLatitudeCauchyNormalProfile) ⊆
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  refine Set.Subset.trans ?_ Icc_neg_one_one_subset_latitudeBand
  apply closure_minimal
  · intro normal hNormal
    have hOpen :=
      support_canonicalLatitudeCauchyNormalProfile_subset hNormal
    exact ⟨hOpen.1.le, hOpen.2.le⟩
  · exact isClosed_Icc

/-- The local extension is identically zero near the positive latitude pole. -/
theorem canonicalLatitudeLocalCauchyExtensionSlice_eventuallyEq_zero_at_pos_pole
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeLocalCauchyExtensionSlice data base =ᶠ[
        𝓝 (Real.pi / 2)]
      fun _ : Real => 0 := by
  have hPole : (Real.pi / 2 : Real) ∈ Set.Ioi 1 := one_lt_pi_div_two
  filter_upwards [isOpen_Ioi.mem_nhds hPole] with normal hNormal
  unfold canonicalLatitudeLocalCauchyExtensionSlice
  apply canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
  exact hNormal.le.trans (le_abs_self normal)

/-- The local extension is identically zero near the negative latitude pole. -/
theorem canonicalLatitudeLocalCauchyExtensionSlice_eventuallyEq_zero_at_neg_pole
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeLocalCauchyExtensionSlice data base =ᶠ[
        𝓝 (-(Real.pi / 2))]
      fun _ : Real => 0 := by
  have hPole : (-(Real.pi / 2) : Real) ∈ Set.Iio (-1) := by
    exact neg_lt_neg one_lt_pi_div_two
  filter_upwards [isOpen_Iio.mem_nhds hPole] with normal hNormal
  unfold canonicalLatitudeLocalCauchyExtensionSlice
  apply canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
  have hNeg : 1 < -normal := by
    have hNormal' : normal < -1 := hNormal
    simpa using (neg_lt_neg hNormal')
  exact hNeg.le.trans (neg_le_abs normal)

/-- Strict-support certificate for the exact Cauchy profiles. -/
theorem canonicalLatitudeCauchyJetSupport_certificate
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    Function.support
        (canonicalLatitudeLocalCauchyExtensionSlice data base) ⊆
      Set.Ioo (-1 : Real) 1 ∧
      closure (Function.support canonicalLatitudeCauchyValueProfile) ⊆
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      closure (Function.support canonicalLatitudeCauchyNormalProfile) ⊆
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨support_canonicalLatitudeLocalCauchyExtensionSlice_subset data base,
    closure_support_canonicalLatitudeCauchyValueProfile_subset_latitudeBand,
    closure_support_canonicalLatitudeCauchyNormalProfile_subset_latitudeBand⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
end JanusFormal
