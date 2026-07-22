import Mathlib.Analysis.SpecificLimits.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-!
# Shrinking latitude profiles for the physical minimal core

Starting from the existing smooth bump `canonicalLatitudeCollarCutoff`, equal to
one on `|normal| ≤ 1/2` and zero on `1 ≤ |normal|`, define

`chi_n(normal) = 1 - bump((n+1) normal)`.

Then `chi_n` is smooth, takes values in `[0,1]`, is identically zero in a
neighborhood of the throat, and is eventually equal to one at every nonzero
normal coordinate.  Multiplication by this profile therefore kills both value
and normal traces while converging pointwise to the identity away from the
measure-zero throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffProfile4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open scoped ContDiff
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-- Positive dilation factor of the `n`th shrinking collar. -/
def canonicalLatitudeMinimalCutoffScale (index : Nat) : Real :=
  index + 1

/-- The dilation factor is positive. -/
theorem canonicalLatitudeMinimalCutoffScale_pos (index : Nat) :
    0 < canonicalLatitudeMinimalCutoffScale index := by
  unfold canonicalLatitudeMinimalCutoffScale
  positivity

/-- The dilation factor is nonnegative. -/
theorem canonicalLatitudeMinimalCutoffScale_nonnegative (index : Nat) :
    0 ≤ canonicalLatitudeMinimalCutoffScale index :=
  (canonicalLatitudeMinimalCutoffScale_pos index).le

/-- Shrinking complement of the canonical collar bump. -/
def canonicalLatitudeMinimalCutoffProfile
    (index : Nat) (normal : Real) : Real :=
  1 - canonicalLatitudeCollarCutoff
    (canonicalLatitudeMinimalCutoffScale index * normal)

/-- Smoothness of every shrinking profile. -/
theorem canonicalLatitudeMinimalCutoffProfile_contDiff
    (index : Nat) :
    ContDiff Real ∞ (canonicalLatitudeMinimalCutoffProfile index) := by
  unfold canonicalLatitudeMinimalCutoffProfile
  exact contDiff_const.sub
    (canonicalLatitudeCollarCutoff_contDiff.comp
      (contDiff_const.mul contDiff_id))

/-- The profile is nonnegative. -/
theorem canonicalLatitudeMinimalCutoffProfile_nonnegative
    (index : Nat) (normal : Real) :
    0 ≤ canonicalLatitudeMinimalCutoffProfile index normal := by
  unfold canonicalLatitudeMinimalCutoffProfile
  linarith [ContDiffBump.le_one
    (canonicalLatitudeCollarCutoff
      (canonicalLatitudeMinimalCutoffScale index * normal))]

/-- The profile is at most one. -/
theorem canonicalLatitudeMinimalCutoffProfile_le_one
    (index : Nat) (normal : Real) :
    canonicalLatitudeMinimalCutoffProfile index normal ≤ 1 := by
  unfold canonicalLatitudeMinimalCutoffProfile
  linarith [ContDiffBump.nonneg
    (canonicalLatitudeCollarCutoff
      (canonicalLatitudeMinimalCutoffScale index * normal))]

/-- The profile vanishes wherever the dilated coordinate lies in the bump's
unit region. -/
theorem canonicalLatitudeMinimalCutoffProfile_eq_zero_of_scaled_abs_le_half
    (index : Nat) (normal : Real)
    (hNormal :
      |canonicalLatitudeMinimalCutoffScale index * normal| ≤ 1 / 2) :
    canonicalLatitudeMinimalCutoffProfile index normal = 0 := by
  unfold canonicalLatitudeMinimalCutoffProfile
  rw [canonicalLatitudeCollarCutoff_eq_one _ hNormal]
  ring

/-- The profile is one outside the dilated support of the bump. -/
theorem canonicalLatitudeMinimalCutoffProfile_eq_one_of_one_le_scaled_abs
    (index : Nat) (normal : Real)
    (hNormal :
      1 ≤ |canonicalLatitudeMinimalCutoffScale index * normal|) :
    canonicalLatitudeMinimalCutoffProfile index normal = 1 := by
  unfold canonicalLatitudeMinimalCutoffProfile
  rw [canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs _ hNormal]
  ring

/-- Every shrinking profile vanishes at the throat. -/
@[simp] theorem canonicalLatitudeMinimalCutoffProfile_zero
    (index : Nat) :
    canonicalLatitudeMinimalCutoffProfile index 0 = 0 := by
  apply canonicalLatitudeMinimalCutoffProfile_eq_zero_of_scaled_abs_le_half
  norm_num

/-- Every shrinking profile is locally identically zero near the throat. -/
theorem canonicalLatitudeMinimalCutoffProfile_eventuallyEq_zero
    (index : Nat) :
    canonicalLatitudeMinimalCutoffProfile index =ᶠ[𝓝 0]
      fun _ : Real => 0 := by
  let scale := canonicalLatitudeMinimalCutoffScale index
  have hContinuous : Continuous (fun normal : Real => |scale * normal|) :=
    continuous_abs.comp (continuous_const.mul continuous_id)
  have hOpen : IsOpen {normal : Real | |scale * normal| < 1 / 2} :=
    isOpen_lt hContinuous continuous_const
  have hMem : (0 : Real) ∈ {normal : Real | |scale * normal| < 1 / 2} := by
    norm_num
  filter_upwards [hOpen.mem_nhds hMem] with normal hNormal
  exact canonicalLatitudeMinimalCutoffProfile_eq_zero_of_scaled_abs_le_half
    index normal (le_of_lt hNormal)

/-- A field multiplied by the profile is locally zero near the throat, hence
all of its ordinary derivatives vanish there. -/
theorem canonicalLatitudeMinimalCutoffProfile_mul_eventuallyEq_zero
    (index : Nat) (field : Real → Real) :
    (fun normal => canonicalLatitudeMinimalCutoffProfile index normal *
      field normal) =ᶠ[𝓝 0] fun _ : Real => 0 := by
  filter_upwards
    [canonicalLatitudeMinimalCutoffProfile_eventuallyEq_zero index]
    with normal hProfile
  rw [hProfile, zero_mul]

/-- Arithmetic lower bound used for eventual escape from the bump support. -/
theorem one_le_scale_mul_abs_of_large
    (normal : Real) (hNormal : normal ≠ 0)
    (index : Nat)
    (hLarge : 1 / |normal| ≤ (index : Real)) :
    1 ≤ canonicalLatitudeMinimalCutoffScale index * |normal| := by
  have hAbsPos : 0 < |normal| := abs_pos.mpr hNormal
  have hIndex : 1 ≤ (index : Real) * |normal| := by
    have hMultiply := mul_le_mul_of_nonneg_right hLarge hAbsPos.le
    rw [div_mul_cancel₀ 1 (ne_of_gt hAbsPos)] at hMultiply
    exact hMultiply
  have hScaleIndex : (index : Real) ≤
      canonicalLatitudeMinimalCutoffScale index := by
    unfold canonicalLatitudeMinimalCutoffScale
    norm_num
  exact hIndex.trans
    (mul_le_mul_of_nonneg_right hScaleIndex hAbsPos.le)

/-- At every nonzero normal coordinate, the shrinking profiles are eventually
exactly one. -/
theorem canonicalLatitudeMinimalCutoffProfile_eventuallyEq_one
    (normal : Real) (hNormal : normal ≠ 0) :
    (fun index : Nat => canonicalLatitudeMinimalCutoffProfile index normal) =ᶠ[atTop]
      fun _ => 1 := by
  obtain ⟨threshold, hThreshold⟩ := exists_nat_ge (1 / |normal|)
  filter_upwards [eventually_ge_atTop threshold] with index hIndex
  have hCast : (threshold : Real) ≤ (index : Real) := by
    exact_mod_cast hIndex
  have hLarge : 1 / |normal| ≤ (index : Real) :=
    hThreshold.trans hCast
  apply canonicalLatitudeMinimalCutoffProfile_eq_one_of_one_le_scaled_abs
  rw [abs_mul, abs_of_nonneg
    (canonicalLatitudeMinimalCutoffScale_nonnegative index)]
  exact one_le_scale_mul_abs_of_large normal hNormal index hLarge

/-- Pointwise convergence to one away from the throat. -/
theorem canonicalLatitudeMinimalCutoffProfile_tendsto_one
    (normal : Real) (hNormal : normal ≠ 0) :
    Tendsto
      (fun index : Nat => canonicalLatitudeMinimalCutoffProfile index normal)
      atTop (𝓝 1) :=
  (canonicalLatitudeMinimalCutoffProfile_eventuallyEq_one normal hNormal).tendsto

/-- Complete shrinking-profile certificate. -/
theorem canonicalLatitudeMinimalCutoffProfile_certificate
    (index : Nat) :
    ContDiff Real ∞ (canonicalLatitudeMinimalCutoffProfile index) ∧
      (∀ normal, 0 ≤ canonicalLatitudeMinimalCutoffProfile index normal) ∧
      (∀ normal, canonicalLatitudeMinimalCutoffProfile index normal ≤ 1) ∧
      canonicalLatitudeMinimalCutoffProfile index =ᶠ[𝓝 0]
        fun _ : Real => 0 :=
  ⟨canonicalLatitudeMinimalCutoffProfile_contDiff index,
    canonicalLatitudeMinimalCutoffProfile_nonnegative index,
    canonicalLatitudeMinimalCutoffProfile_le_one index,
    canonicalLatitudeMinimalCutoffProfile_eventuallyEq_zero index⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffProfile4D
end JanusFormal
