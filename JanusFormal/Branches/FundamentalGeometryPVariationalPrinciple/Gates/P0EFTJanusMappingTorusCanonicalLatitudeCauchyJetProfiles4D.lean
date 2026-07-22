import Mathlib.Analysis.Calculus.FDeriv.Congr
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-!
# Exact latitude Cauchy-jet profiles

The canonical collar bump is identically one near the throat.  Hence the two
profiles

`a(ν) = η(ν)` and `b(ν) = ν η(ν)`

have exact first jets

`a(0)=1`, `a'(0)=0`, `b(0)=0`, `b'(0)=1`.

For boundary value and normal data `(g,h)`, the local collar expression

`E(g,h)(x,ν) = a(ν) g(x) + b(ν) h(x)`

therefore realizes the prescribed Cauchy jet.  This file isolates the complete
one-dimensional interpolation argument needed by the global smooth Cauchy
extension.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open scoped ContDiff
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-- Value profile: one near the throat and compactly supported in the latitude
band. -/
def canonicalLatitudeCauchyValueProfile (normal : Real) : Real :=
  canonicalLatitudeCollarCutoff normal

/-- Normal profile: the normal coordinate near the throat and compactly
supported in the latitude band. -/
def canonicalLatitudeCauchyNormalProfile (normal : Real) : Real :=
  normal * canonicalLatitudeCollarCutoff normal

/-- Smoothness of the value profile. -/
theorem canonicalLatitudeCauchyValueProfile_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyValueProfile := by
  simpa [canonicalLatitudeCauchyValueProfile] using
    canonicalLatitudeCollarCutoff_contDiff

/-- Smoothness of the normal profile. -/
theorem canonicalLatitudeCauchyNormalProfile_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyNormalProfile := by
  unfold canonicalLatitudeCauchyNormalProfile
  exact contDiff_id.mul canonicalLatitudeCollarCutoff_contDiff

/-- The value profile is locally exactly one. -/
theorem canonicalLatitudeCauchyValueProfile_eventuallyEq_one :
    canonicalLatitudeCauchyValueProfile =ᶠ[𝓝 0]
      fun _ : Real => 1 := by
  simpa [canonicalLatitudeCauchyValueProfile] using
    (canonicalLatitudeCollarCutoff.eventuallyEq_one)

/-- The normal profile is locally exactly the identity. -/
theorem canonicalLatitudeCauchyNormalProfile_eventuallyEq_id :
    canonicalLatitudeCauchyNormalProfile =ᶠ[𝓝 0]
      fun normal : Real => normal := by
  filter_upwards [canonicalLatitudeCauchyValueProfile_eventuallyEq_one]
    with normal hNormal
  simp [canonicalLatitudeCauchyNormalProfile,
    canonicalLatitudeCauchyValueProfile] at hNormal ⊢
  rw [hNormal, mul_one]

/-- Exact value jet of the value profile. -/
@[simp] theorem canonicalLatitudeCauchyValueProfile_zero :
    canonicalLatitudeCauchyValueProfile 0 = 1 := by
  exact canonicalLatitudeCauchyValueProfile_eventuallyEq_one.eq_of_nhds

/-- Exact value jet of the normal profile. -/
@[simp] theorem canonicalLatitudeCauchyNormalProfile_zero :
    canonicalLatitudeCauchyNormalProfile 0 = 0 := by
  simp [canonicalLatitudeCauchyNormalProfile]

/-- The value profile has zero derivative at the throat. -/
theorem canonicalLatitudeCauchyValueProfile_hasDerivAt_zero :
    HasDerivAt canonicalLatitudeCauchyValueProfile 0 0 := by
  exact (hasDerivAt_const (x := (0 : Real)) (c := (1 : Real)))
    |>.congr_of_eventuallyEq
      canonicalLatitudeCauchyValueProfile_eventuallyEq_one

/-- The normal profile has unit derivative at the throat. -/
theorem canonicalLatitudeCauchyNormalProfile_hasDerivAt_zero :
    HasDerivAt canonicalLatitudeCauchyNormalProfile 1 0 := by
  exact (hasDerivAt_id (x := (0 : Real)))
    |>.congr_of_eventuallyEq
      canonicalLatitudeCauchyNormalProfile_eventuallyEq_id

@[simp] theorem deriv_canonicalLatitudeCauchyValueProfile_zero :
    deriv canonicalLatitudeCauchyValueProfile 0 = 0 :=
  canonicalLatitudeCauchyValueProfile_hasDerivAt_zero.deriv

@[simp] theorem deriv_canonicalLatitudeCauchyNormalProfile_zero :
    deriv canonicalLatitudeCauchyNormalProfile 0 = 1 :=
  canonicalLatitudeCauchyNormalProfile_hasDerivAt_zero.deriv

/-- Local collar Cauchy extension of a value/normal pair. -/
def canonicalLatitudeLocalCauchyExtension
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (parameter : CanonicalLatitudeBase × Real) : Real :=
  canonicalLatitudeCauchyValueProfile parameter.2 * data.1 parameter.1 +
    canonicalLatitudeCauchyNormalProfile parameter.2 * data.2 parameter.1

/-- Linearity of the local Cauchy extension. -/
def canonicalLatitudeLocalCauchyExtensionLinearMap :
    ((CanonicalLatitudeBase → Real) ×
        (CanonicalLatitudeBase → Real)) →ₗ[Real]
      (CanonicalLatitudeBase × Real → Real) where
  toFun := canonicalLatitudeLocalCauchyExtension
  map_add' first second := by
    funext parameter
    simp [canonicalLatitudeLocalCauchyExtension]
    ring
  map_smul' scalar data := by
    funext parameter
    simp [canonicalLatitudeLocalCauchyExtension]
    ring

@[simp] theorem canonicalLatitudeLocalCauchyExtensionLinearMap_apply
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (parameter : CanonicalLatitudeBase × Real) :
    canonicalLatitudeLocalCauchyExtensionLinearMap data parameter =
      canonicalLatitudeLocalCauchyExtension data parameter :=
  rfl

/-- Normal slice of the local extension at one boundary base point. -/
def canonicalLatitudeLocalCauchyExtensionSlice
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeLocalCauchyExtension data (base, normal)

/-- Every local extension slice is smooth. -/
theorem canonicalLatitudeLocalCauchyExtensionSlice_contDiff
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞
      (canonicalLatitudeLocalCauchyExtensionSlice data base) := by
  unfold canonicalLatitudeLocalCauchyExtensionSlice
  unfold canonicalLatitudeLocalCauchyExtension
  exact
    (canonicalLatitudeCauchyValueProfile_contDiff.mul contDiff_const).add
      (canonicalLatitudeCauchyNormalProfile_contDiff.mul contDiff_const)

/-- Near the throat the local extension is exactly its affine Cauchy jet. -/
theorem canonicalLatitudeLocalCauchyExtensionSlice_eventuallyEq_affine
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeLocalCauchyExtensionSlice data base =ᶠ[𝓝 0]
      fun normal => data.1 base + normal * data.2 base := by
  filter_upwards
    [canonicalLatitudeCauchyValueProfile_eventuallyEq_one,
     canonicalLatitudeCauchyNormalProfile_eventuallyEq_id]
    with normal hValue hNormal
  unfold canonicalLatitudeLocalCauchyExtensionSlice
  unfold canonicalLatitudeLocalCauchyExtension
  rw [hValue, hNormal]
  ring

/-- Exact boundary value of the local Cauchy extension. -/
@[simp] theorem canonicalLatitudeLocalCauchyExtensionSlice_zero
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeLocalCauchyExtensionSlice data base 0 = data.1 base := by
  rw [canonicalLatitudeLocalCauchyExtensionSlice_eventuallyEq_affine
    data base |>.eq_of_nhds]
  ring

/-- Exact normal derivative of the local Cauchy extension. -/
theorem canonicalLatitudeLocalCauchyExtensionSlice_hasDerivAt_zero
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    HasDerivAt (canonicalLatitudeLocalCauchyExtensionSlice data base)
      (data.2 base) 0 := by
  have hAffine : HasDerivAt
      (fun normal : Real => data.1 base + normal * data.2 base)
      (data.2 base) 0 := by
    convert
      (hasDerivAt_const (x := (0 : Real)) (c := data.1 base)).add
        ((hasDerivAt_id (x := (0 : Real))).mul_const (data.2 base)) using 1
    ring
  exact hAffine.congr_of_eventuallyEq
    (canonicalLatitudeLocalCauchyExtensionSlice_eventuallyEq_affine data base)

@[simp] theorem deriv_canonicalLatitudeLocalCauchyExtensionSlice_zero
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) 0 =
      data.2 base :=
  (canonicalLatitudeLocalCauchyExtensionSlice_hasDerivAt_zero data base).deriv

/-- Complete local Cauchy-jet interpolation certificate. -/
theorem canonicalLatitudeLocalCauchyExtension_certificate
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real)) :
    (∀ base,
      canonicalLatitudeLocalCauchyExtensionSlice data base 0 = data.1 base) ∧
      (∀ base,
        deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) 0 =
          data.2 base) ∧
      (∀ base,
        ContDiff Real ∞
          (canonicalLatitudeLocalCauchyExtensionSlice data base)) :=
  ⟨canonicalLatitudeLocalCauchyExtensionSlice_zero data,
    deriv_canonicalLatitudeLocalCauchyExtensionSlice_zero data,
    canonicalLatitudeLocalCauchyExtensionSlice_contDiff data⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
end JanusFormal
