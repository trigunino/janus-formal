import Mathlib.Analysis.Calculus.ContDiff.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D

/-!
# Normal calculus for the canonical latitude Cauchy jet

The explicit collar lift is

`E(g,h)(x,ν) = a(ν) g(x) + b(ν) h(x)`

with `a = η` and `b = ν η`.  This file records its complete one-dimensional
normal calculus.  The first and second normal derivatives are linear
combinations of the same boundary representatives with fixed smooth profile
coefficients.  These formulas are the input needed to realize and estimate the
physical Euler residual in product coarea coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open scoped ContDiff
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D

/-- First derivative of the value profile. -/
def canonicalLatitudeCauchyValueProfileDeriv (normal : Real) : Real :=
  deriv canonicalLatitudeCauchyValueProfile normal

/-- Second derivative of the value profile. -/
def canonicalLatitudeCauchyValueProfileSecondDeriv (normal : Real) : Real :=
  deriv canonicalLatitudeCauchyValueProfileDeriv normal

/-- First derivative of the normal profile. -/
def canonicalLatitudeCauchyNormalProfileDeriv (normal : Real) : Real :=
  deriv canonicalLatitudeCauchyNormalProfile normal

/-- Second derivative of the normal profile. -/
def canonicalLatitudeCauchyNormalProfileSecondDeriv (normal : Real) : Real :=
  deriv canonicalLatitudeCauchyNormalProfileDeriv normal

/-- Smoothness of the first value-profile derivative. -/
theorem canonicalLatitudeCauchyValueProfileDeriv_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyValueProfileDeriv := by
  unfold canonicalLatitudeCauchyValueProfileDeriv
  exact (contDiff_infty_iff_deriv.mp
    canonicalLatitudeCauchyValueProfile_contDiff).2

/-- Smoothness of the second value-profile derivative. -/
theorem canonicalLatitudeCauchyValueProfileSecondDeriv_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyValueProfileSecondDeriv := by
  unfold canonicalLatitudeCauchyValueProfileSecondDeriv
  exact (contDiff_infty_iff_deriv.mp
    canonicalLatitudeCauchyValueProfileDeriv_contDiff).2

/-- Smoothness of the first normal-profile derivative. -/
theorem canonicalLatitudeCauchyNormalProfileDeriv_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyNormalProfileDeriv := by
  unfold canonicalLatitudeCauchyNormalProfileDeriv
  exact (contDiff_infty_iff_deriv.mp
    canonicalLatitudeCauchyNormalProfile_contDiff).2

/-- Smoothness of the second normal-profile derivative. -/
theorem canonicalLatitudeCauchyNormalProfileSecondDeriv_contDiff :
    ContDiff Real ∞ canonicalLatitudeCauchyNormalProfileSecondDeriv := by
  unfold canonicalLatitudeCauchyNormalProfileSecondDeriv
  exact (contDiff_infty_iff_deriv.mp
    canonicalLatitudeCauchyNormalProfileDeriv_contDiff).2

@[simp] theorem canonicalLatitudeCauchyValueProfileDeriv_zero :
    canonicalLatitudeCauchyValueProfileDeriv 0 = 0 := by
  exact deriv_canonicalLatitudeCauchyValueProfile_zero

@[simp] theorem canonicalLatitudeCauchyNormalProfileDeriv_zero :
    canonicalLatitudeCauchyNormalProfileDeriv 0 = 1 := by
  exact deriv_canonicalLatitudeCauchyNormalProfile_zero

/-- First normal derivative of one local Cauchy slice. -/
def canonicalLatitudeLocalCauchyExtensionNormalDeriv
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeCauchyValueProfileDeriv normal * data.1 base +
    canonicalLatitudeCauchyNormalProfileDeriv normal * data.2 base

/-- Second normal derivative of one local Cauchy slice. -/
def canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeCauchyValueProfileSecondDeriv normal * data.1 base +
    canonicalLatitudeCauchyNormalProfileSecondDeriv normal * data.2 base

/-- Exact first normal derivative formula. -/
theorem deriv_canonicalLatitudeLocalCauchyExtensionSlice
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) :
    deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) normal =
      canonicalLatitudeLocalCauchyExtensionNormalDeriv data base normal := by
  unfold canonicalLatitudeLocalCauchyExtensionSlice
    canonicalLatitudeLocalCauchyExtension
    canonicalLatitudeLocalCauchyExtensionNormalDeriv
    canonicalLatitudeCauchyValueProfileDeriv
    canonicalLatitudeCauchyNormalProfileDeriv
  have hValue :=
    canonicalLatitudeCauchyValueProfile_contDiff.differentiable.differentiableAt
      |>.hasDerivAt
  have hNormal :=
    canonicalLatitudeCauchyNormalProfile_contDiff.differentiable.differentiableAt
      |>.hasDerivAt
  exact ((hValue.mul_const (data.1 base)).add
    (hNormal.mul_const (data.2 base))).deriv

/-- Exact second normal derivative formula. -/
theorem deriv_canonicalLatitudeLocalCauchyExtensionNormalDeriv
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) :
    deriv (canonicalLatitudeLocalCauchyExtensionNormalDeriv data base) normal =
      canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
        data base normal := by
  unfold canonicalLatitudeLocalCauchyExtensionNormalDeriv
    canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
    canonicalLatitudeCauchyValueProfileSecondDeriv
    canonicalLatitudeCauchyNormalProfileSecondDeriv
  have hValue :=
    canonicalLatitudeCauchyValueProfileDeriv_contDiff.differentiable
      |>.differentiableAt.hasDerivAt
  have hNormal :=
    canonicalLatitudeCauchyNormalProfileDeriv_contDiff.differentiable
      |>.differentiableAt.hasDerivAt
  exact ((hValue.mul_const (data.1 base)).add
    (hNormal.mul_const (data.2 base))).deriv

/-- Iterated derivative form of the second normal derivative. -/
theorem second_deriv_canonicalLatitudeLocalCauchyExtensionSlice
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) (normal : Real) :
    deriv (fun value =>
      deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) value) normal =
      canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
        data base normal := by
  have hFirst :
      (fun value =>
        deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) value) =
      canonicalLatitudeLocalCauchyExtensionNormalDeriv data base := by
    funext value
    exact deriv_canonicalLatitudeLocalCauchyExtensionSlice data base value
  rw [hFirst]
  exact deriv_canonicalLatitudeLocalCauchyExtensionNormalDeriv
    data base normal

/-- Smoothness of the first normal derivative of every local slice. -/
theorem canonicalLatitudeLocalCauchyExtensionNormalDeriv_contDiff
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞
      (canonicalLatitudeLocalCauchyExtensionNormalDeriv data base) := by
  unfold canonicalLatitudeLocalCauchyExtensionNormalDeriv
  exact
    (canonicalLatitudeCauchyValueProfileDeriv_contDiff.mul contDiff_const).add
      (canonicalLatitudeCauchyNormalProfileDeriv_contDiff.mul contDiff_const)

/-- Smoothness of the second normal derivative of every local slice. -/
theorem canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv_contDiff
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞
      (canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv data base) := by
  unfold canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
  exact
    (canonicalLatitudeCauchyValueProfileSecondDeriv_contDiff.mul contDiff_const).add
      (canonicalLatitudeCauchyNormalProfileSecondDeriv_contDiff.mul contDiff_const)

/-- Exact Cauchy jet recovered from the normal calculus. -/
theorem canonicalLatitudeLocalCauchyExtensionNormalDeriv_zero
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeLocalCauchyExtensionNormalDeriv data base 0 =
      data.2 base := by
  simp [canonicalLatitudeLocalCauchyExtensionNormalDeriv]

/-- Normal-calculus certificate. -/
theorem canonicalLatitudeCauchyJetNormalCalculus_certificate
    (data : (CanonicalLatitudeBase → Real) ×
      (CanonicalLatitudeBase → Real))
    (base : CanonicalLatitudeBase) :
    (∀ normal,
      deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) normal =
        canonicalLatitudeLocalCauchyExtensionNormalDeriv data base normal) ∧
      (∀ normal,
        deriv (fun value =>
          deriv (canonicalLatitudeLocalCauchyExtensionSlice data base) value)
            normal =
          canonicalLatitudeLocalCauchyExtensionNormalSecondDeriv
            data base normal) ∧
      canonicalLatitudeLocalCauchyExtensionNormalDeriv data base 0 =
        data.2 base :=
  ⟨deriv_canonicalLatitudeLocalCauchyExtensionSlice data base,
    second_deriv_canonicalLatitudeLocalCauchyExtensionSlice data base,
    canonicalLatitudeLocalCauchyExtensionNormalDeriv_zero data base⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D
end JanusFormal
