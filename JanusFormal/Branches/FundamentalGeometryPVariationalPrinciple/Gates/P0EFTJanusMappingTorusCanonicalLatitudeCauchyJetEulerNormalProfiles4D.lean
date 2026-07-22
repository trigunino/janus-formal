import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.L2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D

/-!
# The six canonical normal profiles in the Cauchy-jet Euler residual

A second-order scalar operator applied to

`E(g,h) = a(ν) g + b(ν) h`

uses exactly six fixed normal profiles:

`a`, `b`, `a'`, `b'`, `a''`, `b''`.

This file packages them as a finite type and proves square-integrability of every
profile for the weighted latitude measure.  The original profiles have compact
support in `[-1,1]`; support of a derivative is contained in topological support
of the original function, so the first and second derivatives remain compactly
supported.  Smooth compactly supported functions belong to every finite `L²`
normal measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal ContDiff
open MeasureTheory Set Topology Function
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D

/-- The finite family of normal profiles appearing in a second-order Euler
expansion. -/
inductive CanonicalLatitudeCauchyJetEulerNormalProfileIndex
  | value
  | normal
  | valueFirst
  | normalFirst
  | valueSecond
  | normalSecond
  deriving DecidableEq, Fintype

open CanonicalLatitudeCauchyJetEulerNormalProfileIndex

/-- The profile represented by one index. -/
def canonicalLatitudeCauchyJetEulerNormalProfile :
    CanonicalLatitudeCauchyJetEulerNormalProfileIndex → Real → Real
  | value => canonicalLatitudeCauchyValueProfile
  | normal => canonicalLatitudeCauchyNormalProfile
  | valueFirst => canonicalLatitudeCauchyValueProfileDeriv
  | normalFirst => canonicalLatitudeCauchyNormalProfileDeriv
  | valueSecond => canonicalLatitudeCauchyValueProfileSecondDeriv
  | normalSecond => canonicalLatitudeCauchyNormalProfileSecondDeriv

/-- Smoothness of every Euler normal profile. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfile_contDiff
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) :
    ContDiff Real ∞ (canonicalLatitudeCauchyJetEulerNormalProfile index) := by
  cases index <;>
    simp only [canonicalLatitudeCauchyJetEulerNormalProfile] <;>
    first
    | exact canonicalLatitudeCauchyValueProfile_contDiff
    | exact canonicalLatitudeCauchyNormalProfile_contDiff
    | exact canonicalLatitudeCauchyValueProfileDeriv_contDiff
    | exact canonicalLatitudeCauchyNormalProfileDeriv_contDiff
    | exact canonicalLatitudeCauchyValueProfileSecondDeriv_contDiff
    | exact canonicalLatitudeCauchyNormalProfileSecondDeriv_contDiff

/-- Compact support of the value profile. -/
theorem canonicalLatitudeCauchyValueProfile_hasCompactSupport :
    HasCompactSupport canonicalLatitudeCauchyValueProfile := by
  unfold HasCompactSupport tsupport
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal support_canonicalLatitudeCauchyValueProfile_subset
      isClosed_Icc)

/-- Compact support of the normal profile. -/
theorem canonicalLatitudeCauchyNormalProfile_hasCompactSupport :
    HasCompactSupport canonicalLatitudeCauchyNormalProfile := by
  unfold HasCompactSupport tsupport
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal support_canonicalLatitudeCauchyNormalProfile_subset
      isClosed_Icc)

/-- Compact support of every Euler normal profile. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfile_hasCompactSupport
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) :
    HasCompactSupport (canonicalLatitudeCauchyJetEulerNormalProfile index) := by
  cases index
  · exact canonicalLatitudeCauchyValueProfile_hasCompactSupport
  · exact canonicalLatitudeCauchyNormalProfile_hasCompactSupport
  · exact canonicalLatitudeCauchyValueProfile_hasCompactSupport.deriv
  · exact canonicalLatitudeCauchyNormalProfile_hasCompactSupport.deriv
  · exact canonicalLatitudeCauchyValueProfile_hasCompactSupport.deriv.deriv
  · exact canonicalLatitudeCauchyNormalProfile_hasCompactSupport.deriv.deriv

/-- Local finiteness of the weighted normal measure. -/
local instance canonicalLatitudeCauchyJetNormalMeasureLocallyFinite :
    IsLocallyFiniteMeasure canonicalLatitudeCauchyJetNormalMeasure := by
  apply IsLocallyFiniteMeasure.of_le
    (volume.restrict
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  exact canonicalLatitudeCauchyJetNormalMeasure_le_restrictVolume

/-- Every Euler normal profile belongs to weighted normal `L²`. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfile_memLp
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) :
    MemLp (canonicalLatitudeCauchyJetEulerNormalProfile index)
      (2 : ENNReal) canonicalLatitudeCauchyJetNormalMeasure :=
  (canonicalLatitudeCauchyJetEulerNormalProfile_contDiff index).continuous
    |>.memLp_of_hasCompactSupport
      (canonicalLatitudeCauchyJetEulerNormalProfile_hasCompactSupport index)

/-- Square-integrability of every Euler normal profile. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfile_sq_integrable
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) :
    Integrable
      (fun normal =>
        canonicalLatitudeCauchyJetEulerNormalProfile index normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure := by
  rw [← memLp_two_iff_integrable_sq]
  exact canonicalLatitudeCauchyJetEulerNormalProfile_memLp index

/-- Squared moment of one Euler normal profile. -/
def canonicalLatitudeCauchyJetEulerNormalProfileMoment
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) : Real :=
  ∫ normal,
    canonicalLatitudeCauchyJetEulerNormalProfile index normal ^ 2
    ∂canonicalLatitudeCauchyJetNormalMeasure

/-- Every profile moment is finite and nonnegative. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfileMoment_nonnegative
    (index : CanonicalLatitudeCauchyJetEulerNormalProfileIndex) :
    0 ≤ canonicalLatitudeCauchyJetEulerNormalProfileMoment index := by
  unfold canonicalLatitudeCauchyJetEulerNormalProfileMoment
  exact integral_nonneg fun _ => sq_nonneg _

/-- Six-profile normal certificate. -/
theorem canonicalLatitudeCauchyJetEulerNormalProfiles_certificate :
    (∀ index,
      ContDiff Real ∞
        (canonicalLatitudeCauchyJetEulerNormalProfile index)) ∧
      (∀ index,
        Integrable
          (fun normal =>
            canonicalLatitudeCauchyJetEulerNormalProfile index normal ^ 2)
          canonicalLatitudeCauchyJetNormalMeasure) ∧
      (∀ index,
        0 ≤ canonicalLatitudeCauchyJetEulerNormalProfileMoment index) :=
  ⟨canonicalLatitudeCauchyJetEulerNormalProfile_contDiff,
    canonicalLatitudeCauchyJetEulerNormalProfile_sq_integrable,
    canonicalLatitudeCauchyJetEulerNormalProfileMoment_nonnegative⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D
end JanusFormal
