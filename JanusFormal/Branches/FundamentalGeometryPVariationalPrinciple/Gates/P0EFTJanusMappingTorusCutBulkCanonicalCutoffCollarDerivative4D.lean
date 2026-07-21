import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D

/-!
# Collar derivatives of the global canonical cutoff
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarDerivative4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Along every interior collar fiber, the genuine global cutoff has exactly
the derivative of the canonical one-dimensional bump. -/
theorem cutBulkCanonicalCutoff_canonicalCollarFiber_hasDerivAt
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt
      (fun current ↦ cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (base, current)))
      (deriv canonicalLatitudeCollarCutoff normal) normal := by
  have hEventually : Filter.EventuallyEq (nhds normal)
      (fun current ↦ cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (base, current)))
      canonicalLatitudeCollarCutoff := by
    filter_upwards [isOpen_Ioo.mem_nhds hNormal] with current hCurrent
    exact cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
      period hPeriod base current ⟨hCurrent.1.le, hCurrent.2.le⟩
  have hDerivative : HasDerivAt canonicalLatitudeCollarCutoff
      (deriv canonicalLatitudeCollarCutoff normal) normal :=
    (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  exact hDerivative.congr_of_eventuallyEq hEventually

theorem deriv_cutBulkCanonicalCutoff_canonicalCollarFiber
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    deriv
      (fun current ↦ cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (base, current))) normal =
      deriv canonicalLatitudeCollarCutoff normal :=
  (cutBulkCanonicalCutoff_canonicalCollarFiber_hasDerivAt period hPeriod
    base normal hNormal).deriv

/-- At fixed normal coordinate, the global cutoff is independent of the
collar base point. -/
theorem cutBulkCanonicalCutoff_canonicalCollar_base_independent
    (firstBase secondBase : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (firstBase, normal)) =
      cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (secondBase, normal)) := by
  rw [cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
      period hPeriod firstBase normal hNormal,
    cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
      period hPeriod secondBase normal hNormal]

/-- Consequently every real curve contained in a fixed-normal collar slice
sees zero cutoff derivative, without any regularity assumption on the curve. -/
theorem cutBulkCanonicalCutoff_fixedNormalBaseCurve_hasDerivAt_zero
    (curve : Real → CanonicalLatitudeBase) (parameter normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    HasDerivAt
      (fun current ↦ cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod
          (curve current, normal))) 0 parameter := by
  have hEq :
      (fun current ↦ cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod
          (curve current, normal))) =
        fun _ ↦ canonicalLatitudeCollarCutoff normal := by
    funext current
    exact cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
      period hPeriod (curve current) normal hNormal
  rw [hEq]
  exact hasDerivAt_const parameter _

end
end P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarDerivative4D
end JanusFormal
