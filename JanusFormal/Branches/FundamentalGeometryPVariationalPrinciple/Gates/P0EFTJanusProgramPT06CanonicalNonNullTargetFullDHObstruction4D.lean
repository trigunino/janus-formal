import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D

/-!
# Obstruction for the canonical non-null target to realize the full dH

The canonical cut-bulk affine jet current realizes the geometric
`bulk → nonNullBoundary` Stokes edge.  The fixed relative differential of Gate
819 also copies a bulk component into `nullBoundary`.  The geometric non-null
target has zero in that slot.

Consequently the full cochains agree exactly when the bulk integral vanishes.
Thus the currently constructed non-null-only target does not by itself realize
the missing `bulk → nullBoundary` component.  This does not rule out enriching
the same collar with an additional null restriction or constructing a separate
bulk-to-null restriction operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalNonNullTargetFullDHObstruction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Gate 819 sends the canonical bulk integral to the still-unrealized null
boundary slot as well as to the realized non-null slot. -/
theorem programPT06CanonicalNonNullJetCurrent_dH_nullBoundary
    (field test : SmoothQuotientField period hPeriod Real) :
    (programPT05ExactT03RelativeBicomplex.dH 4 0
      (programPT05CutBulkDensityIntegratedCochain period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
          field test))) .nullBoundary =
      (programPT05CutBulkDensityIntegral period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
          field test), 0) := by
  rfl

/-- The geometric canonical-collar target is supported only on the non-null
boundary slot. -/
theorem programPT06CanonicalNonNullJetCurrent_target_nullBoundary
    (field test : SmoothQuotientField period hPeriod Real) :
    (programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
      (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
        field test)) .nullBoundary = 0 := by
  rfl

/-- The realized non-null target equals the full relative differential exactly
when the copied bulk integral in the null slot vanishes. -/
theorem programPT06CanonicalNonNullJetCurrent_full_dH_eq_iff_bulkIntegral_eq_zero
    (field test : SmoothQuotientField period hPeriod Real) :
    programPT05ExactT03RelativeBicomplex.dH 4 0
        (programPT05CutBulkDensityIntegratedCochain period hPeriod
          (programPT06CanonicalCutBulkJetLocalDensityCochain
            period hPeriod field test)) =
      programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain
          period hPeriod field test) ↔
    programPT05CutBulkDensityIntegral period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain
          period hPeriod field test) = 0 := by
  constructor
  · intro hEquality
    have hNull := congrFun hEquality RelativeJetStratum4D.nullBoundary
    have hFirst := congrArg Prod.fst hNull
    simpa [programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential,
      programPT05CutBulkDensityIntegratedCochain,
      programPT05NonNullBoundaryDensityIntegratedCochain] using hFirst
  · intro hBulk
    funext stratum
    cases stratum with
    | bulk =>
        simp [programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          programPT05NonNullBoundaryDensityIntegratedCochain]
    | nonNullBoundary =>
        exact programPT06CanonicalCutBulkJetLocalDensity_dH_nonNull
          period hPeriod 0 field test
    | nullBoundary =>
        simp [programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          programPT05CutBulkDensityIntegratedCochain,
          programPT05NonNullBoundaryDensityIntegratedCochain, hBulk]
    | joint =>
        simp [programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          programPT05CutBulkDensityIntegratedCochain,
          programPT05NonNullBoundaryDensityIntegratedCochain]

/-- A nonzero canonical bulk integral witnesses that the non-null collar alone
does not realize the full relative horizontal differential. -/
theorem programPT06CanonicalNonNullJetCurrent_full_dH_ne_of_bulkIntegral_ne_zero
    (field test : SmoothQuotientField period hPeriod Real)
    (hBulk : programPT05CutBulkDensityIntegral period hPeriod
      (programPT06CanonicalCutBulkJetLocalDensityCochain
        period hPeriod field test) ≠ 0) :
    programPT05ExactT03RelativeBicomplex.dH 4 0
        (programPT05CutBulkDensityIntegratedCochain period hPeriod
          (programPT06CanonicalCutBulkJetLocalDensityCochain
            period hPeriod field test)) ≠
      programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain
          period hPeriod field test) := by
  intro hEquality
  exact hBulk
    ((programPT06CanonicalNonNullJetCurrent_full_dH_eq_iff_bulkIntegral_eq_zero
      period hPeriod field test).mp hEquality)

end
end P0EFTJanusProgramPT06CanonicalNonNullTargetFullDHObstruction4D
end JanusFormal
