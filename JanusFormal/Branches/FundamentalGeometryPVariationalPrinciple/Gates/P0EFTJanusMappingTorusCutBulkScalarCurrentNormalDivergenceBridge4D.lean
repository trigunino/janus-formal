import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D

/-!
# Normal-divergence bridge for the global cut-bulk current

Inside the positive collar, the ordinary derivative of the global current
along the canonical clamped collar path is exactly the previously defined
densitized normal divergence.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Total real parametrization obtained by clamping the normal coordinate to
the closed positive collar. -/
def canonicalLatitudeCutBulkCollarPath
    (base : CanonicalLatitudeBase) (normal : Real) :
    PositiveHemisphereCutBulk period hPeriod :=
  canonicalLatitudeCutBulkCollarLift period hPeriod base
    (Set.projIcc 0 1 zero_le_one normal)

theorem cutBulkScalarCurrent_canonicalCollarPath
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal) =
      cutoffCollarScalarCurrentDensity period hPeriod field test base
        (Set.projIcc 0 1 zero_le_one normal).1 := by
  exact cutBulkScalarCurrent_canonicalCollarLift
    period hPeriod field test base _

/-- Interior normal derivative of the actual global current. -/
theorem cutBulkScalarCurrent_canonicalCollarPath_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt
      (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current))
      (cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal) normal := by
  have hEventually :
      (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) =ᶠ[𝓝 normal]
      cutoffCollarScalarCurrentDensity period hPeriod field test base := by
    filter_upwards [isOpen_Ioo.mem_nhds hNormal] with current hCurrent
    rw [cutBulkScalarCurrent_canonicalCollarPath]
    simp [Set.projIcc_of_mem zero_le_one ⟨hCurrent.1.le, hCurrent.2.le⟩]
  exact (cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod massSquared
    field test base normal).congr_of_eventuallyEq hEventually

theorem deriv_cutBulkScalarCurrent_canonicalCollarPath
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal =
      cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal :=
  (cutBulkScalarCurrent_canonicalCollarPath_hasDerivAt period hPeriod
    massSquared field test base normal hNormal).deriv

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
end JanusFormal
