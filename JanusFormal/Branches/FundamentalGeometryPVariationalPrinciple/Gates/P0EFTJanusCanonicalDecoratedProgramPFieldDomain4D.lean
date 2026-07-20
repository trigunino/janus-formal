import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D

/-! # Canonical decorated Program-P field domain -/

namespace JanusFormal
namespace P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- One actual same-base package containing the canonical decorated geometry,
the existing common field/operator/boundary domain, and the linear inclusion
of independent variations into the complete tangent space. -/
structure CanonicalDecoratedProgramPFieldDomain where
  decorations : CanonicalEffectiveDecoratedMappingTorus period hPeriod
  fieldDomain : ProgramPCommonGeometricDomain4D period hPeriod
  independentVariationEmbedding :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod

def canonicalDecoratedProgramPFieldDomain :
    CanonicalDecoratedProgramPFieldDomain period hPeriod where
  decorations := canonicalEffectiveDecoratedMappingTorus period hPeriod
  fieldDomain := canonicalProgramPCommonGeometricDomain4D period hPeriod
  independentVariationEmbedding :=
    independentCompleteVariationLinearMap period hPeriod

@[simp] theorem canonicalDecoratedProgramPFieldDomain_configuration :
    (canonicalDecoratedProgramPFieldDomain period hPeriod).fieldDomain.configuration =
      canonicalPositiveOperatorFields period hPeriod :=
  rfl

/-- The positive canonical field configuration is fixed by simultaneous
PT/exchange in every matter, gauge, ghost, auxiliary and LL slot. -/
theorem canonicalPositiveOperatorFields_ptMatched :
    PTMatchedIndependent period hPeriod
      (canonicalPositiveOperatorFields period hPeriod) := by
  refine ⟨flatPositiveMetricPair_pt_fixed period hPeriod,
    matchedPair_ptMatched period hPeriod MatterFiber _,
    matchedPair_ptMatched period hPeriod GaugeFiber _,
    matchedPair_ptMatched period hPeriod GhostFiber _,
    matchedPair_ptMatched period hPeriod AuxiliaryFiber _, ?_, ?_, ?_⟩
  all_goals
    apply SmoothThroatField.ext period hPeriod _
    intro point
    rfl

theorem canonicalDecoratedProgramPFieldDomain_ptMatched :
    PTMatchedIndependent period hPeriod
      (canonicalDecoratedProgramPFieldDomain period hPeriod).fieldDomain.configuration :=
  canonicalPositiveOperatorFields_ptMatched period hPeriod

/-- The root stored in the same field domain obeys its exact metric square. -/
theorem canonicalDecoratedProgramPFieldDomain_root_square (point) :
    let package := canonicalDecoratedProgramPFieldDomain period hPeriod
    ProgramPCommonGeometricDomain4D.principalRoot period hPeriod
          package.fieldDomain point *
        ProgramPCommonGeometricDomain4D.principalRoot period hPeriod
          package.fieldDomain point =
      lorentzMetricInverse
          (package.fieldDomain.configuration.metrics.plusMagnitude point) *
        package.fieldDomain.induced.minusMetric point :=
  ProgramPCommonGeometricDomain4D.principalRoot_square period hPeriod
    (canonicalProgramPCommonGeometricDomain4D period hPeriod) point

/-- The stored boundary data are the actual trace of the stored fields. -/
theorem canonicalDecoratedProgramPFieldDomain_satisfies_boundary :
    let package := canonicalDecoratedProgramPFieldDomain period hPeriod
    SatisfiesIndependentBoundary period hPeriod package.fieldDomain.boundary
      package.fieldDomain.configuration :=
  ProgramPCommonGeometricDomain4D.satisfies_boundary period hPeriod
    (canonicalProgramPCommonGeometricDomain4D period hPeriod)

theorem canonicalDecoratedProgramPFieldDomain_embedding_injective :
    Function.Injective
      (canonicalDecoratedProgramPFieldDomain period hPeriod).independentVariationEmbedding :=
  independentCompleteVariation_injective period hPeriod

end
end P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D
end JanusFormal
