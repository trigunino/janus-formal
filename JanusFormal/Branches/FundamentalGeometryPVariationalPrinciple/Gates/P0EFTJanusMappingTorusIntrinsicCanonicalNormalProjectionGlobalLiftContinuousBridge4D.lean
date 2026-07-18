import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D

/-!
# Dependent continuous bridge for the canonical global normal lift

This gate only packages the already constructed canonical lift.  It introduces
no replacement quotient types or local manifold instances.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuousBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D
open P0EFTJanusMappingTorusIntrinsicDifferentialNormalCausalStratification4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical global orthogonal lift packaged in the generic dependent
continuous-lift interface. -/
def canonicalContinuousOrthogonalDifferentialNormalLift :
    ContinuousOrthogonalDifferentialNormalLift period hPeriod where
  lift := canonicalGlobalOrthogonalNormalLift period hPeriod
  represents := by
    intro point normal
    exact canonicalGlobalOrthogonalNormalLift_represents
      period hPeriod point normal
  orthogonal := by
    intro point normal tangent
    exact canonicalGlobalOrthogonalNormalLift_orthogonal
      period hPeriod point normal tangent
  continuous_metric_square := by
    exact canonicalGlobalOrthogonalNormalLift_continuous_metric_square
      period hPeriod
      (canonicalGlobalNormalMetricSquareLocalRegularity period hPeriod)

/-- Generic causal stratification specialized to the canonical dependent
continuous lift. -/
def canonicalIntrinsicDifferentialNormalCausalStratification :=
  intrinsicDifferentialNormalCausalStratification period hPeriod
    (canonicalContinuousOrthogonalDifferentialNormalLift period hPeriod)

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuousBridge4D
end JanusFormal
