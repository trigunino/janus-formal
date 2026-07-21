import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusRobinJunctionActualHelmholtz4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Helmholtz condition for the actual Robin junction Euler functional at
every junction background and fixed pair of bulk traces. -/
def RobinJunctionActualHelmholtzCondition : Prop :=
  ∀ (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu],
    deriv (fun epsilon : Real =>
      robinJunctionActionDirectionalDerivative period hPeriod kPlus kMinus
        bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction first epsilon) second mu) 0 =
    deriv (fun epsilon : Real =>
      robinJunctionActionDirectionalDerivative period hPeriod kPlus kMinus
        bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction second epsilon) first mu) 0

/-- Both sides are genuine mixed second variations of the same unchanged
Robin junction action and hence agree. -/
theorem robin_junction_actual_helmholtz_condition :
    RobinJunctionActualHelmholtzCondition period hPeriod := by
  intro kPlus kMinus bulkPlus bulkMinus junction first second mu _
  change robinJunctionActionMixedHessian period hPeriod kPlus kMinus bulkPlus
      bulkMinus junction first second mu =
    robinJunctionActionMixedHessian period hPeriod kPlus kMinus bulkPlus
      bulkMinus junction second first mu
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
      kMinus bulkPlus bulkMinus junction first second mu,
    robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
      kMinus bulkPlus bulkMinus junction second first mu]
  exact robinHessian_symmetric period hPeriod kPlus kMinus first second mu

end

end P0EFTJanusRobinJunctionActualHelmholtz4D
end JanusFormal
