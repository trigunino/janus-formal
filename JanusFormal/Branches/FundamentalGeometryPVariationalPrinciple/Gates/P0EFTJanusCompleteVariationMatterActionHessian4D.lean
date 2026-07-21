import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterActionVariation4D

namespace JanusFormal
namespace P0EFTJanusCompleteVariationMatterActionHessian4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D

variable (period : ℝ) (hPeriod : period ≠ 0)

/-- The existing matter action curve pulled back from a complete D9/D10
variation through its common independent-field component. -/
def completeVariationMatterActionCurve
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod) (epsilon : ℝ) : ℝ :=
  globalIndependentMatterAction period hPeriod data
    (independentFieldCurve period hPeriod fields variation.independent epsilon)

/-- The existing matter Hessian pulled back through the same independent
component of both complete variations. -/
def completeVariationMatterHessian
    (data : MatterMultipletActionData period hPeriod)
    (first second : ProgramPCompleteVariation4D period hPeriod) : ℝ :=
  globalMatterMultipletHessian period hPeriod data
    (matterVariationComponentFamily period hPeriod first.independent.matter)
    (matterVariationComponentFamily period hPeriod second.independent.matter)

@[simp] theorem completeVariationMatterActionCurve_on_independent
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod) (epsilon : ℝ) :
    completeVariationMatterActionCurve period hPeriod data fields
        (independentCompleteVariation period hPeriod variation) epsilon =
      globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields variation epsilon) := rfl

@[simp] theorem completeVariationMatterHessian_on_independent
    (data : MatterMultipletActionData period hPeriod)
    (first second : IndependentFieldVariation period hPeriod) :
    completeVariationMatterHessian period hPeriod data
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) =
      globalMatterMultipletHessian period hPeriod data
        (matterVariationComponentFamily period hPeriod first.matter)
        (matterVariationComponentFamily period hPeriod second.matter) := rfl

/-- The genuine matter-only derivative theorem transports unchanged to the
canonical complete variation. -/
theorem completeVariationMatterAction_matterOnly_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    HasDerivAt
      (completeVariationMatterActionCurve period hPeriod data fields
        (independentCompleteVariation period hPeriod
          (matterOnlyIndependentVariation period hPeriod direction)))
      (globalMatterMultipletEuler period hPeriod data
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction)) 0 := by
  exact globalIndependentMatterAction_matterOnlyCurve_hasDerivAt
    period hPeriod data fields direction

end
end P0EFTJanusCompleteVariationMatterActionHessian4D
end JanusFormal
