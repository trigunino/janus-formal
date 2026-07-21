import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

/-! # Gauge-functional type bridge to complete Program-P variations -/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCommonGaugeD9Variation4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev GaugeVariationPair :=
  SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber

/-- Exact gauge direction read by an action from the common independent slot
of a complete D9/D10 variation. -/
def completeVariationGaugeDirection
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    GaugeVariationPair period hPeriod :=
  variation.independent.gauge

/-- Pullback of any genuinely supplied gauge action along the real line in
the gauge component.  No Maxwell action is invented here. -/
def completeVariationGaugeActionCurve
    (action : GaugeVariationPair period hPeriod → Real)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (epsilon : Real) : Real :=
  action (epsilon • completeVariationGaugeDirection period hPeriod variation)

/-- Pullback of a supplied gauge Hessian through the same independent slots. -/
def completeVariationGaugeHessian
    (hessian : GaugeVariationPair period hPeriod →
      GaugeVariationPair period hPeriod → Real)
    (first second : ProgramPCompleteVariation4D period hPeriod) : Real :=
  hessian (completeVariationGaugeDirection period hPeriod first)
    (completeVariationGaugeDirection period hPeriod second)

@[simp]
theorem completeVariationGaugeDirection_on_independent
    (variation : IndependentFieldVariation period hPeriod) :
    completeVariationGaugeDirection period hPeriod
        (independentCompleteVariation period hPeriod variation) =
      variation.gauge := rfl

@[simp]
theorem completeVariationGaugeDirection_on_gaugeOnly
    (direction : GaugeVariationPair period hPeriod) :
    completeVariationGaugeDirection period hPeriod
        (independentCompleteVariation period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod direction)) =
      direction := rfl

@[simp]
theorem completeVariationGaugeActionCurve_on_gaugeOnly
    (action : GaugeVariationPair period hPeriod → Real)
    (direction : GaugeVariationPair period hPeriod) (epsilon : Real) :
    completeVariationGaugeActionCurve period hPeriod action
        (independentCompleteVariation period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod direction)) epsilon =
      action (epsilon • direction) := rfl

@[simp]
theorem completeVariationGaugeHessian_on_gaugeOnly
    (hessian : GaugeVariationPair period hPeriod →
      GaugeVariationPair period hPeriod → Real)
    (first second : GaugeVariationPair period hPeriod) :
    completeVariationGaugeHessian period hPeriod hessian
        (independentCompleteVariation period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod first))
        (independentCompleteVariation period hPeriod
          (gaugeOnlyIndependentVariation period hPeriod second)) =
      hessian first second := rfl

end
end P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
end JanusFormal
