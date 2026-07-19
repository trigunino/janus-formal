import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentMatterLLActionVisibleQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D

/-!
# Same complete variation for matter--LL action, metric BV and boundary

The general-metric BV doublet occupies the full tensor completion of the same
`ProgramPCompleteVariation4D`; it does not alter the independent component read
by the present matter--LL action.  This gate records the resulting exact action,
first-variation and Hessian equalities, together with the already proved BRST
boundary compatibility.  It adds no EH or Maxwell dynamics.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationMatterLLGeneralMetricBVAgreement4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

theorem matterLLActionCurve_withGeneralMetricBV
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation phase)
        mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod variation) mu parameter :=
  rfl

theorem matterLLActionCurve_withGeneralMetricBV_BRST
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase)) mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation phase)
        mu parameter :=
  rfl

theorem matterLLFirstVariation_withGeneralMetricBV
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation phase) mu =
      completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (independentCompleteVariation period hPeriod variation) mu :=
  rfl

theorem matterLLHessian_withGeneralMetricBV
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod first firstPhase)
        (completeVariationWithGeneralMetricBV period hPeriod second secondPhase) mu =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu :=
  rfl

theorem matterLLHessian_withGeneralMetricBV_BRST
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod first
          (smoothGeneralMetricBVBRST period hPeriod firstPhase))
        (completeVariationWithGeneralMetricBV period hPeriod second
          (smoothGeneralMetricBVBRST period hPeriod secondPhase)) mu =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod first firstPhase)
        (completeVariationWithGeneralMetricBV period hPeriod second secondPhase) mu :=
  rfl

/-- The current boundary domain, the present sectorial action and its Hessian
all consume this one complete variation; only the tensor BV slot is BRST-moved. -/
theorem matterLLGeneralMetricBV_BRST_boundary_agreement
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    (completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase)) mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation phase)
        mu parameter) ∧
    (completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase) ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
        programPBoundaryTangentDomain4D period hPeriod domain) := by
  exact ⟨matterLLActionCurve_withGeneralMetricBV_BRST period hPeriod data frame
    fields variation phase mu parameter,
    completeVariationWithGeneralMetricBV_BRST_mem_boundaryDomain_iff period
      hPeriod domain variation phase⟩

end
end P0EFTJanusCompleteVariationMatterLLGeneralMetricBVAgreement4D
end JanusFormal
