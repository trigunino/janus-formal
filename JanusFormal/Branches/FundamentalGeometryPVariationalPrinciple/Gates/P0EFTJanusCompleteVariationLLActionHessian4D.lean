import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusCompleteVariationLLActionHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The existing PT-symmetric LL action pulled back along the independent
component of a complete D9/D10 variation. -/
def completeVariationLLActionCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    (parameter : ℝ) : ℝ :=
  globalPTSymmetricDifferentialLLAction period hPeriod frame
    (independentFieldCurve period hPeriod fields variation.independent parameter) mu

/-- The existing LL Hessian pulled back through the same complete content. -/
def completeVariationLLHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod))) : ℝ :=
  globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
    first.independent.llField second.independent.llField mu

@[simp] theorem completeVariationLLActionCurve_on_independent
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    (parameter : ℝ) :
    completeVariationLLActionCurve period hPeriod frame fields
        (independentCompleteVariation period hPeriod variation) mu parameter =
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (independentFieldCurve period hPeriod fields variation parameter) mu := rfl

@[simp] theorem completeVariationLLHessian_on_independent
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod))) :
    completeVariationLLHessian period hPeriod frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
        first.llField second.llField mu := rfl

theorem completeVariationLLAction_llOnly_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (completeVariationLLActionCurve period hPeriod frame fields
        (independentCompleteVariation period hPeriod
          (llFluxIndependentVariation period hPeriod direction)) mu)
      (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        fields direction mu) 0 := by
  exact globalPTSymmetricDifferentialLLAction_independentFieldCurve_hasDerivAt
    period hPeriod frame fields direction mu

/-- The genuine mixed LL Hessian derivative also transports to the complete
variation curve. -/
theorem completeVariationLLFirstVariation_llOnly_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (fun parameter =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (independentFieldCurve period hPeriod fields
            (independentCompleteVariation period hPeriod
              (llFluxIndependentVariation period hPeriod first)).independent
            parameter)
          second mu)
      (completeVariationLLHessian period hPeriod frame fields
        (independentCompleteVariation period hPeriod
          (llFluxIndependentVariation period hPeriod first))
        (independentCompleteVariation period hPeriod
          (llFluxIndependentVariation period hPeriod second)) mu) 0 := by
  exact globalPTSymmetricDifferentialLLFirstVariation_independentFieldCurve_hasDerivAt
    period hPeriod frame fields first second mu

end
end P0EFTJanusCompleteVariationLLActionHessian4D
end JanusFormal
