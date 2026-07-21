import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationLLActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorMatterActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCombinedLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusCompleteVariationMatterLLActionHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationMatterActionHessian4D P0EFTJanusCompleteVariationLLActionHessian4D
open P0EFTJanusCommonMatterActionVariation4D P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonCompleteSectorMatterActionVariation4D P0EFTJanusCombinedLLActionVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

variable (period : ℝ) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def completeVariationMatterLLActionCurve
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : ℝ) : ℝ :=
  completeVariationMatterActionCurve period hPeriod data fields variation parameter +
    completeVariationLLActionCurve period hPeriod frame fields variation mu parameter

def completeVariationMatterLLHessian
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : ℝ :=
  completeVariationMatterHessian period hPeriod data first second +
    completeVariationLLHessian period hPeriod frame fields first second mu

def completeVariationMatterLLFirstVariation
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPCompleteVariation4D period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : ℝ :=
  globalMatterMultipletEuler period hPeriod data
      (independentMatterComponentFamily period hPeriod fields)
      (matterVariationComponentFamily period hPeriod direction.independent.matter) +
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame fields
      direction.independent.llField mu

@[simp] theorem completeVariationMatterLLHessian_on_independent
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLHessian period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu =
      globalMatterMultipletHessian period hPeriod data
          (matterVariationComponentFamily period hPeriod first.matter)
          (matterVariationComponentFamily period hPeriod second.matter) +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
          first.llField second.llField mu := rfl

theorem completeVariationMatterLLAction_combined_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod
          (combinedIndependentVariation period hPeriod direction)) mu)
      (completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (independentCompleteVariation period hPeriod
          (combinedIndependentVariation period hPeriod direction)) mu) 0 := by
  exact (globalIndependentMatterAction_combinedCurve_hasDerivAt period hPeriod
    data fields direction).add
      (globalPTSymmetricDifferentialLLAction_combined_curve_hasDerivAt period
        hPeriod frame fields direction mu)

theorem completeVariationMatterLLFirstVariation_combined_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : CommonSectorDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      ((fun parameter => globalMatterMultipletEuler period hPeriod data
          (independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields
              (combinedIndependentVariation period hPeriod first) parameter))
          (matterVariationComponentFamily period hPeriod second.matter)) +
        (fun parameter =>
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            (independentFieldCurve period hPeriod fields
              (combinedIndependentVariation period hPeriod first) parameter)
            second.ll mu))
      (globalMatterMultipletHessian period hPeriod data
          (matterVariationComponentFamily period hPeriod first.matter)
          (matterVariationComponentFamily period hPeriod second.matter) +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
          first.ll second.ll mu) 0 := by
  have hMatter := globalMatterMultipletEuler_hasDerivAt period hPeriod data
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod first.matter)
    (matterVariationComponentFamily period hPeriod second.matter)
  have hMatter' : HasDerivAt
      (fun parameter => globalMatterMultipletEuler period hPeriod data
        (independentMatterComponentFamily period hPeriod
          (independentFieldCurve period hPeriod fields
            (combinedIndependentVariation period hPeriod first) parameter))
        (matterVariationComponentFamily period hPeriod second.matter))
      (globalMatterMultipletHessian period hPeriod data
        (matterVariationComponentFamily period hPeriod first.matter)
        (matterVariationComponentFamily period hPeriod second.matter)) 0 := by
    convert hMatter using 1
    funext parameter
    rw [independentMatterComponentFamily_combinedIndependentVariation]
  exact hMatter'.add
    (globalPTSymmetricDifferentialLLFirstVariation_combined_curve_hasDerivAt
      period hPeriod frame fields first second mu)

end
end P0EFTJanusCompleteVariationMatterLLActionHessian4D
end JanusFormal
