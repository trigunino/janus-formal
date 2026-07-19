import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveTaylorDensity4D

/-! PT averages and integrated factorial normalizations of the raw full LL cubic and quartic terms. -/

namespace JanusFormal
namespace P0EFTJanusPTRawFullLLTaylorOrder34Support4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLFullCurveTaylorDensity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def ptRawFullLLCubicDensity (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (rawFullLLCubicDensity period hPeriod frame fields dAux variation p +
    rawFullLLCubicDensity period hPeriod frame fields dAux variation (fixedThroatPT period hPeriod p))

def ptRawFullLLQuarticDensity (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (rawFullLLQuarticDensity period hPeriod frame dAux dField p +
    rawFullLLQuarticDensity period hPeriod frame dAux dField (fixedThroatPT period hPeriod p))

theorem rawFullLLCubicDensity_continuous (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) :
    Continuous (rawFullLLCubicDensity period hPeriod frame fields dAux variation) := by
  unfold rawFullLLCubicDensity
  exact (((fields.llAuxMetric.contMDiff_toFun.continuous.inner dAux.contMDiff_toFun.continuous).mul
      (throatDerivativeEnergy_continuous period hPeriod frame variation.fieldDirection)).add
    ((dAux.contMDiff_toFun.continuous.norm.pow 2).mul
      (throatDerivativePairing_continuous period hPeriod frame fields.llField variation.fieldDirection))).add
        (llThirdVariationCoefficient_continuous period hPeriod variation)

theorem rawFullLLQuarticDensity_continuous (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (rawFullLLQuarticDensity period hPeriod frame dAux dField) := by
  unfold rawFullLLQuarticDensity
  exact (continuous_const.mul (dAux.contMDiff_toFun.continuous.norm.pow 2)).mul
    (throatDerivativeEnergy_continuous period hPeriod frame dField)

theorem ptRawFullLLCubicDensity_continuous (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) :
    Continuous (ptRawFullLLCubicDensity period hPeriod frame fields dAux variation) := by
  exact continuous_const.mul ((rawFullLLCubicDensity_continuous period hPeriod frame fields dAux variation).add
    ((rawFullLLCubicDensity_continuous period hPeriod frame fields dAux variation).comp
      (continuous_fixedThroatPT period hPeriod)))

theorem ptRawFullLLQuarticDensity_continuous (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (ptRawFullLLQuarticDensity period hPeriod frame dAux dField) := by
  exact continuous_const.mul ((rawFullLLQuarticDensity_continuous period hPeriod frame dAux dField).add
    ((rawFullLLQuarticDensity_continuous period hPeriod frame dAux dField).comp
      (continuous_fixedThroatPT period hPeriod)))

theorem ptRawFullLLCubicDensity_integrable (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptRawFullLLCubicDensity period hPeriod frame fields dAux variation) mu :=
  (ptRawFullLLCubicDensity_continuous period hPeriod frame fields dAux variation).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ptRawFullLLQuarticDensity_integrable (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptRawFullLLQuarticDensity period hPeriod frame dAux dField) mu :=
  (ptRawFullLLQuarticDensity_continuous period hPeriod frame dAux dField).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def globalPTRawFullLLCubicCoefficient (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptRawFullLLCubicDensity period hPeriod frame fields dAux variation p ∂mu

def globalPTRawFullLLQuarticCoefficient (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptRawFullLLQuarticDensity period hPeriod frame dAux dField p ∂mu

def globalPTRawFullLLThirdVariation (coefficient : Real) : Real := 6 * coefficient
def globalPTRawFullLLFourthVariation (coefficient : Real) : Real := 24 * coefficient

theorem globalPTRawFullLLThirdVariation_factorial (coefficient : Real) :
    globalPTRawFullLLThirdVariation coefficient = Nat.factorial 3 * coefficient := by
  norm_num [globalPTRawFullLLThirdVariation]

theorem globalPTRawFullLLFourthVariation_factorial (coefficient : Real) :
    globalPTRawFullLLFourthVariation coefficient = Nat.factorial 4 * coefficient := by
  norm_num [globalPTRawFullLLFourthVariation]

theorem cubic_monomial_iteratedDeriv (c : Real) : iteratedDeriv 3 (fun t : Real => t^3 * c) 0 = 6*c := by
  rw [show (fun t : Real => t^3*c) = fun t => c*t^3 by funext t; ring]
  rw [iteratedDeriv_const_mul (n := 3) _ (by fun_prop), iteratedDeriv_pow]
  norm_num
  ring

theorem quartic_monomial_iteratedDeriv (c : Real) : iteratedDeriv 4 (fun t : Real => t^4 * c) 0 = 24*c := by
  rw [show (fun t : Real => t^4*c) = fun t => c*t^4 by funext t; ring]
  rw [iteratedDeriv_const_mul (n := 4) _ (by fun_prop), iteratedDeriv_pow]
  norm_num
  ring

end
end P0EFTJanusPTRawFullLLTaylorOrder34Support4D
end JanusFormal
