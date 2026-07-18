import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

/-! Global LL coefficient fields and their worldvolume action on the actual compact throat. -/
namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalLLWorldvolume4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

variable (period : Real) (hPeriod : Not (period = 0))
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance effectiveThroatChartedSpace : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance effectiveThroatIsManifold : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance effectiveThroatCompactSpace : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance effectiveThroatMeasurableSpace : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance effectiveThroatBorelSpace : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The LL vector field slot is the worldvolume flux coefficient field. -/
def llFlux (fields : IndependentFields period hPeriod) : SmoothThroatField period hPeriod LLFieldFiber := fields.llField

/-- Smooth LL density built from the independent composite-measure coefficient and flux. -/
def llWorldvolumeDensity (fields : IndependentFields period hPeriod) (point : EffectiveThroat period hPeriod) : Real := fields.llMeasure point * ‖llFlux period hPeriod fields point‖ ^ 2

theorem llWorldvolumeDensity_continuous (fields : IndependentFields period hPeriod) : Continuous (llWorldvolumeDensity period hPeriod fields) := by
  exact fields.llMeasure.contMDiff_toFun.continuous.mul
    (fields.llField.contMDiff_toFun.continuous.norm.pow 2)

/-- The global LL action is an actual integral on the compact throat. -/
def globalLLAction (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) : Real := ∫ point, llWorldvolumeDensity period hPeriod fields point ∂mu

theorem llWorldvolumeDensity_integrable (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] : Integrable (llWorldvolumeDensity period hPeriod fields) mu := by
  exact (llWorldvolumeDensity_continuous period hPeriod fields).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace (llWorldvolumeDensity period hPeriod fields))

/-- The populated PT-matched zero configuration gives a nonempty throat branch with zero LL action. -/
@[simp] theorem globalLLAction_zeroMatched (mu : Measure (EffectiveThroat period hPeriod)) : globalLLAction period hPeriod (zeroMatchedIndependentFields period hPeriod) mu = 0 := by
  simp [globalLLAction, llWorldvolumeDensity, llFlux, zeroMatchedIndependentFields, constantSmoothThroatField]

end
end P0EFTJanusMappingTorusGlobalLLWorldvolume4D
end JanusFormal
