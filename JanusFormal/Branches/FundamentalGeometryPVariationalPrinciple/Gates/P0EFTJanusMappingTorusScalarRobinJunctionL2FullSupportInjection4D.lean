import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Conditional injectivity of the smooth Robin inclusion for a finite measure of full topological support. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem smoothThroatFieldToL2_injective_of_fullSupport
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    [Measure.IsOpenPosMeasure mu] :
    Function.Injective (smoothThroatFieldToL2 period hPeriod mu) := by
  intro first second hEqual
  have hCoe :
      ((smoothThroatFieldToL2 period hPeriod mu first : ThroatScalarL2 period hPeriod mu) :
          EffectiveThroat period hPeriod → Real) =
        ((smoothThroatFieldToL2 period hPeriod mu second : ThroatScalarL2 period hPeriod mu) :
          EffectiveThroat period hPeriod → Real) :=
    congrArg (fun value : ThroatScalarL2 period hPeriod mu =>
      (value : EffectiveThroat period hPeriod → Real)) hEqual
  have hCoeAE :
      ((smoothThroatFieldToL2 period hPeriod mu first : ThroatScalarL2 period hPeriod mu) :
          EffectiveThroat period hPeriod → Real) =ᵐ[mu]
        ((smoothThroatFieldToL2 period hPeriod mu second : ThroatScalarL2 period hPeriod mu) :
          EffectiveThroat period hPeriod → Real) :=
    Filter.Eventually.of_forall fun point => congrFun hCoe point
  have hAE : first.toFun =ᵐ[mu] second.toFun :=
    (smoothThroatFieldToL2_ae period hPeriod mu first).symm.trans
      (hCoeAE.trans (smoothThroatFieldToL2_ae period hPeriod mu second))
  have hFun : first.toFun = second.toFun :=
    Measure.eq_of_ae_eq hAE first.contMDiff_toFun.continuous second.contMDiff_toFun.continuous
  apply SmoothThroatField.ext period hPeriod Real
  exact congrFun hFun

end
end P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D
end JanusFormal
