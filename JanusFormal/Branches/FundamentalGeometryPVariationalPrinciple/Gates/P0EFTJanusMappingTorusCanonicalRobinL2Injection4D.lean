import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D

/-! Injection of smooth Robin fields into L2 for the actual canonical throat volume. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalRobinL2Injection4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : Measure.IsOpenPosMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

theorem smoothThroatFieldToCanonicalL2_injective :
    Function.Injective (smoothThroatFieldToL2 period hPeriod
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  exact smoothThroatFieldToL2_injective_of_fullSupport period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

end
end P0EFTJanusMappingTorusCanonicalRobinL2Injection4D
end JanusFormal
