import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLReducedKernelFullSupportRobin4D
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
open P0EFTJanusMappingTorusScalarRobinJunctionL2FullSupportInjection4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem reducedJacobi_shared_kernel_robin_eq_zero_of_fullSupport
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    [Measure.IsOpenPosMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hZero : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus robinMeasure llData
      (reducedRobinLLInclusion period hPeriod scalarData robinMeasure llData robin ll) = 0) :
    robin = 0 := by
  have hIncluded := reducedBosonicJacobiOperator_shared_inclusion_kernel period hPeriod scalarData
    kPlus kMinus hCoupling robinMeasure llData robin ll hZero
  have hRobin := congrArg (fun value => value.2.1) hIncluded
  have hZeroEmbedding : smoothThroatFieldToL2 period hPeriod robinMeasure
      (0 : SmoothThroatField period hPeriod Real) = 0 := by
    apply Lp.ext
    filter_upwards [smoothThroatFieldToL2_ae period hPeriod robinMeasure
      (0 : SmoothThroatField period hPeriod Real), Lp.coeFn_zero Real 2 robinMeasure]
      with point hPoint hLpZero
    rw [hPoint, hLpZero]
    rfl
  apply smoothThroatFieldToL2_injective_of_fullSupport period hPeriod robinMeasure
  change smoothThroatFieldToL2 period hPeriod robinMeasure robin =
    smoothThroatFieldToL2 period hPeriod robinMeasure (0 : SmoothThroatField period hPeriod Real)
  simpa [reducedRobinLLInclusion] using hRobin.trans hZeroEmbedding.symm

end
end P0EFTJanusCommonMatterRobinLLReducedKernelFullSupportRobin4D
end JanusFormal
