import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ActiveQuotientBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientReducedFredholmPairing4D

/-! The smooth Robin--LL enriched D9 observation pairs with the genuine reduced Jacobi operator. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMatterRobinFullLLActiveQuotientReducedFredholmPairing4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem enrichedD9_robinLL_Hessian_eq_reducedJacobi_pairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest) sector column point) =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
  rw [← fullHessian_eq_enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus
    robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
    sector column point]
  exact globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block period hPeriod
    matterData scalarData kPlus kMinus robinMeasure llData robinFirst robinSecond llFirst llSecond

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D
end JanusFormal
