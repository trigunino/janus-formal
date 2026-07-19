import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedKernel4D
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
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D
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

theorem reducedJacobi_kernel_annihilates_enrichedD9_robinLL_observations
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robinFirst : SmoothThroatField period hPeriod Real) (llFirst : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus robinMeasure llData
      (staticScalarEnergyEmbedding period hPeriod scalarData 0,
        smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
        llH1SmoothEmbedding period hPeriod llData llFirst) = 0) :
    ∀ (robinSecond : SmoothThroatField period hPeriod Real) (llSecond : LLH1Smooth period hPeriod llData),
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest) sector column point) = 0 := by
  have hScalar := congrArg (fun value => value.1) hKernel
  have hRobin := congrArg (fun value => value.2.1) hKernel
  have hLL := congrArg (fun value => value.2.2) hKernel
  simp only [reducedBosonicJacobiOperator_apply, Prod.fst_zero, Prod.snd_zero] at hScalar hRobin hLL
  intro robinSecond llSecond
  rw [enrichedD9_robinLL_Hessian_eq_reducedJacobi_pairing]
  unfold reducedBosonicNaturalHessian
  rw [hScalar, hRobin, hLL]
  simp

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedKernel4D
end JanusFormal
