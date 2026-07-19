import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedReducedFredholmPairing4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff InnerProduct
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The smooth Robin+LL inclusion has identically zero matter block. -/
theorem fullRobinLLDirection_matterHessian_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) :
    globalMatterMultipletHessian period hPeriod matterData
        (matterVariationComponentFamily period hPeriod
          (fullRobinLLDirection period hPeriod robinFirst llFirst).common.matter)
        (matterVariationComponentFamily period hPeriod
          (fullRobinLLDirection period hPeriod robinSecond llSecond).common.matter) = 0 := by
  change globalMatterMultipletHessian period hPeriod matterData 0 0 = 0
  unfold globalMatterMultipletHessian
  apply Finset.sum_eq_zero
  intro index _
  change weakGlobalHolonomicScalarJacobiOperator period hPeriod
    (matterData index) 0 0 = 0
  simp

/-- On the smooth Robin+LL inclusion, the genuine assembled mixed coefficient
is exactly `reducedBosonicNaturalHessian`, the pairing of the true reduced
Fredholm Jacobi operator. The scalar/matter entry is explicitly the zero
embedding. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_reducedJacobi_pairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest)
        (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest) =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
    globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block]

/-- The same identification stated directly on the active quotient classes. -/
theorem quotientHessian_fullRobinLL_eq_reducedJacobi_pairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod robinFirst llFirst.toTest⟧
        ⟦fullRobinLLDirection period hPeriod robinSecond llSecond.toTest⟧ =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
  rw [quotientHessian_mk,
    globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block]

/-- A smooth Robin+LL vector in the kernel of the true reduced Jacobi
operator has zero assembled mixed coefficient against every other smooth
Robin+LL vector. No converse is asserted. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_zero_of_reducedJacobi_kernel
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (robinKernel robinTest : SmoothThroatField period hPeriod Real)
    (llKernel llTest : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus
      kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinKernel,
          llH1SmoothEmbedding period hPeriod llData llKernel) = 0) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (fullRobinLLDirection period hPeriod robinKernel llKernel.toTest)
        (fullRobinLLDirection period hPeriod robinTest llTest.toTest) = 0 := by
  have hScalar := congrArg (fun field => field.1) hKernel
  have hRobin := congrArg (fun field => field.2.1) hKernel
  have hLL := congrArg (fun field => field.2.2) hKernel
  simp only [reducedBosonicJacobiOperator_apply, Prod.fst_zero, Prod.snd_zero] at hScalar hRobin hLL
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_reducedJacobi_pairing]
  unfold reducedBosonicNaturalHessian
  rw [hScalar, hRobin, hLL]
  simp

/-- The same kernel implication after descent to the active quotient Hessian. -/
theorem quotientHessian_fullRobinLL_eq_zero_of_reducedJacobi_kernel
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (robinKernel robinTest : SmoothThroatField period hPeriod Real)
    (llKernel llTest : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus
      kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinKernel,
          llH1SmoothEmbedding period hPeriod llData llKernel) = 0) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod robinKernel llKernel.toTest⟧
        ⟦fullRobinLLDirection period hPeriod robinTest llTest.toTest⟧ = 0 := by
  rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_quotientHessian]
  exact fullMatterRobinTrueLLMixedTaylorCoefficient_eq_zero_of_reducedJacobi_kernel
    period hPeriod matterData scalarData kPlus kMinus robinMeasure llData
    robinKernel robinTest llKernel llTest hKernel

end
end P0EFTJanusFullMatterRobinTrueLLMixedReducedFredholmPairing4D
end JanusFormal
