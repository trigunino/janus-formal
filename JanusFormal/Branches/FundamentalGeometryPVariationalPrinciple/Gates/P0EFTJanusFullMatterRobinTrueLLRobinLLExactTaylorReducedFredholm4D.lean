import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedReducedFredholmPairing4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLRobinLLExactTaylorReducedFredholm4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLExactTaylor4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
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

private theorem fullRobinLLDirection_matterEuler_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (matter : MatterComponentFamily period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (ll : SmoothThroatField period hPeriod LLFieldFiber) :
    globalMatterMultipletEuler period hPeriod matterData matter
      (matterVariationComponentFamily period hPeriod
        (fullRobinLLDirection period hPeriod robin ll).common.matter) = 0 := by
  change globalMatterMultipletEuler period hPeriod matterData matter 0 = 0
  unfold globalMatterMultipletEuler
  apply Finset.sum_eq_zero
  intro index _
  exact (weakGlobalHolonomicScalarEulerOperator period hPeriod
    (matterData index) (matter index)).map_zero

/-- Reduced-scope exact Taylor formula along a smooth Robin+LL direction.
The matter direction is zero, the Robin and LL linear terms remain explicit,
and the diagonal quadratic coefficient is the true reduced Fredholm Jacobi
pairing. -/
theorem fullMatterRobinTrueLLCurve_robinLL_exact_taylor_reducedFredholm
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
          llData.mu llData.fields junction +
        t * (robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
            junction robin robinMeasure +
          globalPTFullLLFirstVariation period hPeriod
            (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
            (fullRobinLLDirection period hPeriod robin ll.toTest) llData.mu) +
        (t ^ 2 / 2) * reducedBosonicNaturalHessian period hPeriod scalarData
          kPlus kMinus robinMeasure llData
          (staticScalarEnergyEmbedding period hPeriod scalarData 0,
            smoothThroatFieldToL2 period hPeriod robinMeasure robin,
            llH1SmoothEmbedding period hPeriod llData ll)
          (staticScalarEnergyEmbedding period hPeriod scalarData 0,
            smoothThroatFieldToL2 period hPeriod robinMeasure robin,
            llH1SmoothEmbedding period hPeriod llData ll) +
        t ^ 3 * globalPTFullLLTaylorCubic period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
          (fullDirectionLLVariation period hPeriod
            (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu +
        t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
          (fullDirectionLLVariation period hPeriod
            (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu := by
  unfold fullMatterRobinTrueLLCurve
  rw [fullMatterRobinTrueLLAction_exact_taylor period hPeriod matterData kPlus
      kMinus bulkPlus bulkMinus robinMeasure
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
      (fullRobinLLDirection period hPeriod robin ll.toTest) t,
    globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block period hPeriod
      matterData scalarData kPlus kMinus robinMeasure llData robin robin ll ll]
  unfold fullMatterRobinTrueLLEuler
  rw [fullRobinLLDirection_matterEuler_eq_zero period hPeriod matterData
    (independentMatterComponentFamily period hPeriod llData.fields) robin ll.toTest]
  simp only [zero_add, fullRobinLLDirection]

/-- The actual second iterated derivative at the base point is exactly the
diagonal pairing of the true reduced Fredholm Jacobi operator. -/
theorem fullMatterRobinTrueLLCurve_robinLL_second_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData) :
    iteratedDeriv 2 (fun t : Real =>
      fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robin,
          llH1SmoothEmbedding period hPeriod llData ll)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robin,
          llH1SmoothEmbedding period hPeriod llData ll) := by
  have hCurve : (fun t : Real =>
      fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) = fun t =>
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
          llData.mu llData.fields junction +
        t * (robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
            junction robin robinMeasure +
          globalPTFullLLFirstVariation period hPeriod
            (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
            (fullRobinLLDirection period hPeriod robin ll.toTest) llData.mu) +
        (t ^ 2 / 2) * reducedBosonicNaturalHessian period hPeriod scalarData
          kPlus kMinus robinMeasure llData
          (staticScalarEnergyEmbedding period hPeriod scalarData 0,
            smoothThroatFieldToL2 period hPeriod robinMeasure robin,
            llH1SmoothEmbedding period hPeriod llData ll)
          (staticScalarEnergyEmbedding period hPeriod scalarData 0,
            smoothThroatFieldToL2 period hPeriod robinMeasure robin,
            llH1SmoothEmbedding period hPeriod llData ll) +
        t ^ 3 * globalPTFullLLTaylorCubic period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
          (fullDirectionLLVariation period hPeriod
            (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu +
        t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
          (fullDirectionLLVariation period hPeriod
            (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu := by
    funext t
    exact fullMatterRobinTrueLLCurve_robinLL_exact_taylor_reducedFredholm
      period hPeriod matterData scalarData kPlus kMinus bulkPlus bulkMinus
      robinMeasure llData junction robin ll t
  rw [hCurve]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_id_zero,
    iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

/-- The third derivative of the same reduced-scope true curve is exclusively
the integrated LL cubic coefficient. -/
theorem fullMatterRobinTrueLLCurve_robinLL_third_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData) :
    iteratedDeriv 3 (fun t : Real =>
      fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 =
      6 * globalPTFullLLTaylorCubic period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
        (fullDirectionLLVariation period hPeriod
          (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu := by
  simpa only [fullRobinLLDirection] using
    fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
      junction (fullRobinLLDirection period hPeriod robin ll.toTest)

/-- The fourth derivative of the same reduced-scope true curve is exclusively
the integrated LL quartic coefficient. -/
theorem fullMatterRobinTrueLLCurve_robinLL_fourth_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData) :
    iteratedDeriv 4 (fun t : Real =>
      fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 =
      24 * globalPTFullLLTaylorQuartic period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
        (fullDirectionLLVariation period hPeriod
          (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu := by
  simpa only [fullRobinLLDirection] using
    fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
      junction (fullRobinLLDirection period hPeriod robin ll.toTest)

end
end P0EFTJanusFullMatterRobinTrueLLRobinLLExactTaylorReducedFredholm4D
end JanusFormal
