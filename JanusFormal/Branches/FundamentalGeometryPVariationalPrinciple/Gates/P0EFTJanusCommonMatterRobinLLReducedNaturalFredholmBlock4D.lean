import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

/-!
# Robin--LL block shared with the reduced natural Fredholm Hessian

The matter action and the reduced scalar action are different.  The equality
proved here therefore sets both corresponding directions to zero and identifies
only the Robin + LL block, with the same fields, measure, frame and directions.
No equality of the full actions or Hessians is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff InnerProduct ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Inclusion of the shared Robin + LL directions into the enriched common
packet, with all matter and other common directions zero. -/
def commonRobinLLDirection
    (robin : SmoothThroatField period hPeriod Real)
    (ll : SmoothThroatField period hPeriod LLFieldFiber) :
    MatterRobinLLEnrichedDirections period hPeriod where
  common :=
    { metric := { plusLogDirection := 0, minusLogDirection := 0 }
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := ll }
  robin := robin

private theorem globalMatterMultipletHessian_zero_zero
    (matterData : MatterMultipletActionData period hPeriod) :
    globalMatterMultipletHessian period hPeriod matterData 0 0 = 0 := by
  unfold globalMatterMultipletHessian
  apply Finset.sum_eq_zero
  intro index _
  change weakGlobalHolonomicScalarJacobiOperator period hPeriod
    (matterData index) 0 0 = 0
  simp

private theorem staticScalarJacobiForm_zero_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod) :
    globalHolonomicScalarJacobiForm period hPeriod scalarData.formData
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField = 0 := by
  rw [← weakGlobalHolonomicScalarJacobiOperator_apply]
  change weakGlobalHolonomicScalarJacobiOperator period hPeriod
    scalarData.formData 0 0 = 0
  simp

/-- Exact equality of the shared smooth Robin + LL block with the corresponding
dense smooth block of the reduced natural Fredholm Hessian. -/
theorem commonMatterRobinLLHessian_eq_reducedNatural_robinLL_block
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (commonRobinLLDirection period hPeriod robinFirst llFirst.toTest)
        (commonRobinLLDirection period hPeriod robinSecond llSecond.toTest) =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
  rw [reducedBosonicNaturalHessian_smooth_eq]
  unfold commonMatterRobinLLHessian matterRobinLLHessian
  change globalMatterMultipletHessian period hPeriod matterData 0 0 +
      robinHessian period hPeriod kPlus kMinus robinFirst robinSecond
        robinMeasure +
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        llFirst.toTest llSecond.toTest llData.mu = _
  rw [globalMatterMultipletHessian_zero_zero,
    staticScalarJacobiForm_zero_zero]

end

end P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
end JanusFormal
