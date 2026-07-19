import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D

/-!
# Reduced LL Fredholm pairing on the complete Program-P tangent

This gate identifies only the smooth LL block.  The reduced scalar and Robin
directions are exactly zero.  No EH, Maxwell, ghost, scalar-matter, or nonzero
Robin identification is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusReducedBosonicLLCompleteVariationHessianBridge4D

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
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationMatterActionHessian4D
open P0EFTJanusCompleteVariationLLActionHessian4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Faithful inclusion of the smooth LL form domain into the actual complete
Program-P tangent.  Every non-LL slot, including the three completion slots,
is exactly zero. -/
def reducedLLSmoothCompleteVariation
    (llData : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod llData) :
    ProgramPCompleteVariation4D period hPeriod :=
  independentCompleteVariation period hPeriod
    (llFluxIndependentVariation period hPeriod direction.toTest)

theorem reducedLLSmoothCompleteVariation_injective
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Injective
      (reducedLLSmoothCompleteVariation period hPeriod llData) := by
  intro first second hEqual
  apply LLH1Smooth.ext
  exact congrArg
    (fun variation : ProgramPCompleteVariation4D period hPeriod =>
      variation.independent.llField) hEqual

private theorem staticScalarJacobiForm_zero_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod) :
    globalHolonomicScalarJacobiForm period hPeriod scalarData.formData
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField = 0 := by
  rw [← weakGlobalHolonomicScalarJacobiOperator_apply]
  change weakGlobalHolonomicScalarJacobiOperator period hPeriod
    scalarData.formData 0 0 = 0
  simp

private theorem completeVariationMatterHessian_reducedLL_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (llData : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod llData) :
    completeVariationMatterHessian period hPeriod matterData
        (reducedLLSmoothCompleteVariation period hPeriod llData first)
        (reducedLLSmoothCompleteVariation period hPeriod llData second) = 0 := by
  unfold completeVariationMatterHessian reducedLLSmoothCompleteVariation
  change globalMatterMultipletHessian period hPeriod matterData 0 0 = 0
  unfold globalMatterMultipletHessian
  apply Finset.sum_eq_zero
  intro index _
  change weakGlobalHolonomicScalarJacobiOperator period hPeriod
    (matterData index) 0 0 = 0
  simp

/-- The direct LL Hessian pulled back to the complete tangent is the smooth LL
block of the reduced Fredholm pairing. -/
theorem completeVariationLLHessian_eq_reducedBosonic_LL_block
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (first second : LLH1Smooth period hPeriod llData) :
    completeVariationLLHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        (reducedLLSmoothCompleteVariation period hPeriod llData first)
        (reducedLLSmoothCompleteVariation period hPeriod llData second) llData.mu =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData first)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData second) := by
  rw [reducedBosonicNaturalHessian_smooth_eq]
  change globalPTSymmetricDifferentialLLFluxHessian period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
      first.toTest second.toTest llData.mu =
    globalHolonomicScalarJacobiForm period hPeriod scalarData.formData
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField
        (0 : StaticGlobalScalarTest period hPeriod scalarData).toField +
      robinHessian period hPeriod kPlus kMinus 0 0 robinMeasure +
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        first.toTest second.toTest llData.mu
  rw [staticScalarJacobiForm_zero_zero]
  have hRobin : robinHessian period hPeriod kPlus kMinus 0 0 robinMeasure = 0 := by
    unfold robinHessian
    apply integral_eq_zero_of_ae
    filter_upwards [] with point
    unfold robinHessianDensity
    change (kPlus + kMinus) * 0 * 0 = 0
    ring
  simpa only [hRobin, zero_add]

/-- On the smooth LL form domain, the LL block of the reduced Fredholm pairing
is exactly the Hessian of the unchanged matter+LL action pulled back to the
same complete tangent.  Both matter directions and both omitted reduced
directions (scalar and Robin) are exactly zero. -/
theorem completeVariationMatterLLHessian_eq_reducedBosonic_LL_block
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (first second : LLH1Smooth period hPeriod llData) :
    completeVariationMatterLLHessian period hPeriod matterData
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        (reducedLLSmoothCompleteVariation period hPeriod llData first)
        (reducedLLSmoothCompleteVariation period hPeriod llData second) llData.mu =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData first)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData second) := by
  unfold completeVariationMatterLLHessian
  rw [completeVariationMatterHessian_reducedLL_eq_zero,
    completeVariationLLHessian_eq_reducedBosonic_LL_block period hPeriod
      scalarData kPlus kMinus robinMeasure llData first second]
  exact zero_add _

/-- The same equality is variation-theoretic: the reduced LL Fredholm pairing
is the derivative of the genuine LL first variation along the injectively
included complete tangent. -/
theorem reducedBosonic_LL_pairing_is_completeAction_secondVariation
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (first second : LLH1Smooth period hPeriod llData) :
    HasDerivAt
      (fun parameter =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod)
          (independentFieldCurve period hPeriod llData.fields
            (reducedLLSmoothCompleteVariation period hPeriod llData first).independent
            parameter)
          second.toTest llData.mu)
      (reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData first)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure 0,
          llH1SmoothEmbedding period hPeriod llData second)) 0 := by
  have h := completeVariationLLFirstVariation_llOnly_hasDerivAt period hPeriod
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
    first.toTest second.toTest llData.mu
  rw [← completeVariationLLHessian_eq_reducedBosonic_LL_block
    period hPeriod scalarData kPlus kMinus robinMeasure llData first second]
  exact h

end
end P0EFTJanusReducedBosonicLLCompleteVariationHessianBridge4D
end JanusFormal
