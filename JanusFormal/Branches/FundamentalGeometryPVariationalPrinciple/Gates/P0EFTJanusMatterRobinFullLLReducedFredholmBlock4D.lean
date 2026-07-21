import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActualHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
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
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def fullRobinLLDirection (robin : SmoothThroatField period hPeriod Real)
    (ll : SmoothThroatField period hPeriod LLFieldFiber) :
    FullMatterRobinLLDirections period hPeriod where
  common := (commonRobinLLDirection period hPeriod robin ll).common
  robin := robin
  llAuxMetric := 0
  llMeasure := 0

theorem fullLLHessian_zeroAuxMeasure_eq_fluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (r₁ r₂ : SmoothThroatField period hPeriod Real)
    (f₁ f₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLHessianForm period hPeriod frame fields
        (fullRobinLLDirection period hPeriod r₁ f₁)
        (fullRobinLLDirection period hPeriod r₂ f₂) mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields f₁ f₂ mu := by
  let fieldsPT := llPTPullback period hPeriod fields
  let f₁PT := differentialLLFluxDirectionPT period hPeriod f₁
  let f₂PT := differentialLLFluxDirectionPT period hPeriod f₂
  have hk0 := differentialLLKineticMixedHessianDensity_integrable period hPeriod frame
    fields.llAuxMetric fields.llField 0 0 f₁ f₂ mu
  have hk1 := differentialLLKineticMixedHessianDensity_integrable period hPeriod frame
    fieldsPT.llAuxMetric fieldsPT.llField 0 0 f₁PT f₂PT mu
  have hw := ptLLWorldvolumeHessianDensity_integrable period hPeriod fields
    ({ measureDirection := 0, fieldDirection := f₁ } : LLVariation period hPeriod)
    ({ measureDirection := 0, fieldDirection := f₂ } : LLVariation period hPeriod) mu
  have hkpt : Integrable (ptSymmetricDifferentialLLKineticMixedHessianDensity
      period hPeriod frame fields.llAuxMetric fields.llField 0 0 f₁ f₂) mu := by
    unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    exact (hk0.add hk1).const_mul (1 / 2 : Real)
  have hf0 := differentialLLFluxHessianDensity_continuous period hPeriod frame fields f₁ f₂
  have hfi0 : Integrable (differentialLLFluxHessianDensity period hPeriod frame fields f₁ f₂) mu :=
    hf0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf1 := differentialLLFluxHessianDensity_continuous period hPeriod frame fieldsPT f₁PT f₂PT
  have hfi1 : Integrable (differentialLLFluxHessianDensity period hPeriod frame fieldsPT f₁PT f₂PT) mu :=
    hf1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have zeroReal_apply (p : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun (0 : SmoothThroatField period hPeriod Real) p = 0 := rfl
  have zeroMetric_apply (p : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun (0 : SmoothThroatField period hPeriod LLMetricFiber) p = 0 := rfl
  unfold globalPTFullLLHessianForm globalPTDifferentialLLKineticMixedHessian
    globalPTLLWorldvolumeHessian globalPTSymmetricDifferentialLLFluxHessian
    globalDifferentialLLFluxHessian
  simp only [fullRobinLLDirection, commonRobinLLDirection,
    fullDirectionLLVariation]
  rw [← integral_add hkpt hw]
  rw [← integral_add hfi0 hfi1]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp [fieldsPT, f₁PT, f₂PT]
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    differentialLLKineticMixedHessianDensity ptLLWorldvolumeHessianDensity
    llWorldvolumeHessianDensity ptAverage differentialLLFluxHessianDensity
    llAuxiliaryKineticWeight llPTPullback differentialLLFluxDirectionPT
    differentialLLAuxMetricDirectionPT
  simp only [zeroReal_apply, zeroMetric_apply, inner_zero_right, zero_mul,
    mul_zero, add_zero, throatPTPullback_apply]
  ring

theorem globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest)
        (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest) =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
  rw [globalMatterRobinFullLLHessian]
  rw [fullLLHessian_zeroAuxMeasure_eq_fluxHessian]
  exact commonMatterRobinLLHessian_eq_reducedNatural_robinLL_block period hPeriod
    matterData scalarData kPlus kMinus robinMeasure llData robinFirst robinSecond llFirst llSecond

end
end P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
end JanusFormal
