import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetBackgroundNormalSection
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetCarrierTraceProduct

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetCarrierTraceAssembly

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
open P0EFTJanusPhysicalSecondJetBackgroundNormalCore
open P0EFTJanusPhysicalSecondJetBackgroundNormalSection
open P0EFTJanusPhysicalSecondJetCarrierTraceProduct

universe uField uBulkBase uThroatBase
universe uBulkModel uBulkModelSpace uThroatModel uThroatModelSpace
universe uGaugeBulkFiber uGaugeThroatFiber uLLBulkFiber uLLThroatFiber
universe uMetricBulkFiber uMetricThroatFiber uSpinCBulkFiber uSpinCThroatFiber
universe uBackgroundBulkFiber uBackgroundThroatFiber uNormalBulkFiber uNormalThroatFiber
universe uGaugeBulkChart uGaugeThroatChart uLLBulkChart uLLThroatChart
universe uMetricBulkChart uMetricThroatChart uSpinCBulkChart uSpinCThroatChart
universe uBackgroundBulkChart uBackgroundThroatChart uNormalBulkChart uNormalThroatChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]

variable {BulkModel : Type uBulkModel} [NormedAddCommGroup BulkModel]
variable [NormedSpace 𝕜 BulkModel]
variable {BulkModelSpace : Type uBulkModelSpace} [TopologicalSpace BulkModelSpace]
variable (IBulk : ModelWithCorners 𝕜 BulkModel BulkModelSpace)
variable {BulkBase : Type uBulkBase} [TopologicalSpace BulkBase]
variable [ChartedSpace BulkModelSpace BulkBase]

variable {ThroatModel : Type uThroatModel} [NormedAddCommGroup ThroatModel]
variable [NormedSpace 𝕜 ThroatModel]
variable {ThroatModelSpace : Type uThroatModelSpace} [TopologicalSpace ThroatModelSpace]
variable (IThroat : ModelWithCorners 𝕜 ThroatModel ThroatModelSpace)
variable {ThroatBase : Type uThroatBase} [TopologicalSpace ThroatBase]
variable [ChartedSpace ThroatModelSpace ThroatBase]

variable {GaugeBulkFiber : Type uGaugeBulkFiber}
variable {GaugeThroatFiber : Type uGaugeThroatFiber}
variable {LLBulkFiber : Type uLLBulkFiber}
variable {LLThroatFiber : Type uLLThroatFiber}
variable {MetricBulkFiber : Type uMetricBulkFiber}
variable {MetricThroatFiber : Type uMetricThroatFiber}
variable {SpinCBulkFiber : Type uSpinCBulkFiber}
variable {SpinCThroatFiber : Type uSpinCThroatFiber}
variable {BackgroundBulkFiber : Type uBackgroundBulkFiber}
variable {BackgroundThroatFiber : Type uBackgroundThroatFiber}
variable {NormalBulkFiber : Type uNormalBulkFiber}
variable {NormalThroatFiber : Type uNormalThroatFiber}

variable [NormedAddCommGroup GaugeBulkFiber] [NormedSpace 𝕜 GaugeBulkFiber]
variable [NormedAddCommGroup GaugeThroatFiber] [NormedSpace 𝕜 GaugeThroatFiber]
variable [NormedAddCommGroup LLBulkFiber] [NormedSpace 𝕜 LLBulkFiber]
variable [NormedAddCommGroup LLThroatFiber] [NormedSpace 𝕜 LLThroatFiber]
variable [NormedAddCommGroup MetricBulkFiber] [NormedSpace 𝕜 MetricBulkFiber]
variable [NormedAddCommGroup MetricThroatFiber] [NormedSpace 𝕜 MetricThroatFiber]
variable [NormedAddCommGroup SpinCBulkFiber] [NormedSpace 𝕜 SpinCBulkFiber]
variable [NormedAddCommGroup SpinCThroatFiber] [NormedSpace 𝕜 SpinCThroatFiber]
variable [NormedAddCommGroup BackgroundBulkFiber] [NormedSpace 𝕜 BackgroundBulkFiber]
variable [NormedAddCommGroup BackgroundThroatFiber] [NormedSpace 𝕜 BackgroundThroatFiber]
variable [NormedAddCommGroup NormalBulkFiber] [NormedSpace 𝕜 NormalBulkFiber]
variable [NormedAddCommGroup NormalThroatFiber] [NormedSpace 𝕜 NormalThroatFiber]

variable {GaugeBulkChart : Type uGaugeBulkChart}
variable {GaugeThroatChart : Type uGaugeThroatChart}
variable {LLBulkChart : Type uLLBulkChart}
variable {LLThroatChart : Type uLLThroatChart}
variable {MetricBulkChart : Type uMetricBulkChart}
variable {MetricThroatChart : Type uMetricThroatChart}
variable {SpinCBulkChart : Type uSpinCBulkChart}
variable {SpinCThroatChart : Type uSpinCThroatChart}
variable {BackgroundBulkChart : Type uBackgroundBulkChart}
variable {BackgroundThroatChart : Type uBackgroundThroatChart}
variable {NormalBulkChart : Type uNormalBulkChart}
variable {NormalThroatChart : Type uNormalThroatChart}

/-- Componentwise trace of the gauge, LL, metric, and SpinC carriers on their
named physical common atlases. -/
def physicalSecondJetCarrierTrace
    (restrictBase : ThroatBase → BulkBase)
    (bulkGaugeCore : VectorBundleCore 𝕜 BulkBase GaugeBulkFiber GaugeBulkChart)
    (throatGaugeCore : VectorBundleCore 𝕜 ThroatBase GaugeThroatFiber GaugeThroatChart)
    (bulkLLCore : VectorBundleCore 𝕜 BulkBase LLBulkFiber LLBulkChart)
    (throatLLCore : VectorBundleCore 𝕜 ThroatBase LLThroatFiber LLThroatChart)
    (bulkMetricCore : VectorBundleCore 𝕜 BulkBase MetricBulkFiber MetricBulkChart)
    (throatMetricCore : VectorBundleCore 𝕜 ThroatBase MetricThroatFiber MetricThroatChart)
    (bulkSpinCCore : VectorBundleCore 𝕜 BulkBase SpinCBulkFiber SpinCBulkChart)
    (throatSpinCCore : VectorBundleCore 𝕜 ThroatBase SpinCThroatFiber SpinCThroatChart)
    (bulkGaugeCoordinates : SmoothCoreSectionCoordinates IBulk bulkGaugeCore)
    (throatGaugeCoordinates : SmoothCoreSectionCoordinates IThroat throatGaugeCore)
    (bulkLLCoordinates : SmoothCoreSectionCoordinates IBulk bulkLLCore)
    (throatLLCoordinates : SmoothCoreSectionCoordinates IThroat throatLLCore)
    (bulkMetricCoordinates : SmoothCoreSectionCoordinates IBulk bulkMetricCore)
    (throatMetricCoordinates : SmoothCoreSectionCoordinates IThroat throatMetricCore)
    (bulkSpinCCoordinates : SmoothCoreSectionCoordinates IBulk bulkSpinCCore)
    (throatSpinCCoordinates : SmoothCoreSectionCoordinates IThroat throatSpinCCore)
    (gaugeTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkGaugeCore throatGaugeCore bulkGaugeCoordinates throatGaugeCoordinates)
    (llTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkLLCore throatLLCore bulkLLCoordinates throatLLCoordinates)
    (metricTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkMetricCore throatMetricCore bulkMetricCoordinates throatMetricCoordinates)
    (spinCTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkSpinCCore throatSpinCCore bulkSpinCCoordinates throatSpinCCoordinates) :
    SmoothCoreCarrierTrace IBulk IThroat restrictBase
      (physicalSecondJetVectorBundleCore bulkGaugeCore bulkLLCore bulkMetricCore
        bulkSpinCCore)
      (physicalSecondJetVectorBundleCore throatGaugeCore throatLLCore
        throatMetricCore throatSpinCCore)
      (physicalSecondJetSmoothCoordinates IBulk bulkGaugeCore bulkLLCore
        bulkMetricCore bulkSpinCCore bulkGaugeCoordinates bulkLLCoordinates
        bulkMetricCoordinates bulkSpinCCoordinates)
      (physicalSecondJetSmoothCoordinates IThroat throatGaugeCore throatLLCore
        throatMetricCore throatSpinCCore throatGaugeCoordinates throatLLCoordinates
        throatMetricCoordinates throatSpinCCoordinates) where
  chartMap chart :=
    { gauge := gaugeTrace.chartMap chart.gauge
      ll := llTrace.chartMap chart.ll
      metric := metricTrace.chartMap chart.metric
      spinC := spinCTrace.chartMap chart.spinC }
  trace base :=
    (((gaugeTrace.trace base).prodMap (llTrace.trace base)).prodMap
      (metricTrace.trace base)).prodMap (spinCTrace.trace base)
  localTrace chart base :=
    (((gaugeTrace.localTrace chart.gauge base).prodMap
        (llTrace.localTrace chart.ll base)).prodMap
      (metricTrace.localTrace chart.metric base)).prodMap
        (spinCTrace.localTrace chart.spinC base)
  baseSet_compatible := by
    intro chart base hBase
    exact ⟨⟨⟨gaugeTrace.baseSet_compatible chart.gauge base hBase.1.1.1,
      llTrace.baseSet_compatible chart.ll base hBase.1.1.2⟩,
      metricTrace.baseSet_compatible chart.metric base hBase.1.2⟩,
      spinCTrace.baseSet_compatible chart.spinC base hBase.2⟩
  value_compatible := by
    intro base
    change
      (((throatGaugeCoordinates.value base, throatLLCoordinates.value base),
          throatMetricCoordinates.value base), throatSpinCCoordinates.value base) =
      (((gaugeTrace.trace base
            (bulkGaugeCoordinates.value (restrictBase base)),
          llTrace.trace base
            (bulkLLCoordinates.value (restrictBase base))),
        metricTrace.trace base
          (bulkMetricCoordinates.value (restrictBase base))),
        spinCTrace.trace base
          (bulkSpinCCoordinates.value (restrictBase base)))
    rw [gaugeTrace.value_compatible base, llTrace.value_compatible base,
      metricTrace.value_compatible base, spinCTrace.value_compatible base]
  extractor_compatible := by
    intro chart base hBase
    change
      (((throatGaugeCoordinates.extractor chart.gauge base,
          throatLLCoordinates.extractor chart.ll base),
        throatMetricCoordinates.extractor chart.metric base),
        throatSpinCCoordinates.extractor chart.spinC base) =
      (((gaugeTrace.localTrace chart.gauge base
            (bulkGaugeCoordinates.extractor (gaugeTrace.chartMap chart.gauge)
              (restrictBase base)),
          llTrace.localTrace chart.ll base
            (bulkLLCoordinates.extractor (llTrace.chartMap chart.ll)
              (restrictBase base))),
        metricTrace.localTrace chart.metric base
          (bulkMetricCoordinates.extractor (metricTrace.chartMap chart.metric)
            (restrictBase base))),
        spinCTrace.localTrace chart.spinC base
          (bulkSpinCCoordinates.extractor (spinCTrace.chartMap chart.spinC)
            (restrictBase base)))
    rw [gaugeTrace.extractor_compatible chart.gauge base hBase.1.1.1,
      llTrace.extractor_compatible chart.ll base hBase.1.1.2,
      metricTrace.extractor_compatible chart.metric base hBase.1.2,
      spinCTrace.extractor_compatible chart.spinC base hBase.2]

/-- Adjoin background and normal carrier traces to an already assembled
four-sector physical trace. -/
def physicalSecondJetBackgroundNormalCarrierTrace
    (restrictBase : ThroatBase → BulkBase)
    (bulkGaugeCore : VectorBundleCore 𝕜 BulkBase GaugeBulkFiber GaugeBulkChart)
    (throatGaugeCore : VectorBundleCore 𝕜 ThroatBase GaugeThroatFiber GaugeThroatChart)
    (bulkLLCore : VectorBundleCore 𝕜 BulkBase LLBulkFiber LLBulkChart)
    (throatLLCore : VectorBundleCore 𝕜 ThroatBase LLThroatFiber LLThroatChart)
    (bulkMetricCore : VectorBundleCore 𝕜 BulkBase MetricBulkFiber MetricBulkChart)
    (throatMetricCore : VectorBundleCore 𝕜 ThroatBase MetricThroatFiber MetricThroatChart)
    (bulkSpinCCore : VectorBundleCore 𝕜 BulkBase SpinCBulkFiber SpinCBulkChart)
    (throatSpinCCore : VectorBundleCore 𝕜 ThroatBase SpinCThroatFiber SpinCThroatChart)
    (bulkBackgroundCore : VectorBundleCore 𝕜 BulkBase BackgroundBulkFiber BackgroundBulkChart)
    (throatBackgroundCore : VectorBundleCore 𝕜 ThroatBase BackgroundThroatFiber BackgroundThroatChart)
    (bulkNormalCore : VectorBundleCore 𝕜 BulkBase NormalBulkFiber NormalBulkChart)
    (throatNormalCore : VectorBundleCore 𝕜 ThroatBase NormalThroatFiber NormalThroatChart)
    (bulkPhysicalCoordinates : SmoothCoreSectionCoordinates IBulk
      (physicalSecondJetVectorBundleCore bulkGaugeCore bulkLLCore bulkMetricCore
        bulkSpinCCore))
    (throatPhysicalCoordinates : SmoothCoreSectionCoordinates IThroat
      (physicalSecondJetVectorBundleCore throatGaugeCore throatLLCore
        throatMetricCore throatSpinCCore))
    (bulkBackgroundCoordinates : SmoothCoreSectionCoordinates IBulk bulkBackgroundCore)
    (throatBackgroundCoordinates : SmoothCoreSectionCoordinates IThroat throatBackgroundCore)
    (bulkNormalCoordinates : SmoothCoreSectionCoordinates IBulk bulkNormalCore)
    (throatNormalCoordinates : SmoothCoreSectionCoordinates IThroat throatNormalCore)
    (physicalTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      (physicalSecondJetVectorBundleCore bulkGaugeCore bulkLLCore bulkMetricCore
        bulkSpinCCore)
      (physicalSecondJetVectorBundleCore throatGaugeCore throatLLCore
        throatMetricCore throatSpinCCore)
      bulkPhysicalCoordinates throatPhysicalCoordinates)
    (backgroundTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkBackgroundCore throatBackgroundCore bulkBackgroundCoordinates
      throatBackgroundCoordinates)
    (normalTrace : SmoothCoreCarrierTrace IBulk IThroat restrictBase
      bulkNormalCore throatNormalCore bulkNormalCoordinates throatNormalCoordinates) :
    SmoothCoreCarrierTrace IBulk IThroat restrictBase
      (physicalSecondJetBackgroundNormalCore bulkGaugeCore bulkLLCore bulkMetricCore
        bulkSpinCCore bulkBackgroundCore bulkNormalCore)
      (physicalSecondJetBackgroundNormalCore throatGaugeCore throatLLCore
        throatMetricCore throatSpinCCore throatBackgroundCore throatNormalCore)
      (physicalSecondJetBackgroundNormalSmoothCoordinates IBulk
        bulkGaugeCore bulkLLCore bulkMetricCore bulkSpinCCore bulkBackgroundCore
        bulkNormalCore bulkPhysicalCoordinates bulkBackgroundCoordinates
        bulkNormalCoordinates)
      (physicalSecondJetBackgroundNormalSmoothCoordinates IThroat
        throatGaugeCore throatLLCore throatMetricCore throatSpinCCore
        throatBackgroundCore throatNormalCore throatPhysicalCoordinates
        throatBackgroundCoordinates throatNormalCoordinates) where
  chartMap chart :=
    { physical := physicalTrace.chartMap chart.physical
      background := backgroundTrace.chartMap chart.background
      normal := normalTrace.chartMap chart.normal }
  trace base :=
    ((physicalTrace.trace base).prodMap (backgroundTrace.trace base)).prodMap
      (normalTrace.trace base)
  localTrace chart base :=
    ((physicalTrace.localTrace chart.physical base).prodMap
      (backgroundTrace.localTrace chart.background base)).prodMap
        (normalTrace.localTrace chart.normal base)
  baseSet_compatible := by
    intro chart base hBase
    exact ⟨⟨physicalTrace.baseSet_compatible chart.physical base hBase.1.1,
      backgroundTrace.baseSet_compatible chart.background base hBase.1.2⟩,
      normalTrace.baseSet_compatible chart.normal base hBase.2⟩
  value_compatible := by
    intro base
    change
      ((throatPhysicalCoordinates.value base,
          throatBackgroundCoordinates.value base),
        throatNormalCoordinates.value base) =
      ((physicalTrace.trace base
          (bulkPhysicalCoordinates.value (restrictBase base)),
        backgroundTrace.trace base
          (bulkBackgroundCoordinates.value (restrictBase base))),
        normalTrace.trace base
          (bulkNormalCoordinates.value (restrictBase base)))
    rw [physicalTrace.value_compatible base,
      backgroundTrace.value_compatible base, normalTrace.value_compatible base]
  extractor_compatible := by
    intro chart base hBase
    change
      ((throatPhysicalCoordinates.extractor chart.physical base,
          throatBackgroundCoordinates.extractor chart.background base),
        throatNormalCoordinates.extractor chart.normal base) =
      ((physicalTrace.localTrace chart.physical base
          (bulkPhysicalCoordinates.extractor
            (physicalTrace.chartMap chart.physical) (restrictBase base)),
        backgroundTrace.localTrace chart.background base
          (bulkBackgroundCoordinates.extractor
            (backgroundTrace.chartMap chart.background) (restrictBase base))),
        normalTrace.localTrace chart.normal base
          (bulkNormalCoordinates.extractor
            (normalTrace.chartMap chart.normal) (restrictBase base)))
    rw [physicalTrace.extractor_compatible chart.physical base hBase.1.1,
      backgroundTrace.extractor_compatible chart.background base hBase.1.2,
      normalTrace.extractor_compatible chart.normal base hBase.2]

end

end P0EFTJanusPhysicalSecondJetCarrierTraceAssembly
end JanusFormal
