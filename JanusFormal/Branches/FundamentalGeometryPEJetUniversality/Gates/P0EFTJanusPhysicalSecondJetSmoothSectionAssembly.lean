import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold Bundle
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

universe uBase uField uModel uModelSpace uFiber uChart
universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]
variable {Model : Type uModel} [NormedAddCommGroup Model]
variable [NormedSpace 𝕜 Model]
variable {ModelSpace : Type uModelSpace} [TopologicalSpace ModelSpace]
variable (IB : ModelWithCorners 𝕜 Model ModelSpace)
variable {Base : Type uBase} [TopologicalSpace Base]
variable [ChartedSpace ModelSpace Base]

variable {Fiber : Type uFiber}
variable [NormedAddCommGroup Fiber] [NormedSpace 𝕜 Fiber]
variable {Chart : Type uChart}

/-- A global section together with the exact real extractor in every source
chart.  The coordinate equality and chartwise smoothness are the reusable data
already supplied by each sector-specific second-jet construction. -/
structure SmoothCoreSectionCoordinates
    (core : VectorBundleCore 𝕜 Base Fiber Chart) where
  value : Base → Fiber
  extractor : Chart → Base → Fiber
  coordinate_eq :
    ∀ chart base, base ∈ core.baseSet chart →
      core.coordChange (core.indexAt base) chart base (value base) =
        extractor chart base
  extractor_contMDiffOn :
    ∀ chart,
      ContMDiffOn IB 𝓘(𝕜, Fiber) ∞ (extractor chart) (core.baseSet chart)

variable {GaugeFiber : Type uGaugeFiber}
variable {LLFiber : Type uLLFiber}
variable {MetricFiber : Type uMetricFiber}
variable {SpinCFiber : Type uSpinCFiber}
variable [NormedAddCommGroup GaugeFiber] [NormedSpace 𝕜 GaugeFiber]
variable [NormedAddCommGroup LLFiber] [NormedSpace 𝕜 LLFiber]
variable [NormedAddCommGroup MetricFiber] [NormedSpace 𝕜 MetricFiber]
variable [NormedAddCommGroup SpinCFiber] [NormedSpace 𝕜 SpinCFiber]

variable {GaugeChart : Type uGaugeChart}
variable {LLChart : Type uLLChart}
variable {MetricChart : Type uMetricChart}
variable {SpinCChart : Type uSpinCChart}

/-- Pointwise value of the common physical section. -/
def physicalSecondJetSectionValue
    {gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart}
    {llCore : VectorBundleCore 𝕜 Base LLFiber LLChart}
    {metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart}
    {spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart}
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore)
    (base : Base) :
    PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) :=
  (((gaugeSection.value base, llSection.value base), metricSection.value base),
    spinCSection.value base)

/-- Exact common local extractor in a refined physical chart. -/
def physicalSecondJetLocalExtractor
    {gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart}
    {llCore : VectorBundleCore 𝕜 Base LLFiber LLChart}
    {metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart}
    {spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart}
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (base : Base) :
    PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) :=
  (((gaugeSection.extractor chart.gauge base,
      llSection.extractor chart.ll base),
    metricSection.extractor chart.metric base),
    spinCSection.extractor chart.spinC base)

/-- The common local extractor is smooth on the exact fourfold refined domain. -/
theorem physicalSecondJetLocalExtractor_contMDiffOn
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    ContMDiffOn IB
      𝓘(𝕜, PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)) ∞
      (physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection chart)
      ((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet chart) := by
  have hGauge :=
    (gaugeSection.extractor_contMDiffOn chart.gauge).mono (by
      intro base hBase
      exact hBase.1.1.1)
  have hLL :=
    (llSection.extractor_contMDiffOn chart.ll).mono (by
      intro base hBase
      exact hBase.1.1.2)
  have hMetric :=
    (metricSection.extractor_contMDiffOn chart.metric).mono (by
      intro base hBase
      exact hBase.1.2)
  have hSpinC :=
    (spinCSection.extractor_contMDiffOn chart.spinC).mono (by
      intro base hBase
      exact hBase.2)
  exact ((hGauge.prodMk_space hLL).prodMk_space hMetric).prodMk_space hSpinC

/-- The coordinates of the common section are exactly the tuple of the four
real sector extractors, with no quotient representative or truncation. -/
theorem physicalSecondJetSection_coordinate_eq
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (base : Base)
    (hBase : base ∈
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet chart) :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).coordChange
        ((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).indexAt base)
        chart base
        (physicalSecondJetSectionValue IB gaugeSection llSection metricSection spinCSection base) =
      physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection
        chart base := by
  change
    (((gaugeCore.coordChange (gaugeCore.indexAt base) chart.gauge base
          (gaugeSection.value base),
        llCore.coordChange (llCore.indexAt base) chart.ll base
          (llSection.value base)),
      metricCore.coordChange (metricCore.indexAt base) chart.metric base
        (metricSection.value base)),
      spinCCore.coordChange (spinCCore.indexAt base) chart.spinC base
        (spinCSection.value base)) =
    (((gaugeSection.extractor chart.gauge base,
        llSection.extractor chart.ll base),
      metricSection.extractor chart.metric base),
      spinCSection.extractor chart.spinC base)
  rw [gaugeSection.coordinate_eq chart.gauge base hBase.1.1.1,
    llSection.coordinate_eq chart.ll base hBase.1.1.2,
    metricSection.coordinate_eq chart.metric base hBase.1.2,
    spinCSection.coordinate_eq chart.spinC base hBase.2]

/-- The common pointwise value as a section of the physical core bundle. -/
def physicalSecondJetBundleSection
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore) :
    Base → Bundle.TotalSpace
      (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).Fiber :=
  fun base =>
    ⟨base,
      physicalSecondJetSectionValue IB gaugeSection llSection metricSection spinCSection base⟩

@[simp] theorem physicalSecondJetBundleSection_proj
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore) :
    Bundle.TotalSpace.proj ∘
      physicalSecondJetBundleSection IB gaugeCore llCore metricCore spinCCore
        gaugeSection llSection metricSection spinCSection = id :=
  rfl

/-- Exact local-trivialization coordinate formula for the physical section. -/
theorem physicalSecondJetBundleSection_localTriv
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (base : Base)
    (hBase : base ∈
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet chart) :
    (((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).localTriv
        chart)
      (physicalSecondJetBundleSection IB gaugeCore llCore metricCore spinCCore
        gaugeSection llSection metricSection spinCSection base)).2 =
      physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection
        chart base := by
  change
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).coordChange
        ((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).indexAt base)
        chart base
        (physicalSecondJetSectionValue IB gaugeSection llSection metricSection spinCSection base) =
      physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection
        chart base
  exact physicalSecondJetSection_coordinate_eq IB gaugeCore llCore metricCore spinCCore
    gaugeSection llSection metricSection spinCSection chart base hBase

/-- The assembled physical section is globally smooth. -/
theorem physicalSecondJetBundleSection_contMDiff
    [IsManifold IB ∞ Base]
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    [gaugeCore.IsContMDiff IB ∞]
    [llCore.IsContMDiff IB ∞]
    [metricCore.IsContMDiff IB ∞]
    [spinCCore.IsContMDiff IB ∞]
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore) :
    ContMDiff IB
      (IB.prod
        𝓘(𝕜, PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))) ∞
      (physicalSecondJetBundleSection IB gaugeCore llCore metricCore spinCCore
        gaugeSection llSection metricSection spinCSection) := by
  let physicalCore :=
    physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  letI physicalCoreSmooth : physicalCore.IsContMDiff IB ∞ :=
    physicalSecondJetVectorBundleCore_isContMDiff IB
      gaugeCore llCore metricCore spinCCore
  letI physicalTotalSpaceTopology :
      TopologicalSpace
        (Bundle.TotalSpace
          (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))
          physicalCore.Fiber) :=
    physicalCore.toTopologicalSpace
  letI physicalFiberBundle :
      FiberBundle
        (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))
        physicalCore.Fiber :=
    physicalCore.fiberBundle
  letI physicalVectorBundle :
      VectorBundle 𝕜
        (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))
        physicalCore.Fiber :=
    physicalCore.vectorBundle
  intro base
  let chart := physicalCore.indexAt base
  let localTriv := physicalCore.localTriv chart
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨chart, ?_⟩⟩
    rfl
  have hBase : base ∈ physicalCore.baseSet chart :=
    physicalCore.mem_baseSet_at base
  have hSource :
      physicalSecondJetBundleSection IB gaugeCore llCore metricCore spinCCore
          gaugeSection llSection metricSection spinCSection base ∈
        localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth :
        ContMDiffAt IB
          𝓘(𝕜, PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)) ∞
          (physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection
            chart) base :=
      (physicalSecondJetLocalExtractor_contMDiffOn IB gaugeCore llCore metricCore spinCCore
        gaugeSection llSection metricSection spinCSection chart).contMDiffAt
          (physicalCore.isOpen_baseSet chart).mem_nhds hBase
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [(physicalCore.isOpen_baseSet chart).mem_nhds hBase]
      with nearby hNearby
    exact physicalSecondJetBundleSection_localTriv IB
      gaugeCore llCore metricCore spinCCore gaugeSection llSection metricSection spinCSection
      chart nearby hNearby

end

end P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
end JanusFormal
