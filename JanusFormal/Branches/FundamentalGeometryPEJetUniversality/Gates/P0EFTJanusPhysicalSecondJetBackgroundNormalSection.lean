import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetBackgroundNormalCore

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetBackgroundNormalSection

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold Bundle ContDiff
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
open P0EFTJanusPhysicalSecondJetBackgroundNormalCore

universe uBase uField uModel uModelSpace
universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber
universe uBackgroundFiber uNormalFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart
universe uBackgroundChart uNormalChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]
variable {Model : Type uModel} [NormedAddCommGroup Model]
variable [NormedSpace 𝕜 Model]
variable {ModelSpace : Type uModelSpace} [TopologicalSpace ModelSpace]
variable (IB : ModelWithCorners 𝕜 Model ModelSpace)
variable {Base : Type uBase} [TopologicalSpace Base]
variable [ChartedSpace ModelSpace Base]

variable {GaugeFiber : Type uGaugeFiber}
variable {LLFiber : Type uLLFiber}
variable {MetricFiber : Type uMetricFiber}
variable {SpinCFiber : Type uSpinCFiber}
variable {BackgroundFiber : Type uBackgroundFiber}
variable {NormalFiber : Type uNormalFiber}
variable [NormedAddCommGroup GaugeFiber] [NormedSpace 𝕜 GaugeFiber]
variable [NormedAddCommGroup LLFiber] [NormedSpace 𝕜 LLFiber]
variable [NormedAddCommGroup MetricFiber] [NormedSpace 𝕜 MetricFiber]
variable [NormedAddCommGroup SpinCFiber] [NormedSpace 𝕜 SpinCFiber]
variable [NormedAddCommGroup BackgroundFiber] [NormedSpace 𝕜 BackgroundFiber]
variable [NormedAddCommGroup NormalFiber] [NormedSpace 𝕜 NormalFiber]

variable {GaugeChart : Type uGaugeChart}
variable {LLChart : Type uLLChart}
variable {MetricChart : Type uMetricChart}
variable {SpinCChart : Type uSpinCChart}
variable {BackgroundChart : Type uBackgroundChart}
variable {NormalChart : Type uNormalChart}

/-- The already assembled four-sector section in the reusable chart-coordinate
interface. -/
def physicalSecondJetSmoothCoordinates
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (gaugeSection : SmoothCoreSectionCoordinates IB gaugeCore)
    (llSection : SmoothCoreSectionCoordinates IB llCore)
    (metricSection : SmoothCoreSectionCoordinates IB metricCore)
    (spinCSection : SmoothCoreSectionCoordinates IB spinCCore) :
    SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore) where
  value :=
    physicalSecondJetSectionValue IB gaugeSection llSection metricSection spinCSection
  extractor :=
    physicalSecondJetLocalExtractor IB gaugeSection llSection metricSection spinCSection
  coordinate_eq := by
    intro chart base hBase
    exact physicalSecondJetSection_coordinate_eq IB gaugeCore llCore metricCore spinCCore
      gaugeSection llSection metricSection spinCSection chart base hBase
  extractor_contMDiffOn := by
    intro chart
    exact physicalSecondJetLocalExtractor_contMDiffOn IB
      gaugeCore llCore metricCore spinCCore gaugeSection llSection metricSection spinCSection
      chart

/-- Pointwise value after adjoining background and geometric normal slots. -/
def physicalSecondJetBackgroundNormalSectionValue
    {gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart}
    {llCore : VectorBundleCore 𝕜 Base LLFiber LLChart}
    {metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart}
    {spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart}
    {backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart}
    {normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart}
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore)
    (base : Base) :
    PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber) :=
  ((physicalSection.value base, backgroundSection.value base),
    normalSection.value base)

/-- Exact six-sector extractor in one common chart. -/
def physicalSecondJetBackgroundNormalLocalExtractor
    {gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart}
    {llCore : VectorBundleCore 𝕜 Base LLFiber LLChart}
    {metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart}
    {spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart}
    {backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart}
    {normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart}
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore)
    (chart : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart))
    (base : Base) :
    PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber) :=
  ((physicalSection.extractor chart.physical base,
      backgroundSection.extractor chart.background base),
    normalSection.extractor chart.normal base)

/-- The six-sector extractor is smooth on the exact common domain. -/
theorem physicalSecondJetBackgroundNormalLocalExtractor_contMDiffOn
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore)
    (chart : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart)) :
    ContMDiffOn IB
      𝓘(𝕜,
        PhysicalSecondJetBackgroundNormalFiber
          (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
          (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber)) ∞
      (physicalSecondJetBackgroundNormalLocalExtractor IB
        physicalSection backgroundSection normalSection chart)
      ((physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).baseSet chart) := by
  have hPhysical :=
    (physicalSection.extractor_contMDiffOn chart.physical).mono (show
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
          backgroundCore normalCore).baseSet chart ⊆
        (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet
          chart.physical from by
      intro base hBase
      exact hBase.1.1)
  have hBackground :=
    (backgroundSection.extractor_contMDiffOn chart.background).mono (show
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
          backgroundCore normalCore).baseSet chart ⊆
        backgroundCore.baseSet chart.background from by
      intro base hBase
      exact hBase.1.2)
  have hNormal :=
    (normalSection.extractor_contMDiffOn chart.normal).mono (show
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
          backgroundCore normalCore).baseSet chart ⊆
        normalCore.baseSet chart.normal from by
      intro base hBase
      exact hBase.2)
  exact (hPhysical.prodMk_space hBackground).prodMk_space hNormal

/-- The local coordinates are exactly the physical extractor, background
extractor, and geometric-normal extractor. -/
theorem physicalSecondJetBackgroundNormalSection_coordinate_eq
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore)
    (chart : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart))
    (base : Base)
    (hBase : base ∈
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).baseSet chart) :
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).coordChange
      ((physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).indexAt base)
      chart base
      (physicalSecondJetBackgroundNormalSectionValue IB
        physicalSection backgroundSection normalSection base) =
      physicalSecondJetBackgroundNormalLocalExtractor IB
        physicalSection backgroundSection normalSection chart base := by
  change
    (((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).coordChange
        ((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).indexAt base)
        chart.physical base (physicalSection.value base),
      backgroundCore.coordChange (backgroundCore.indexAt base) chart.background base
        (backgroundSection.value base)),
      normalCore.coordChange (normalCore.indexAt base) chart.normal base
        (normalSection.value base)) =
    ((physicalSection.extractor chart.physical base,
      backgroundSection.extractor chart.background base),
      normalSection.extractor chart.normal base)
  rw [physicalSection.coordinate_eq chart.physical base hBase.1.1,
    backgroundSection.coordinate_eq chart.background base hBase.1.2,
    normalSection.coordinate_eq chart.normal base hBase.2]

/-- Reusable coordinate package for the complete section. -/
def physicalSecondJetBackgroundNormalSmoothCoordinates
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore) :
    SmoothCoreSectionCoordinates IB
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore) where
  value := physicalSecondJetBackgroundNormalSectionValue IB
    physicalSection backgroundSection normalSection
  extractor := physicalSecondJetBackgroundNormalLocalExtractor IB
    physicalSection backgroundSection normalSection
  coordinate_eq := by
    intro chart base hBase
    exact physicalSecondJetBackgroundNormalSection_coordinate_eq IB
      gaugeCore llCore metricCore spinCCore backgroundCore normalCore
      physicalSection backgroundSection normalSection chart base hBase
  extractor_contMDiffOn := by
    intro chart
    exact physicalSecondJetBackgroundNormalLocalExtractor_contMDiffOn IB
      gaugeCore llCore metricCore spinCCore backgroundCore normalCore
      physicalSection backgroundSection normalSection chart

/-- The complete pointwise value as a section of the six-sector bundle. -/
def physicalSecondJetBackgroundNormalBundleSection
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore) :
    Base → Bundle.TotalSpace
      (PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).Fiber :=
  fun base =>
    ⟨base,
      physicalSecondJetBackgroundNormalSectionValue IB
        physicalSection backgroundSection normalSection base⟩

@[simp] theorem physicalSecondJetBackgroundNormalBundleSection_proj
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore) :
    Bundle.TotalSpace.proj ∘
      physicalSecondJetBackgroundNormalBundleSection IB
        gaugeCore llCore metricCore spinCCore backgroundCore normalCore
        physicalSection backgroundSection normalSection = id :=
  rfl

/-- The complete six-sector section is globally smooth. -/
theorem physicalSecondJetBackgroundNormalBundleSection_contMDiff
    [IsManifold IB ∞ Base]
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    [gaugeCore.IsContMDiff IB ∞]
    [llCore.IsContMDiff IB ∞]
    [metricCore.IsContMDiff IB ∞]
    [spinCCore.IsContMDiff IB ∞]
    [backgroundCore.IsContMDiff IB ∞]
    [normalCore.IsContMDiff IB ∞]
    (physicalSection : SmoothCoreSectionCoordinates IB
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore))
    (backgroundSection : SmoothCoreSectionCoordinates IB backgroundCore)
    (normalSection : SmoothCoreSectionCoordinates IB normalCore) :
    ContMDiff IB
      (IB.prod
        𝓘(𝕜,
          PhysicalSecondJetBackgroundNormalFiber
            (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
            (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))) ∞
      (physicalSecondJetBackgroundNormalBundleSection IB
        gaugeCore llCore metricCore spinCCore backgroundCore normalCore
        physicalSection backgroundSection normalSection) := by
  let extendedCore :=
    physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore
  letI extendedCoreSmooth : extendedCore.IsContMDiff IB ∞ :=
    physicalSecondJetBackgroundNormalCore_isContMDiff IB
      gaugeCore llCore metricCore spinCCore backgroundCore normalCore
  letI extendedTotalSpaceTopology :
      TopologicalSpace
        (Bundle.TotalSpace
          (PhysicalSecondJetBackgroundNormalFiber
            (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
            (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
          extendedCore.Fiber) :=
    extendedCore.toTopologicalSpace
  letI extendedFiberBundle :
      FiberBundle
        (PhysicalSecondJetBackgroundNormalFiber
          (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
          (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
        extendedCore.Fiber :=
    extendedCore.fiberBundle
  letI extendedVectorBundle :
      VectorBundle 𝕜
        (PhysicalSecondJetBackgroundNormalFiber
          (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
          (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
        extendedCore.Fiber :=
    extendedCore.vectorBundle
  intro base
  let chart := extendedCore.indexAt base
  let localTriv := extendedCore.localTriv chart
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨chart, ?_⟩⟩
    rfl
  have hBase : base ∈ extendedCore.baseSet chart :=
    extendedCore.mem_baseSet_at base
  have hSource :
      physicalSecondJetBackgroundNormalBundleSection IB
          gaugeCore llCore metricCore spinCCore backgroundCore normalCore
          physicalSection backgroundSection normalSection base ∈
        localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth :
        ContMDiffAt IB
          𝓘(𝕜,
            PhysicalSecondJetBackgroundNormalFiber
              (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
              (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
              (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber)) ∞
          (physicalSecondJetBackgroundNormalLocalExtractor IB
            physicalSection backgroundSection normalSection chart) base :=
      (physicalSecondJetBackgroundNormalLocalExtractor_contMDiffOn IB
        gaugeCore llCore metricCore spinCCore backgroundCore normalCore
        physicalSection backgroundSection normalSection chart).contMDiffAt
          (by
            simpa [extendedCore] using
              (extendedCore.isOpen_baseSet chart).mem_nhds hBase)
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [(extendedCore.isOpen_baseSet chart).mem_nhds hBase]
      with nearby hNearby
    change
      (((extendedCore.localTriv chart)
        (physicalSecondJetBackgroundNormalBundleSection IB
          gaugeCore llCore metricCore spinCCore backgroundCore normalCore
          physicalSection backgroundSection normalSection nearby)).2) =
        physicalSecondJetBackgroundNormalLocalExtractor IB
          physicalSection backgroundSection normalSection chart nearby
    change
      extendedCore.coordChange (extendedCore.indexAt nearby) chart nearby
        (physicalSecondJetBackgroundNormalSectionValue IB
          physicalSection backgroundSection normalSection nearby) =
        physicalSecondJetBackgroundNormalLocalExtractor IB
          physicalSection backgroundSection normalSection chart nearby
    exact physicalSecondJetBackgroundNormalSection_coordinate_eq IB
      gaugeCore llCore metricCore spinCCore backgroundCore normalCore
      physicalSection backgroundSection normalSection chart nearby hNearby

end

end P0EFTJanusPhysicalSecondJetBackgroundNormalSection
end JanusFormal
