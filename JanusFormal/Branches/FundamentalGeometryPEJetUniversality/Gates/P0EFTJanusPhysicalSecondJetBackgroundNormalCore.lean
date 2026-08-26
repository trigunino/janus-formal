import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetBackgroundNormalCore

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

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

/-- Named common chart after adjoining the geometric background and normal
slots to the gauge--LL--metric--SpinC physical chart. -/
@[ext]
structure PhysicalSecondJetBackgroundNormalChart where
  physical : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart
  background : BackgroundChart
  normal : NormalChart

/-- Exact fiber with six named sectors.  The nesting follows the binary product
construction and is therefore inherited by all coordinate changes. -/
abbrev PhysicalSecondJetBackgroundNormalFiber :=
  (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) × BackgroundFiber) ×
    NormalFiber

/-- Identification of the named chart with the nested product chart. -/
def physicalSecondJetBackgroundNormalChartEquiv :
    PhysicalSecondJetBackgroundNormalChart
        (GaugeChart := GaugeChart) (LLChart := LLChart)
        (MetricChart := MetricChart) (SpinCChart := SpinCChart)
        (BackgroundChart := BackgroundChart) (NormalChart := NormalChart) ≃
      ((PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart ×
          BackgroundChart) × NormalChart) where
  toFun chart := ((chart.physical, chart.background), chart.normal)
  invFun chart :=
    { physical := chart.1.1
      background := chart.1.2
      normal := chart.2 }
  left_inv chart := by
    cases chart
    rfl
  right_inv chart := by
    rcases chart with ⟨⟨physical, background⟩, normal⟩
    rfl

/-- Nested product before reindexing by the named six-sector chart. -/
def physicalSecondJetBackgroundNormalNestedCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart) :
    VectorBundleCore 𝕜 Base
      (PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
      ((PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart ×
          BackgroundChart) × NormalChart) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore)
      backgroundCore)
    normalCore

/-- The physical second-jet core with background and normal slots on one exact
common atlas. -/
def physicalSecondJetBackgroundNormalCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart) :
    VectorBundleCore 𝕜 Base
      (PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
      (PhysicalSecondJetBackgroundNormalChart
        (GaugeChart := GaugeChart) (LLChart := LLChart)
        (MetricChart := MetricChart) (SpinCChart := SpinCChart)
        (BackgroundChart := BackgroundChart) (NormalChart := NormalChart)) :=
  reindexVectorBundleCore
    (physicalSecondJetBackgroundNormalNestedCore gaugeCore llCore metricCore
      spinCCore backgroundCore normalCore)
    physicalSecondJetBackgroundNormalChartEquiv

/-- Its chart domain is exactly the intersection of the physical, background,
and normal chart domains. -/
theorem physicalSecondJetBackgroundNormalCore_baseSet
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (chart : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart)) :
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).baseSet chart =
      ((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet
          chart.physical ∩ backgroundCore.baseSet chart.background) ∩
        normalCore.baseSet chart.normal :=
  rfl

/-- Exact preferred chart assembled from all six source cores. -/
theorem physicalSecondJetBackgroundNormalCore_indexAt
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (base : Base) :
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).indexAt base =
      { physical :=
          (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).indexAt base
        background := backgroundCore.indexAt base
        normal := normalCore.indexAt base } :=
  rfl

/-- Coordinate changes act independently on the physical, background, and
normal components. -/
theorem physicalSecondJetBackgroundNormalCore_coordChange_apply
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    (first second : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart))
    (base : Base)
    (vector : PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber)) :
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).coordChange first second base vector =
      (((physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).coordChange
          first.physical second.physical base vector.1.1,
        backgroundCore.coordChange first.background second.background base vector.1.2),
        normalCore.coordChange first.normal second.normal base vector.2) :=
  rfl

/-- The complete six-sector coordinate change on an overlap as a continuous
linear equivalence. -/
def physicalSecondJetBackgroundNormalCoordChangeEquiv
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart)
    {first second : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart)}
    {base : Base}
    (hBase : base ∈
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).baseSet first ∩
      (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
        backgroundCore normalCore).baseSet second) :
    PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber) ≃L[𝕜]
      PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber) :=
  vectorBundleCoreCoordChangeEquiv
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore) hBase

/-- Smoothness of the six-sector core follows from the already assembled
physical core and the two added source cores. -/
theorem physicalSecondJetBackgroundNormalCore_isContMDiff
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
    [normalCore.IsContMDiff IB ∞] :
    (physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore).IsContMDiff IB ∞ := by
  let physicalCore :=
    physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  let extendedCore :=
    physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore
  letI physicalCoreSmooth : physicalCore.IsContMDiff IB ∞ :=
    physicalSecondJetVectorBundleCore_isContMDiff IB
      gaugeCore llCore metricCore spinCCore
  constructor
  intro first second
  let overlap : Set Base :=
    extendedCore.baseSet first ∩ extendedCore.baseSet second
  have hPhysical :
      ContMDiffOn IB
        𝓘(𝕜,
          PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) →L[𝕜]
          PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
            (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)) ∞
        (fun base => physicalCore.coordChange first.physical second.physical base)
        overlap :=
    (physicalCore.contMDiffOn_coordChange IB first.physical second.physical).mono (by
      intro base hBase
      exact ⟨hBase.1.1.1, hBase.2.1.1⟩)
  have hBackground :
      ContMDiffOn IB 𝓘(𝕜, BackgroundFiber →L[𝕜] BackgroundFiber) ∞
        (fun base =>
          backgroundCore.coordChange first.background second.background base)
        overlap :=
    (backgroundCore.contMDiffOn_coordChange IB first.background second.background).mono (by
      intro base hBase
      exact ⟨hBase.1.1.2, hBase.2.1.2⟩)
  have hNormal :
      ContMDiffOn IB 𝓘(𝕜, NormalFiber →L[𝕜] NormalFiber) ∞
        (fun base => normalCore.coordChange first.normal second.normal base)
        overlap :=
    (normalCore.contMDiffOn_coordChange IB first.normal second.normal).mono (by
      intro base hBase
      exact ⟨hBase.1.2, hBase.2.2⟩)
  change ContMDiffOn IB
    𝓘(𝕜,
      PhysicalSecondJetBackgroundNormalFiber
          (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
          (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber) →L[𝕜]
        PhysicalSecondJetBackgroundNormalFiber
          (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
          (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber)) ∞
    (fun base =>
      ((physicalCore.coordChange first.physical second.physical base).prodMap
        (backgroundCore.coordChange first.background second.background base)).prodMap
          (normalCore.coordChange first.normal second.normal base))
    overlap
  exact (hPhysical.clm_prodMap hBackground).clm_prodMap hNormal

/-- Canonical smooth package for the physical, background, and normal slots. -/
structure PhysicalSecondJetBackgroundNormalSmoothCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore 𝕜 Base BackgroundFiber BackgroundChart)
    (normalCore : VectorBundleCore 𝕜 Base NormalFiber NormalChart) where
  core : VectorBundleCore 𝕜 Base
    (PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := NormalFiber))
    (PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart) (NormalChart := NormalChart))
  core_eq :
    core = physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore
  isContMDiff : core.IsContMDiff IB ∞

/-- Constructor using only the six already smooth source cores. -/
def physicalSecondJetBackgroundNormalSmoothCore
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
    [normalCore.IsContMDiff IB ∞] :
    PhysicalSecondJetBackgroundNormalSmoothCore IB gaugeCore llCore metricCore spinCCore
      backgroundCore normalCore where
  core := physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
    backgroundCore normalCore
  core_eq := rfl
  isContMDiff := physicalSecondJetBackgroundNormalCore_isContMDiff IB
    gaugeCore llCore metricCore spinCCore backgroundCore normalCore

end

end P0EFTJanusPhysicalSecondJetBackgroundNormalCore
end JanusFormal
