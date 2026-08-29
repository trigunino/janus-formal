import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetProductVectorBundleCore

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore

universe uBase uField uModel uModelSpace
universe uFirstFiber uSecondFiber uFirstChart uSecondChart
universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]
variable {Model : Type uModel} [NormedAddCommGroup Model]
variable [NormedSpace 𝕜 Model]
variable {ModelSpace : Type uModelSpace} [TopologicalSpace ModelSpace]
variable (IB : ModelWithCorners 𝕜 Model ModelSpace)
variable {Base : Type uBase} [TopologicalSpace Base]
variable [ChartedSpace ModelSpace Base]

variable {FirstFiber : Type uFirstFiber}
variable {SecondFiber : Type uSecondFiber}
variable [NormedAddCommGroup FirstFiber] [NormedSpace 𝕜 FirstFiber]
variable [NormedAddCommGroup SecondFiber] [NormedSpace 𝕜 SecondFiber]
variable {FirstChart : Type uFirstChart}
variable {SecondChart : Type uSecondChart}

theorem vectorBundleCoreProd_isContMDiff
    (firstCore : VectorBundleCore 𝕜 Base FirstFiber FirstChart)
    (secondCore : VectorBundleCore 𝕜 Base SecondFiber SecondChart)
    [firstCore.IsContMDiff IB ∞]
    [secondCore.IsContMDiff IB ∞] :
    (vectorBundleCoreProd firstCore secondCore).IsContMDiff IB ∞ := by
  constructor
  intro first second
  let productCore := vectorBundleCoreProd firstCore secondCore
  let overlap : Set Base :=
    productCore.baseSet first ∩ productCore.baseSet second
  have hFirst :
      ContMDiffOn IB
        (modelWithCornersSelf 𝕜 (FirstFiber →L[𝕜] FirstFiber)) ∞
        (fun base ↦ firstCore.coordChange first.1 second.1 base) overlap :=
    (firstCore.contMDiffOn_coordChange IB first.1 second.1).mono (by
      intro base hBase
      exact ⟨hBase.1.1, hBase.2.1⟩)
  have hSecond :
      ContMDiffOn IB
        (modelWithCornersSelf 𝕜 (SecondFiber →L[𝕜] SecondFiber)) ∞
        (fun base ↦ secondCore.coordChange first.2 second.2 base) overlap :=
    (secondCore.contMDiffOn_coordChange IB first.2 second.2).mono (by
      intro base hBase
      exact ⟨hBase.1.2, hBase.2.2⟩)
  change ContMDiffOn IB
    (modelWithCornersSelf 𝕜
      ((FirstFiber × SecondFiber) →L[𝕜] (FirstFiber × SecondFiber))) ∞
    (fun base ↦
      (firstCore.coordChange first.1 second.1 base).prodMap
        (secondCore.coordChange first.2 second.2 base)) overlap
  exact hFirst.clm_prodMap hSecond

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

/-- The common gauge--LL--metric--SpinC second-jet core has smooth transition
maps whenever each of its four source cores does. -/
theorem physicalSecondJetVectorBundleCore_isContMDiff
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    [gaugeCore.IsContMDiff IB ∞]
    [llCore.IsContMDiff IB ∞]
    [metricCore.IsContMDiff IB ∞]
    [spinCCore.IsContMDiff IB ∞] :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).IsContMDiff
      IB ∞ := by
  constructor
  intro first second
  let physicalCore :=
    physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  let overlap : Set Base :=
    physicalCore.baseSet first ∩ physicalCore.baseSet second
  have hGauge :
      ContMDiffOn IB 𝓘(𝕜, GaugeFiber →L[𝕜] GaugeFiber) ∞
        (fun base => gaugeCore.coordChange first.gauge second.gauge base)
        overlap :=
    (gaugeCore.contMDiffOn_coordChange IB first.gauge second.gauge).mono (by
      intro base hBase
      exact ⟨hBase.1.1.1.1, hBase.2.1.1.1⟩)
  have hLL :
      ContMDiffOn IB 𝓘(𝕜, LLFiber →L[𝕜] LLFiber) ∞
        (fun base => llCore.coordChange first.ll second.ll base)
        overlap :=
    (llCore.contMDiffOn_coordChange IB first.ll second.ll).mono (by
      intro base hBase
      exact ⟨hBase.1.1.1.2, hBase.2.1.1.2⟩)
  have hMetric :
      ContMDiffOn IB 𝓘(𝕜, MetricFiber →L[𝕜] MetricFiber) ∞
        (fun base => metricCore.coordChange first.metric second.metric base)
        overlap :=
    (metricCore.contMDiffOn_coordChange IB first.metric second.metric).mono (by
      intro base hBase
      exact ⟨hBase.1.1.2, hBase.2.1.2⟩)
  have hSpinC :
      ContMDiffOn IB 𝓘(𝕜, SpinCFiber →L[𝕜] SpinCFiber) ∞
        (fun base => spinCCore.coordChange first.spinC second.spinC base)
        overlap :=
    (spinCCore.contMDiffOn_coordChange IB first.spinC second.spinC).mono (by
      intro base hBase
      exact ⟨hBase.1.2, hBase.2.2⟩)
  change ContMDiffOn IB
    𝓘(𝕜,
      (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)) →L[𝕜]
        PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
          (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)) ∞
    (fun base =>
      (((gaugeCore.coordChange first.gauge second.gauge base).prodMap
          (llCore.coordChange first.ll second.ll base)).prodMap
        (metricCore.coordChange first.metric second.metric base)).prodMap
        (spinCCore.coordChange first.spinC second.spinC base))
    overlap
  exact ((hGauge.clm_prodMap hLL).clm_prodMap hMetric).clm_prodMap hSpinC

/-- Concrete package consisting of the unique four-sector physical core and its
smooth coordinate-change certificate. -/
structure PhysicalSecondJetSmoothCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart) where
  core : VectorBundleCore 𝕜 Base
    (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber))
    (PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
  core_eq_physical :
    core = physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  isContMDiff : core.IsContMDiff IB ∞

/-- Canonical smooth-core package assembled from the four supplied smooth
second-jet cores. -/
def physicalSecondJetSmoothCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    [gaugeCore.IsContMDiff IB ∞]
    [llCore.IsContMDiff IB ∞]
    [metricCore.IsContMDiff IB ∞]
    [spinCCore.IsContMDiff IB ∞] :
    PhysicalSecondJetSmoothCore IB gaugeCore llCore metricCore spinCCore where
  core := physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  core_eq_physical := rfl
  isContMDiff :=
    physicalSecondJetVectorBundleCore_isContMDiff IB
      gaugeCore llCore metricCore spinCCore

end

end P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore
end JanusFormal
