import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetProductVectorBundleCore

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore

universe uBase uField uModel uModelSpace
universe uFirstFiber uSecondFiber uFirstChart uSecondChart
universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart uOldChart uNewChart

variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]
variable {Model : Type uModel} [NormedAddCommGroup Model]
variable [NormedSpace 𝕜 Model]
variable {ModelSpace : Type uModelSpace} [TopologicalSpace ModelSpace]
variable (IB : ModelWithCorners 𝕜 Model ModelSpace)
variable {Base : Type uBase} [TopologicalSpace Base]
variable [ChartedSpace ModelSpace Base]
variable {n : ℕ∞ω}

variable {FirstFiber : Type uFirstFiber}
variable {SecondFiber : Type uSecondFiber}
variable [NormedAddCommGroup FirstFiber] [NormedSpace 𝕜 FirstFiber]
variable [NormedAddCommGroup SecondFiber] [NormedSpace 𝕜 SecondFiber]
variable {FirstChart : Type uFirstChart} {SecondChart : Type uSecondChart}

/-- Smooth coordinate changes are preserved by the binary product of two
vector-bundle cores over the same manifold base. -/
theorem vectorBundleCoreProd_isContMDiff
    (firstCore : VectorBundleCore 𝕜 Base FirstFiber FirstChart)
    (secondCore : VectorBundleCore 𝕜 Base SecondFiber SecondChart)
    [firstCore.IsContMDiff IB n]
    [secondCore.IsContMDiff IB n] :
    (vectorBundleCoreProd firstCore secondCore).IsContMDiff IB n where
  contMDiffOn_coordChange first second := by
    exact
      ((firstCore.contMDiffOn_coordChange IB first.1 second.1).mono (by
          intro base hBase
          exact ⟨hBase.1.1, hBase.2.1⟩)).clm_prodMap
        ((secondCore.contMDiffOn_coordChange IB first.2 second.2).mono (by
          intro base hBase
          exact ⟨hBase.1.2, hBase.2.2⟩))

variable {Fiber : Type uFirstFiber}
variable [NormedAddCommGroup Fiber] [NormedSpace 𝕜 Fiber]
variable {OldChart : Type uOldChart} {NewChart : Type uNewChart}

/-- Reindexing the chart type preserves smoothness of all coordinate changes. -/
theorem reindexVectorBundleCore_isContMDiff
    (core : VectorBundleCore 𝕜 Base Fiber OldChart)
    (indexEquiv : NewChart ≃ OldChart)
    [core.IsContMDiff IB n] :
    (reindexVectorBundleCore core indexEquiv).IsContMDiff IB n where
  contMDiffOn_coordChange first second :=
    core.contMDiffOn_coordChange IB (indexEquiv first) (indexEquiv second)

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
    [gaugeCore.IsContMDiff IB n]
    [llCore.IsContMDiff IB n]
    [metricCore.IsContMDiff IB n]
    [spinCCore.IsContMDiff IB n] :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).IsContMDiff
      IB n := by
  letI gaugeLLSmooth :
      (vectorBundleCoreProd gaugeCore llCore).IsContMDiff IB n :=
    vectorBundleCoreProd_isContMDiff IB gaugeCore llCore
  letI gaugeLLMetricSmooth :
      (vectorBundleCoreProd
        (vectorBundleCoreProd gaugeCore llCore) metricCore).IsContMDiff IB n :=
    vectorBundleCoreProd_isContMDiff IB
      (vectorBundleCoreProd gaugeCore llCore) metricCore
  letI nestedSmooth :
      (physicalSecondJetNestedProductCore gaugeCore llCore metricCore spinCCore).IsContMDiff
        IB n :=
    vectorBundleCoreProd_isContMDiff IB
      (vectorBundleCoreProd
        (vectorBundleCoreProd gaugeCore llCore) metricCore) spinCCore
  exact reindexVectorBundleCore_isContMDiff IB
    (physicalSecondJetNestedProductCore gaugeCore llCore metricCore spinCCore)
    physicalCommonChartEquiv

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
  isContMDiff : core.IsContMDiff IB n

/-- Canonical smooth-core package assembled from the four supplied smooth
second-jet cores. -/
def physicalSecondJetSmoothCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    [gaugeCore.IsContMDiff IB n]
    [llCore.IsContMDiff IB n]
    [metricCore.IsContMDiff IB n]
    [spinCCore.IsContMDiff IB n] :
    PhysicalSecondJetSmoothCore IB gaugeCore llCore metricCore spinCCore where
  core := physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore
  core_eq_physical := rfl
  isContMDiff :=
    physicalSecondJetVectorBundleCore_isContMDiff IB
      gaugeCore llCore metricCore spinCCore

end

end P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore
end JanusFormal
