import Mathlib

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetCommonRefinedAtlas

set_option autoImplicit false

noncomputable section

open Set

universe uBase uChart uGauge uLL uMetric uSpinC uField uFiber

/-- The open-cover part of a bundle atlas.  It retains exactly the data needed
for a common refinement, before any coordinate-change law is assembled. -/
structure OpenChartCover
    (Base : Type uBase) (Chart : Type uChart) [TopologicalSpace Base] where
  baseSet : Chart → Set Base
  isOpen_baseSet : ∀ chart, IsOpen (baseSet chart)
  indexAt : Base → Chart
  mem_baseSet_at : ∀ base, base ∈ baseSet (indexAt base)

variable {Base : Type uBase} [TopologicalSpace Base]
variable {𝕜 : Type uField} {Fiber : Type uFiber} {Chart : Type uChart}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup Fiber] [NormedSpace 𝕜 Fiber]

/-- Every `VectorBundleCore` supplies an open chart cover.  Smoothness and the
coordinate-change laws stay on the original core; this projection forgets
neither coverage nor the actual chart domains. -/
def openChartCoverOfVectorBundleCore
    (core : VectorBundleCore 𝕜 Base Fiber Chart) :
    OpenChartCover Base Chart where
  baseSet := core.baseSet
  isOpen_baseSet := core.isOpen_baseSet
  indexAt := core.indexAt
  mem_baseSet_at := core.mem_baseSet_at

/-- One chart of the physical common refinement records one chart in each of
the gauge, Lorentz--Lorentz, metric and SpinC atlases. -/
structure PhysicalCommonChart
    (GaugeChart : Type uGauge)
    (LLChart : Type uLL)
    (MetricChart : Type uMetric)
    (SpinCChart : Type uSpinC) where
  gauge : GaugeChart
  ll : LLChart
  metric : MetricChart
  spinC : SpinCChart

variable {GaugeChart : Type uGauge}
variable {LLChart : Type uLL}
variable {MetricChart : Type uMetric}
variable {SpinCChart : Type uSpinC}

/-- Domain of a common physical chart: the exact intersection of the four
source chart domains. -/
def physicalCommonBaseSet
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    Set Base :=
  (((gaugeAtlas.baseSet chart.gauge ∩ llAtlas.baseSet chart.ll) ∩
      metricAtlas.baseSet chart.metric) ∩ spinCAtlas.baseSet chart.spinC)

/-- Common physical chart domains are open. -/
theorem physicalCommonBaseSet_isOpen
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    IsOpen (physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas chart) := by
  exact (((gaugeAtlas.isOpen_baseSet chart.gauge).inter
      (llAtlas.isOpen_baseSet chart.ll)).inter
      (metricAtlas.isOpen_baseSet chart.metric)).inter
      (spinCAtlas.isOpen_baseSet chart.spinC)

/-- Canonical common chart selected at a base point. -/
def physicalCommonChartAt
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (base : Base) :
    PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart where
  gauge := gaugeAtlas.indexAt base
  ll := llAtlas.indexAt base
  metric := metricAtlas.indexAt base
  spinC := spinCAtlas.indexAt base

/-- The canonical common chart contains its base point. -/
theorem mem_physicalCommonBaseSet_at
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (base : Base) :
    base ∈ physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas
      (physicalCommonChartAt gaugeAtlas llAtlas metricAtlas spinCAtlas base) := by
  exact ⟨⟨⟨gaugeAtlas.mem_baseSet_at base, llAtlas.mem_baseSet_at base⟩,
    metricAtlas.mem_baseSet_at base⟩, spinCAtlas.mem_baseSet_at base⟩

/-- The four source atlases have a canonical common open refinement. -/
def physicalCommonRefinedAtlas
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart) :
    OpenChartCover Base
      (PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) where
  baseSet := physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas
  isOpen_baseSet := fun chart =>
    physicalCommonBaseSet_isOpen gaugeAtlas llAtlas metricAtlas spinCAtlas chart
  indexAt := physicalCommonChartAt gaugeAtlas llAtlas metricAtlas spinCAtlas
  mem_baseSet_at := fun base =>
    mem_physicalCommonBaseSet_at gaugeAtlas llAtlas metricAtlas spinCAtlas base

/-- Every common chart refines its gauge chart. -/
theorem physicalCommonBaseSet_subset_gauge
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas chart ⊆
      gaugeAtlas.baseSet chart.gauge := by
  intro base hbase
  exact hbase.1.1.1

/-- Every common chart refines its Lorentz--Lorentz chart. -/
theorem physicalCommonBaseSet_subset_ll
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas chart ⊆
      llAtlas.baseSet chart.ll := by
  intro base hbase
  exact hbase.1.1.2

/-- Every common chart refines its metric chart. -/
theorem physicalCommonBaseSet_subset_metric
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas chart ⊆
      metricAtlas.baseSet chart.metric := by
  intro base hbase
  exact hbase.1.2

/-- Every common chart refines its SpinC chart. -/
theorem physicalCommonBaseSet_subset_spinC
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    physicalCommonBaseSet gaugeAtlas llAtlas metricAtlas spinCAtlas chart ⊆
      spinCAtlas.baseSet chart.spinC := by
  intro base hbase
  exact hbase.2

/-- Explicit cover statement for the common refinement. -/
theorem physicalCommonRefinedAtlas_covers
    (gaugeAtlas : OpenChartCover Base GaugeChart)
    (llAtlas : OpenChartCover Base LLChart)
    (metricAtlas : OpenChartCover Base MetricChart)
    (spinCAtlas : OpenChartCover Base SpinCChart)
    (base : Base) :
    ∃ chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart,
      base ∈ (physicalCommonRefinedAtlas gaugeAtlas llAtlas metricAtlas spinCAtlas).baseSet chart := by
  exact ⟨physicalCommonChartAt gaugeAtlas llAtlas metricAtlas spinCAtlas base,
    mem_physicalCommonBaseSet_at gaugeAtlas llAtlas metricAtlas spinCAtlas base⟩

end

end P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
end JanusFormal
