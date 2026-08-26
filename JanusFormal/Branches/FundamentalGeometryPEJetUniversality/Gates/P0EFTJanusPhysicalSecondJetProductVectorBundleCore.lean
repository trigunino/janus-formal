import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetCommonRefinedAtlas

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetProductVectorBundleCore

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas

universe uBase uField uFirstFiber uSecondFiber uFirstChart uSecondChart
universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart uOldChart uNewChart

variable {Base : Type uBase} [TopologicalSpace Base]
variable {𝕜 : Type uField} [NontriviallyNormedField 𝕜]

variable {FirstFiber : Type uFirstFiber}
variable {SecondFiber : Type uSecondFiber}
variable [NormedAddCommGroup FirstFiber] [NormedSpace 𝕜 FirstFiber]
variable [NormedAddCommGroup SecondFiber] [NormedSpace 𝕜 SecondFiber]
variable {FirstChart : Type uFirstChart} {SecondChart : Type uSecondChart}

/-- Product of two vector-bundle cores over the same base.  Its charts and
fibers are products, its domains are exact intersections, and its coordinate
changes act componentwise. -/
def vectorBundleCoreProd
    (firstCore : VectorBundleCore 𝕜 Base FirstFiber FirstChart)
    (secondCore : VectorBundleCore 𝕜 Base SecondFiber SecondChart) :
    VectorBundleCore 𝕜 Base (FirstFiber × SecondFiber)
      (FirstChart × SecondChart) where
  baseSet chart :=
    firstCore.baseSet chart.1 ∩ secondCore.baseSet chart.2
  isOpen_baseSet chart :=
    (firstCore.isOpen_baseSet chart.1).inter
      (secondCore.isOpen_baseSet chart.2)
  indexAt base := (firstCore.indexAt base, secondCore.indexAt base)
  mem_baseSet_at base :=
    ⟨firstCore.mem_baseSet_at base, secondCore.mem_baseSet_at base⟩
  coordChange first second base :=
    (firstCore.coordChange first.1 second.1 base).prodMap
      (secondCore.coordChange first.2 second.2 base)
  coordChange_self chart base hBase vector := by
    rcases vector with ⟨firstVector, secondVector⟩
    change
      (firstCore.coordChange chart.1 chart.1 base firstVector,
        secondCore.coordChange chart.2 chart.2 base secondVector) =
      (firstVector, secondVector)
    rw [firstCore.coordChange_self chart.1 base hBase.1 firstVector,
      secondCore.coordChange_self chart.2 base hBase.2 secondVector]
  continuousOn_coordChange first second := by
    refine
      (((firstCore.continuousOn_coordChange first.1 second.1).mono ?_).prod_mapL 𝕜
        ((secondCore.continuousOn_coordChange first.2 second.2).mono ?_))
    · intro base hBase
      exact ⟨hBase.1.1, hBase.2.1⟩
    · intro base hBase
      exact ⟨hBase.1.2, hBase.2.2⟩
  coordChange_comp first second third base hBase vector := by
    rcases vector with ⟨firstVector, secondVector⟩
    change
      (firstCore.coordChange second.1 third.1 base
          (firstCore.coordChange first.1 second.1 base firstVector),
        secondCore.coordChange second.2 third.2 base
          (secondCore.coordChange first.2 second.2 base secondVector)) =
      (firstCore.coordChange first.1 third.1 base firstVector,
        secondCore.coordChange first.2 third.2 base secondVector)
    rw [firstCore.coordChange_comp first.1 second.1 third.1 base
        ⟨⟨hBase.1.1.1, hBase.1.2.1⟩, hBase.2.1⟩ firstVector,
      secondCore.coordChange_comp first.2 second.2 third.2 base
        ⟨⟨hBase.1.1.2, hBase.1.2.2⟩, hBase.2.2⟩ secondVector]

variable {Fiber : Type uFirstFiber} [NormedAddCommGroup Fiber]
variable [NormedSpace 𝕜 Fiber]
variable {OldChart : Type uOldChart} {NewChart : Type uNewChart}

/-- Reindex a vector-bundle core along an equivalence of chart types.  No base
set, fiber map, or coordinate-change law is altered. -/
def reindexVectorBundleCore
    (core : VectorBundleCore 𝕜 Base Fiber OldChart)
    (indexEquiv : NewChart ≃ OldChart) :
    VectorBundleCore 𝕜 Base Fiber NewChart where
  baseSet chart := core.baseSet (indexEquiv chart)
  isOpen_baseSet chart := core.isOpen_baseSet (indexEquiv chart)
  indexAt base := indexEquiv.symm (core.indexAt base)
  mem_baseSet_at base := by
    change base ∈ core.baseSet
      (indexEquiv (indexEquiv.symm (core.indexAt base)))
    rw [indexEquiv.apply_symm_apply]
    exact core.mem_baseSet_at base
  coordChange first second :=
    core.coordChange (indexEquiv first) (indexEquiv second)
  coordChange_self chart base hBase vector :=
    core.coordChange_self (indexEquiv chart) base hBase vector
  continuousOn_coordChange first second :=
    core.continuousOn_coordChange (indexEquiv first) (indexEquiv second)
  coordChange_comp first second third base hBase vector :=
    core.coordChange_comp (indexEquiv first) (indexEquiv second)
      (indexEquiv third) base hBase vector

/-- On a genuine overlap, the reverse coordinate change is a left inverse. -/
theorem vectorBundleCore_coordChange_leftInverse
    (core : VectorBundleCore 𝕜 Base Fiber OldChart)
    {first second : OldChart} {base : Base}
    (hBase : base ∈ core.baseSet first ∩ core.baseSet second)
    (vector : Fiber) :
    core.coordChange second first base
        (core.coordChange first second base vector) = vector := by
  calc
    core.coordChange second first base
        (core.coordChange first second base vector) =
        core.coordChange first first base vector :=
      core.coordChange_comp first second first base
        ⟨⟨hBase.1, hBase.2⟩, hBase.1⟩ vector
    _ = vector := core.coordChange_self first base hBase.1 vector

/-- On a genuine overlap, the reverse coordinate change is a right inverse. -/
theorem vectorBundleCore_coordChange_rightInverse
    (core : VectorBundleCore 𝕜 Base Fiber OldChart)
    {first second : OldChart} {base : Base}
    (hBase : base ∈ core.baseSet first ∩ core.baseSet second)
    (vector : Fiber) :
    core.coordChange first second base
        (core.coordChange second first base vector) = vector := by
  calc
    core.coordChange first second base
        (core.coordChange second first base vector) =
        core.coordChange second second base vector :=
      core.coordChange_comp second first second base
        ⟨⟨hBase.2, hBase.1⟩, hBase.2⟩ vector
    _ = vector := core.coordChange_self second base hBase.2 vector

/-- Coordinate change on an overlap as an actual continuous linear
equivalence. -/
def vectorBundleCoreCoordChangeEquiv
    (core : VectorBundleCore 𝕜 Base Fiber OldChart)
    {first second : OldChart} {base : Base}
    (hBase : base ∈ core.baseSet first ∩ core.baseSet second) :
    Fiber ≃L[𝕜] Fiber where
  toFun := core.coordChange first second base
  invFun := core.coordChange second first base
  left_inv := vectorBundleCore_coordChange_leftInverse core hBase
  right_inv := vectorBundleCore_coordChange_rightInverse core hBase
  map_add' := (core.coordChange first second base).map_add
  map_smul' := (core.coordChange first second base).map_smul
  continuous_toFun := (core.coordChange first second base).continuous
  continuous_invFun := (core.coordChange second first base).continuous

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

/-- Common physical fiber carrying gauge, LL, metric, and SpinC second jets. -/
abbrev PhysicalSecondJetFiber :=
  ((GaugeFiber × LLFiber) × MetricFiber) × SpinCFiber

/-- Identification of the named physical chart structure with the nested chart
product used by repeated binary core products. -/
def physicalCommonChartEquiv :
    PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart ≃
      (((GaugeChart × LLChart) × MetricChart) × SpinCChart) where
  toFun chart := (((chart.gauge, chart.ll), chart.metric), chart.spinC)
  invFun chart :=
    { gauge := chart.1.1.1
      ll := chart.1.1.2
      metric := chart.1.2
      spinC := chart.2 }
  left_inv chart := by
    cases chart
    rfl
  right_inv chart := by
    rcases chart with ⟨⟨⟨gauge, ll⟩, metric⟩, spinC⟩
    rfl

/-- Fourfold nested product before chart reindexing. -/
def physicalSecondJetNestedProductCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart) :
    VectorBundleCore 𝕜 Base
      (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber)
        (LLFiber := LLFiber) (MetricFiber := MetricFiber)
        (SpinCFiber := SpinCFiber))
      (((GaugeChart × LLChart) × MetricChart) × SpinCChart) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (vectorBundleCoreProd gaugeCore llCore) metricCore) spinCCore

/-- Physical second-jet vector-bundle core on the exact common refined atlas. -/
def physicalSecondJetVectorBundleCore
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart) :
    VectorBundleCore 𝕜 Base
      (PhysicalSecondJetFiber (GaugeFiber := GaugeFiber)
        (LLFiber := LLFiber) (MetricFiber := MetricFiber)
        (SpinCFiber := SpinCFiber))
      (PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :=
  reindexVectorBundleCore
    (physicalSecondJetNestedProductCore gaugeCore llCore metricCore spinCCore)
    physicalCommonChartEquiv

/-- The core domain is definitionally the exact fourfold common domain. -/
theorem physicalSecondJetVectorBundleCore_baseSet
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (chart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart) :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet chart =
      physicalCommonBaseSet
        (openChartCoverOfVectorBundleCore gaugeCore)
        (openChartCoverOfVectorBundleCore llCore)
        (openChartCoverOfVectorBundleCore metricCore)
        (openChartCoverOfVectorBundleCore spinCCore) chart :=
  rfl

/-- The preferred chart at a point is exactly the common chart selected from
all four source cores. -/
theorem physicalSecondJetVectorBundleCore_indexAt
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (base : Base) :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).indexAt base =
      physicalCommonChartAt
        (openChartCoverOfVectorBundleCore gaugeCore)
        (openChartCoverOfVectorBundleCore llCore)
        (openChartCoverOfVectorBundleCore metricCore)
        (openChartCoverOfVectorBundleCore spinCCore) base :=
  rfl

/-- Exact component formula for the physical coordinate change. -/
theorem physicalSecondJetVectorBundleCore_coordChange_apply
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    (first second : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (base : Base)
    (vector : PhysicalSecondJetFiber (GaugeFiber := GaugeFiber)
      (LLFiber := LLFiber) (MetricFiber := MetricFiber)
      (SpinCFiber := SpinCFiber)) :
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).coordChange
        first second base vector =
      (((gaugeCore.coordChange first.gauge second.gauge base vector.1.1.1,
          llCore.coordChange first.ll second.ll base vector.1.1.2),
        metricCore.coordChange first.metric second.metric base vector.1.2),
        spinCCore.coordChange first.spinC second.spinC base vector.2) :=
  rfl

/-- The physical coordinate change on an overlap, bundled with its reverse as
an actual continuous linear equivalence. -/
def physicalSecondJetCoordChangeEquiv
    (gaugeCore : VectorBundleCore 𝕜 Base GaugeFiber GaugeChart)
    (llCore : VectorBundleCore 𝕜 Base LLFiber LLChart)
    (metricCore : VectorBundleCore 𝕜 Base MetricFiber MetricChart)
    (spinCCore : VectorBundleCore 𝕜 Base SpinCFiber SpinCChart)
    {first second : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart}
    {base : Base}
    (hBase : base ∈
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet first ∩
      (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore).baseSet second) :
    PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) ≃L[𝕜]
      PhysicalSecondJetFiber (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber) :=
  vectorBundleCoreCoordChangeEquiv
    (physicalSecondJetVectorBundleCore gaugeCore llCore metricCore spinCCore) hBase

end

end P0EFTJanusPhysicalSecondJetProductVectorBundleCore
end JanusFormal
