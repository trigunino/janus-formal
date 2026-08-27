import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Generic frame/chart-pair second-jet vector-bundle core

This gate packages an open cover and continuous-linear transition cocycle into
a `VectorBundleCore`.  The model fiber is arbitrary, so the constructor can be
reused for gauge, tensor and product second-jet representations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

variable {Base Fiber Index : Type*}
  [TopologicalSpace Base]
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Build a real vector-bundle core from operator-level identity and cocycle
laws on an open cover. -/
def frameChartPairSecondJetVectorBundleCore
    (baseSet : Index → Set Base)
    (isOpenBaseSet : ∀ index, IsOpen (baseSet index))
    (indexAt : Base → Index)
    (memBaseSetAt : ∀ point, point ∈ baseSet (indexAt point))
    (coordChange : Index → Index → Base → Fiber →L[Real] Fiber)
    (coordChangeSelf : ∀ index point, point ∈ baseSet index →
      coordChange index index point = ContinuousLinearMap.id Real Fiber)
    (continuousOnCoordChange : ∀ first second,
      ContinuousOn (coordChange first second)
        (baseSet first ∩ baseSet second))
    (coordChangeComp : ∀ first middle last point,
      point ∈ baseSet first ∩ baseSet middle ∩ baseSet last →
        (coordChange middle last point).comp
            (coordChange first middle point) =
          coordChange first last point) :
    VectorBundleCore Real Base Fiber Index where
  baseSet := baseSet
  isOpen_baseSet := isOpenBaseSet
  indexAt := indexAt
  mem_baseSet_at := memBaseSetAt
  coordChange := coordChange
  coordChange_self index point hPoint value := by
    rw [coordChangeSelf index point hPoint]
    rfl
  continuousOn_coordChange := continuousOnCoordChange
  coordChange_comp first middle last point hPoint value := by
    exact congrArg (fun map : Fiber →L[Real] Fiber ↦ map value)
      (coordChangeComp first middle last point hPoint)

@[simp]
theorem frameChartPairSecondJetVectorBundleCore_baseSet
    (baseSet : Index → Set Base)
    (isOpenBaseSet : ∀ index, IsOpen (baseSet index))
    (indexAt : Base → Index)
    (memBaseSetAt : ∀ point, point ∈ baseSet (indexAt point))
    (coordChange : Index → Index → Base → Fiber →L[Real] Fiber)
    (coordChangeSelf : ∀ index point, point ∈ baseSet index →
      coordChange index index point = ContinuousLinearMap.id Real Fiber)
    (continuousOnCoordChange : ∀ first second,
      ContinuousOn (coordChange first second)
        (baseSet first ∩ baseSet second))
    (coordChangeComp : ∀ first middle last point,
      point ∈ baseSet first ∩ baseSet middle ∩ baseSet last →
        (coordChange middle last point).comp
            (coordChange first middle point) =
          coordChange first last point)
    (index : Index) :
    (frameChartPairSecondJetVectorBundleCore baseSet isOpenBaseSet indexAt
      memBaseSetAt coordChange coordChangeSelf continuousOnCoordChange
      coordChangeComp).baseSet index = baseSet index :=
  rfl

@[simp]
theorem frameChartPairSecondJetVectorBundleCore_coordChange
    (baseSet : Index → Set Base)
    (isOpenBaseSet : ∀ index, IsOpen (baseSet index))
    (indexAt : Base → Index)
    (memBaseSetAt : ∀ point, point ∈ baseSet (indexAt point))
    (coordChange : Index → Index → Base → Fiber →L[Real] Fiber)
    (coordChangeSelf : ∀ index point, point ∈ baseSet index →
      coordChange index index point = ContinuousLinearMap.id Real Fiber)
    (continuousOnCoordChange : ∀ first second,
      ContinuousOn (coordChange first second)
        (baseSet first ∩ baseSet second))
    (coordChangeComp : ∀ first middle last point,
      point ∈ baseSet first ∩ baseSet middle ∩ baseSet last →
        (coordChange middle last point).comp
            (coordChange first middle point) =
          coordChange first last point)
    (first second : Index) (point : Base) :
    (frameChartPairSecondJetVectorBundleCore baseSet isOpenBaseSet indexAt
      memBaseSetAt coordChange coordChangeSelf continuousOnCoordChange
      coordChangeComp).coordChange first second point =
        coordChange first second point :=
  rfl

/-- Smooth transition operators upgrade the constructed core to Mathlib's
`VectorBundleCore.IsContMDiff` mixin. -/
theorem frameChartPairSecondJetVectorBundleCore_isContMDiff
    {Model ModelSpace : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    [TopologicalSpace ModelSpace]
    (I : ModelWithCorners Real Model ModelSpace)
    [ChartedSpace ModelSpace Base]
    (n : ℕ∞ω)
    (baseSet : Index → Set Base)
    (isOpenBaseSet : ∀ index, IsOpen (baseSet index))
    (indexAt : Base → Index)
    (memBaseSetAt : ∀ point, point ∈ baseSet (indexAt point))
    (coordChange : Index → Index → Base → Fiber →L[Real] Fiber)
    (coordChangeSelf : ∀ index point, point ∈ baseSet index →
      coordChange index index point = ContinuousLinearMap.id Real Fiber)
    (continuousOnCoordChange : ∀ first second,
      ContinuousOn (coordChange first second)
        (baseSet first ∩ baseSet second))
    (coordChangeComp : ∀ first middle last point,
      point ∈ baseSet first ∩ baseSet middle ∩ baseSet last →
        (coordChange middle last point).comp
            (coordChange first middle point) =
          coordChange first last point)
    (contMDiffOnCoordChange : ∀ first second,
      ContMDiffOn I 𝓘(Real, Fiber →L[Real] Fiber) n
        (coordChange first second) (baseSet first ∩ baseSet second)) :
    (frameChartPairSecondJetVectorBundleCore baseSet isOpenBaseSet indexAt
      memBaseSetAt coordChange coordChangeSelf continuousOnCoordChange
      coordChangeComp).IsContMDiff I n := by
  constructor
  exact contMDiffOnCoordChange

end
end P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D
end JanusFormal
