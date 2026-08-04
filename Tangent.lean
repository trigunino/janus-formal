import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Function Filter Set

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
private def tangentSpaceModelCoordinates
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    (I : ModelWithCorners Real E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (point : M) : TangentSpace I point ≃L[Real] E where
  toFun vector := vector
  invFun vector := vector
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
theorem localDiffeomorph_mfderiv_rightInverse_test
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    (I : ModelWithCorners Real E H)
    [TopologicalSpace M] [ChartedSpace H M]
    {f : E → M} {x : E}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf Real E) I ⊤ f x)
    {y : M} (hy : y ∈ hf.localInverse.source)
    (hForward : MDifferentiableAt (modelWithCornersSelf Real E) I f
      (hf.localInverse y))
    (vector : E) :
    tangentSpaceModelCoordinates I (f (hf.localInverse y))
        (mfderiv (modelWithCornersSelf Real E) I f (hf.localInverse y)
          (mfderiv I (modelWithCornersSelf Real E) hf.localInverse y vector)) =
      vector := by
  have hInverse : MDifferentiableAt I (modelWithCornersSelf Real E)
      hf.localInverse y :=
    hf.localInverse.mdifferentiableAt (by simp) hy
  have hChain := mfderiv_comp_apply y hForward hInverse vector
  have hRight : (f ∘ hf.localInverse) =ᶠ[nhds y] id :=
    eventuallyEq_of_mem
      (hf.localInverse.open_source.mem_nhds hy)
      hf.localInverse_eqOn_right
  rw [← hChain]
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := I) (I' := I) hRight
  have hApply := congrArg (fun derivative =>
    tangentSpaceModelCoordinates I y
      (derivative vector)) hDerivative
  have hId : tangentSpaceModelCoordinates I y
      ((ContinuousLinearMap.id Real (TangentSpace I y)) vector) = vector := by
    rfl
  rw [mfderiv_id] at hApply
  exact hApply.trans hId
