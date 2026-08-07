import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShift4D

/-!
# Exact range identification from a surjective finite-defect shift

Assume the finite-defect shifted operator `H + P` is surjective.  The stored
relation `PH = 0` gives `range H ⊆ ker P`.  Conversely, for `y ∈ ker P`, choose
`x` with `Hx + Px = y`.  Applying `P` and using `PH = 0` and `P² = P` yields
`Px = 0`, hence `Hx = y`.

Thus

`range H = ker P`.

Together with the kernel identification `ker H = range P`, this gives the
exact finite-dimensional Fredholm splitting used by the terminal Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectRangeIdentification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

private theorem projection_operator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (operator vector) = 0 := by
  have h := congrArg
    (fun map : E →L[Real] E => map vector)
    data.projection_annihilates_operator
  simpa [ContinuousLinearMap.comp_apply] using h

private theorem projection_projection_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (vector : E) :
    data.projection (data.projection vector) = data.projection vector := by
  have h := congrArg
    (fun map : E →L[Real] E => map vector)
    data.projection_idempotent
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Every value of `H` lies in the kernel of the defect projection. -/
theorem finiteDefect_operator_range_le_projection_ker
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    operator.range ≤ data.projection.ker := by
  rintro value ⟨source, rfl⟩
  exact LinearMap.mem_ker.mpr
    (projection_operator_apply operator data source)

/-- Surjectivity of `H + P` fills every vector in `ker P` with an actual value
of `H`. -/
theorem finiteDefect_projection_ker_le_operator_range
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    data.projection.ker ≤ operator.range := by
  intro value hValue
  obtain ⟨source, hSource⟩ := hSurjective value
  have hValueProjection : data.projection value = 0 :=
    LinearMap.mem_ker.mp hValue
  have hProjected := congrArg data.projection hSource
  change data.projection (operator source + data.projection source) =
    data.projection value at hProjected
  rw [map_add, projection_operator_apply operator data,
    projection_projection_apply operator data, zero_add,
    hValueProjection] at hProjected
  have hSourceProjection : data.projection source = 0 := hProjected
  refine ⟨source, ?_⟩
  change operator source = value
  change operator source + data.projection source = value at hSource
  rw [hSourceProjection, add_zero] at hSource
  exact hSource

/-- Exact range identification. -/
theorem finiteDefect_operator_range_eq_projection_ker
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    operator.range = data.projection.ker := by
  apply le_antisymm
  · exact finiteDefect_operator_range_le_projection_ker operator data
  · exact finiteDefect_projection_ker_le_operator_range operator data hSurjective

/-- Public exact-range checkpoint. -/
theorem finite_defect_range_identification_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data)) :
    operator.range = data.projection.ker :=
  finiteDefect_operator_range_eq_projection_ker operator data hSurjective

end
end P0EFTJanusProgramPFiniteDefectRangeIdentification4D
end JanusFormal
