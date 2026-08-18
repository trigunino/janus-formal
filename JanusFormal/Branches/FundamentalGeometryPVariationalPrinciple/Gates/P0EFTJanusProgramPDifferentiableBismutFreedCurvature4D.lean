import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D

/-!
# Curvature derived from a differentiable Bismut--Freed one-form

The curvature of a determinant connection is not an independent alternating
function.  On a real normed parameter space, a Frechet-differentiable complex
one-form

`A : Base → (Base →L[Real] Complex)`

has curvature

`F_b(u,v) = DA_b[u](v) - DA_b[v](u)`.

This file makes that formula definitional.  Antisymmetry is therefore proved,
not supplied.  The families-index input is represented separately by a genuine
continuous bilinear two-form and compared pointwise with this derived
curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D

variable {Base : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]

/-- Frechet-differentiable geometric Bismut--Freed one-form. -/
structure DifferentiableLinearGeometricBismutFreedOneFormData (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base] where
  geometry : LinearGeometricBismutFreedOneFormData Base
  derivative : Base → Base →L[Real] (Base →L[Real] Complex)
  hasFDerivAt_oneForm : ∀ base,
    HasFDerivAt geometry.oneForm (derivative base) base

namespace DifferentiableLinearGeometricBismutFreedOneFormData

/-- Curvature derived from the exterior derivative of the connection one-form. -/
def curvature
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base first second : Base) : Complex :=
  data.derivative base first second - data.derivative base second first

/-- Curvature is antisymmetric by construction. -/
theorem curvature_antisymm
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base first second : Base) :
    data.curvature base first second = -data.curvature base second first := by
  unfold curvature
  abel

/-- Curvature vanishes on the diagonal. -/
@[simp]
theorem curvature_self
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base direction : Base) :
    data.curvature base direction direction = 0 := by
  simp [curvature]

/-- Additivity in the first tangent direction. -/
theorem curvature_add_left
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base first second third : Base) :
    data.curvature base (first + second) third =
      data.curvature base first third + data.curvature base second third := by
  unfold curvature
  simp only [map_add, add_apply, sub_eq_add_neg]
  abel

/-- Additivity in the second tangent direction. -/
theorem curvature_add_right
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base first second third : Base) :
    data.curvature base first (second + third) =
      data.curvature base first second + data.curvature base first third := by
  rw [data.curvature_antisymm base first (second + third),
    data.curvature_add_left base second third first,
    data.curvature_antisymm base second first,
    data.curvature_antisymm base third first]
  abel

/-- Real homogeneity in the first tangent direction. -/
theorem curvature_smul_left
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base : Base) (scalar : Real) (first second : Base) :
    data.curvature base (scalar • first) second =
      scalar • data.curvature base first second := by
  unfold curvature
  rw [map_smul, map_smul]
  change
    (scalar : Complex) * data.derivative base first second -
        (scalar : Complex) * data.derivative base second first =
      (scalar : Complex) *
        (data.derivative base first second - data.derivative base second first)
  ring

/-- Real homogeneity in the second tangent direction. -/
theorem curvature_smul_right
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Base)
    (base : Base) (scalar : Real) (first second : Base) :
    data.curvature base first (scalar • second) =
      scalar • data.curvature base first second := by
  rw [data.curvature_antisymm base first (scalar • second),
    data.curvature_smul_left base scalar second first,
    data.curvature_antisymm base second first]
  simp

end DifferentiableLinearGeometricBismutFreedOneFormData

/-- Genuine continuous bilinear local families-index two-form.  Antisymmetry is
stored because this local index object is independent input; unlike BF
curvature it is not defined here as an exterior derivative. -/
structure LocalFamiliesIndexTwoFormData (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base] where
  twoForm : Base → Base →L[Real] (Base →L[Real] Complex)
  antisymm : ∀ base first second,
    twoForm base first second = -twoForm base second first

/-- The derived BF curvature equals the local families-index two-form. -/
structure DerivedBismutFreedFamiliesIndexComparisonData (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base] where
  bismutFreed : DifferentiableLinearGeometricBismutFreedOneFormData Base
  localIndex : LocalFamiliesIndexTwoFormData Base
  curvature_agreement : ∀ base first second,
    bismutFreed.curvature base first second =
      localIndex.twoForm base first second

namespace DerivedBismutFreedFamiliesIndexComparisonData

/-- The local index two-form inherits the same derived BF curvature formula. -/
theorem localIndex_eq_exteriorDerivative
    (data : DerivedBismutFreedFamiliesIndexComparisonData Base)
    (base first second : Base) :
    data.localIndex.twoForm base first second =
      data.bismutFreed.derivative base first second -
        data.bismutFreed.derivative base second first := by
  rw [← data.curvature_agreement]
  rfl

/-- The local index form and the derived BF curvature have matching
antisymmetry, with no separately supplied BF antisymmetry field. -/
theorem localIndex_antisymm_from_BF
    (data : DerivedBismutFreedFamiliesIndexComparisonData Base)
    (base first second : Base) :
    data.localIndex.twoForm base first second =
      -data.localIndex.twoForm base second first := by
  rw [← data.curvature_agreement base first second,
    ← data.curvature_agreement base second first]
  exact data.bismutFreed.curvature_antisymm base first second

/-- Public derived-curvature families-index checkpoint. -/
theorem derived_bismut_freed_families_index_comparison_gate
    (data : DerivedBismutFreedFamiliesIndexComparisonData Base) :
    (∀ base first second,
      data.bismutFreed.curvature base first second =
        data.localIndex.twoForm base first second) ∧
    (∀ base first second,
      data.bismutFreed.curvature base first second =
        -data.bismutFreed.curvature base second first) ∧
    (∀ base first second,
      data.localIndex.twoForm base first second =
        data.bismutFreed.derivative base first second -
          data.bismutFreed.derivative base second first) :=
  ⟨data.curvature_agreement,
    data.bismutFreed.curvature_antisymm,
    data.localIndex_eq_exteriorDerivative⟩

end DerivedBismutFreedFamiliesIndexComparisonData

end
end P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
end JanusFormal
