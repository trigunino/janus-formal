import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceOrientedBoundaryObstruction4D

/-!
# One-dimensional Euler equations do not kill the Green flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeEulerWronskianNoGo4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D

/-- First-order presentation of the scalar equation `f'' + m² f = 0`. -/
def OneDimensionalEulerSolution
    (massSquared : Real) (field derivative : Real → Real) : Prop :=
  ∀ normal,
    CanonicalLatitudeScalarHasDerivAt field (derivative normal) normal ∧
      CanonicalLatitudeScalarHasDerivAt derivative
        (-massSquared * field normal) normal

/-- The corresponding one-dimensional Green--Wronskian current. -/
def oneDimensionalGreenCurrent
    (field fieldDerivative test testDerivative : Real → Real)
    (normal : Real) : Real :=
  field normal * testDerivative normal - fieldDerivative normal * test normal

theorem one_oneDimensionalEulerSolution :
    OneDimensionalEulerSolution 0 (fun _ : Real => 1) (fun _ => 0) := by
  intro normal
  constructor
  · unfold CanonicalLatitudeScalarHasDerivAt
    exact hasDerivAt_const normal 1
  · unfold CanonicalLatitudeScalarHasDerivAt
    simpa using hasDerivAt_const normal 0

theorem id_oneDimensionalEulerSolution :
    OneDimensionalEulerSolution 0 id (fun _ => 1) := by
  intro normal
  constructor
  · unfold CanonicalLatitudeScalarHasDerivAt
    exact hasDerivAt_id normal
  · unfold CanonicalLatitudeScalarHasDerivAt
    simpa using hasDerivAt_const normal 1

theorem one_id_oneDimensionalGreenCurrent_eq_one (normal : Real) :
    oneDimensionalGreenCurrent (fun _ : Real => 1) (fun _ => 0)
      id (fun _ => 1) normal = 1 := by
  simp [oneDimensionalGreenCurrent]

/-- Equal-mass one-dimensional Euler equations alone cannot imply zero Green
flux; the missing input is genuinely global. -/
theorem oneDimensionalEuler_not_implies_greenCurrent_zero :
    ¬ ∀ (field fieldDerivative test testDerivative : Real → Real),
        OneDimensionalEulerSolution 0 field fieldDerivative →
        OneDimensionalEulerSolution 0 test testDerivative →
        ∀ normal,
          oneDimensionalGreenCurrent field fieldDerivative test testDerivative
            normal = 0 := by
  intro hUniversal
  have hZero := hUniversal (fun _ : Real => 1) (fun _ => 0)
    id (fun _ => 1) one_oneDimensionalEulerSolution
      id_oneDimensionalEulerSolution 0
  rw [one_id_oneDimensionalGreenCurrent_eq_one] at hZero
  norm_num at hZero

end
end P0EFTJanusMappingTorusCanonicalLatitudeEulerWronskianNoGo4D
end JanusFormal
