import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D

set_option autoImplicit false
noncomputable section

open Module
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D

/-- The signed continuous top form selected by the fixed throat basis. -/
def programPT06ThroatSignedVolume :
    ThroatCoverCoordinates [⋀^Fin 3]→L[Real] Real :=
  { programPT06ThroatSpatialBasis.det with
    cont := by
      change Continuous (fun vectors =>
        Matrix.det (programPT06ThroatSpatialBasis.toMatrix vectors))
      exact programPT06ThroatSpatialBasis.continuous_toMatrix.matrix_det }

@[simp] theorem programPT06ThroatSignedVolume_apply_basis :
    programPT06ThroatSignedVolume programPT06ThroatSpatialBasis = 1 := by
  change programPT06ThroatSpatialBasis.det programPT06ThroatSpatialBasis = 1
  exact programPT06ThroatSpatialBasis.det_self

private theorem programPT06ThroatSignedVolume_insert_basis
    (direction : Fin 3) (vector : ThroatCoverCoordinates) :
    programPT06ThroatSignedVolume
        (direction.insertNth vector
          (direction.removeNth programPT06ThroatSpatialBasis)) =
      programPT06ThroatSpatialBasis.equivFun vector direction := by
  rw [Fin.insertNth_removeNth]
  change programPT06ThroatSpatialBasis.det
      (Function.update programPT06ThroatSpatialBasis direction vector) =
    programPT06ThroatSpatialBasis.repr vector direction
  rw [Basis.det_apply, Basis.toMatrix_update, Basis.toMatrix_self]
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

private theorem programPT06ThroatSignedVolume_curry_remove_basis
    (direction : Fin 3) (vector : ThroatCoverCoordinates) :
    (-1 : Int) ^ direction.val •
        programPT06ThroatSignedVolume.curryLeft vector
          (direction.removeNth programPT06ThroatSpatialBasis) =
      programPT06ThroatSpatialBasis.equivFun vector direction := by
  calc
    _ = programPT06ThroatSignedVolume
        (direction.insertNth vector
          (direction.removeNth programPT06ThroatSpatialBasis)) := by
      symm
      simpa [ContinuousAlternatingMap.curryLeft_apply_apply] using
        programPT06ThroatSignedVolume.toAlternatingMap.map_insertNth
          direction vector (direction.removeNth programPT06ThroatSpatialBasis)
    _ = _ := programPT06ThroatSignedVolume_insert_basis direction vector

/-- The flux two-form obtained by contracting the signed volume with a vector field. -/
def programPT06ThroatSignedFluxForm
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates) :
    ThroatCoverCoordinates →
      ThroatCoverCoordinates [⋀^Fin 2]→L[Real] Real :=
  fun coordinate => programPT06ThroatSignedVolume.curryLeft (field coordinate)

/-- Coordinate divergence in the fixed throat basis. -/
def programPT06ThroatCoordinateDivergence
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (coordinate : ThroatCoverCoordinates) : Real :=
  ∑ direction : Fin 3,
    programPT06ThroatSpatialBasis.equivFun
      (fderiv Real field coordinate
        (programPT06ThroatSpatialBasis direction)) direction

/-- Pullback of the signed flux form by a local coordinate map. -/
def programPT06ThroatSignedFluxPullback
    (coordinateMap field : ThroatCoverCoordinates → ThroatCoverCoordinates) :
    ThroatCoverCoordinates →
      ThroatCoverCoordinates [⋀^Fin 2]→L[Real] Real :=
  fun coordinate =>
    (programPT06ThroatSignedFluxForm field (coordinateMap coordinate)).compContinuousLinearMap
      (fderiv Real coordinateMap coordinate)

/-- A constant vector field has closed signed flux form. -/
theorem programPT06ThroatSignedFluxForm_constant_extDeriv
    (vector coordinate : ThroatCoverCoordinates) :
    extDeriv (programPT06ThroatSignedFluxForm (fun _ => vector)) coordinate = 0 := by
  have hFlux : DifferentiableAt Real
      (programPT06ThroatSignedFluxForm (fun _ => vector)) coordinate :=
    programPT06ThroatSignedVolume.curryLeft.differentiableAt.comp coordinate
      (differentiableAt_const vector)
  ext vectors
  rw [extDeriv_apply hFlux vectors]
  simp [programPT06ThroatSignedFluxForm]

private theorem programPT06ThroatSignedFluxForm_differentiableAt
    {field : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hField : DifferentiableAt Real field coordinate) :
    DifferentiableAt Real (programPT06ThroatSignedFluxForm field) coordinate :=
  programPT06ThroatSignedVolume.curryLeft.differentiableAt.comp coordinate hField

/-- The exterior derivative of the flux evaluates to coordinate divergence. -/
theorem programPT06ThroatSignedFluxForm_extDeriv_apply_basis
    {field : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hField : DifferentiableAt Real field coordinate) :
    extDeriv (programPT06ThroatSignedFluxForm field) coordinate
        programPT06ThroatSpatialBasis =
      programPT06ThroatCoordinateDivergence field coordinate := by
  let hFlux : DifferentiableAt Real
      (programPT06ThroatSignedFluxForm field) coordinate :=
    programPT06ThroatSignedFluxForm_differentiableAt hField
  have hFluxDerivative : HasFDerivAt
      (programPT06ThroatSignedFluxForm field)
      (programPT06ThroatSignedVolume.curryLeft.comp
        (fderiv Real field coordinate)) coordinate :=
    programPT06ThroatSignedVolume.curryLeft.hasFDerivAt.comp coordinate
      hField.hasFDerivAt
  rw [extDeriv_apply hFlux programPT06ThroatSpatialBasis]
  unfold programPT06ThroatCoordinateDivergence
  apply Finset.sum_congr rfl
  intro direction _
  rw [fderiv_continuousAlternatingMap_apply_const_apply hFlux]
  rw [hFluxDerivative.fderiv]
  simpa only [ContinuousLinearMap.comp_apply] using
    programPT06ThroatSignedVolume_curry_remove_basis direction
      (fderiv Real field coordinate
        (programPT06ThroatSpatialBasis direction))

/-- The signed flux differential is divergence times the fixed volume form. -/
theorem programPT06ThroatSignedFluxForm_extDeriv
    {field : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hField : DifferentiableAt Real field coordinate) :
    extDeriv (programPT06ThroatSignedFluxForm field) coordinate =
      programPT06ThroatCoordinateDivergence field coordinate •
        programPT06ThroatSignedVolume := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [(extDeriv (programPT06ThroatSignedFluxForm field) coordinate).toAlternatingMap
    |>.eq_smul_basis_det programPT06ThroatSpatialBasis]
  have hEvaluation :
      (extDeriv (programPT06ThroatSignedFluxForm field) coordinate).toAlternatingMap
          programPT06ThroatSpatialBasis =
        programPT06ThroatCoordinateDivergence field coordinate := by
    change extDeriv (programPT06ThroatSignedFluxForm field) coordinate
        programPT06ThroatSpatialBasis = _
    exact programPT06ThroatSignedFluxForm_extDeriv_apply_basis hField
  rw [hEvaluation]
  rfl

/-- A signed top form acquires the determinant of a linear map on the fixed basis. -/
theorem programPT06ThroatSignedTopForm_comp_apply_basis
    (form : ThroatCoverCoordinates [⋀^Fin 3]→L[Real] Real)
    (linear : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) :
    (form.compContinuousLinearMap linear) programPT06ThroatSpatialBasis =
      LinearMap.det linear.toLinearMap * form programPT06ThroatSpatialBasis := by
  change form.toAlternatingMap (linear ∘ programPT06ThroatSpatialBasis) = _
  rw [form.toAlternatingMap.eq_smul_basis_det programPT06ThroatSpatialBasis]
  have hDet :
      programPT06ThroatSpatialBasis.det
          (linear ∘ programPT06ThroatSpatialBasis) =
        LinearMap.det linear.toLinearMap := by
    convert programPT06ThroatSpatialBasis.det_comp linear.toLinearMap
      programPT06ThroatSpatialBasis using 1
    · rfl
    · simp only [programPT06ThroatSpatialBasis.det_self, mul_one]
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [hDet]
  exact mul_comm _ _

/-- Exterior-form Piola naturality, including the signed Jacobian factor when
evaluated on the fixed throat basis. -/
theorem programPT06ThroatSignedFluxPullback_extDeriv_apply_basis
    {coordinateMap field : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hField : DifferentiableAt Real field (coordinateMap coordinate))
    (hCoordinateMap : ContDiffAt Real 2 coordinateMap coordinate) :
    extDeriv (programPT06ThroatSignedFluxPullback coordinateMap field) coordinate
        programPT06ThroatSpatialBasis =
      LinearMap.det (fderiv Real coordinateMap coordinate).toLinearMap *
        extDeriv (programPT06ThroatSignedFluxForm field) (coordinateMap coordinate)
          programPT06ThroatSpatialBasis := by
  unfold programPT06ThroatSignedFluxPullback
  rw [extDeriv_pullback
    (programPT06ThroatSignedFluxForm_differentiableAt hField)
    hCoordinateMap (by simp)]
  exact programPT06ThroatSignedTopForm_comp_apply_basis _ _

/-- Signed Piola law: pulled-back flux divergence carries the Jacobian
determinant, with no absolute value. -/
theorem programPT06ThroatSignedFluxPullback_extDeriv_eq_det_mul_divergence
    {coordinateMap field : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hField : DifferentiableAt Real field (coordinateMap coordinate))
    (hCoordinateMap : ContDiffAt Real 2 coordinateMap coordinate) :
    extDeriv (programPT06ThroatSignedFluxPullback coordinateMap field) coordinate
        programPT06ThroatSpatialBasis =
      LinearMap.det (fderiv Real coordinateMap coordinate).toLinearMap *
        programPT06ThroatCoordinateDivergence field (coordinateMap coordinate) := by
  rw [programPT06ThroatSignedFluxPullback_extDeriv_apply_basis
    hField hCoordinateMap]
  rw [programPT06ThroatSignedFluxForm_extDeriv_apply_basis hField]

end
end P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
end JanusFormal
