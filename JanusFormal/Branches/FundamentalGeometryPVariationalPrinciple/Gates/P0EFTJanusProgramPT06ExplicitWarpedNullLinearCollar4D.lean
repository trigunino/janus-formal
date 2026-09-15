import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D

/-!
# Explicit linear collar of the warped null hyperplane

This gate extends the chart `(u,x,y) ↦ (u,x,y,u)` to the global linear collar
`((u,x,y),r) ↦ (u,x,y,u+r)`.  The collar is a continuous linear equivalence,
its zero slice is the explicit null hyperplane, and the defining function is
exactly the collar coordinate `r`.

The coordinate `r` is not identified with a mapping-torus collar.  No metric
volume, screen integration, or Stokes theorem is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D

set_option autoImplicit false

noncomputable section

open Module
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D

/-- Null-source coordinates with one transverse collar coordinate. -/
abbrev ProgramPT06WarpedNullCollarCoordinate4 :=
  ProgramPT06NullFaceSource3 × Real

/-- Global linear collar `((u,x,y),r) ↦ (u,x,y,u+r)`. -/
def programPT06WarpedNullCollarLinearEquiv :
    ProgramPT06WarpedNullCollarCoordinate4 ≃ₗ[Real]
      ProgramPT06AmbientCoordinate4 where
  toFun coordinate :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      ![coordinate.1.1, coordinate.1.2 0, coordinate.1.2 1,
        coordinate.1.1 + coordinate.2]
  invFun point :=
    ((point 0,
      (EuclideanSpace.equiv (Fin 2) Real).symm ![point 1, point 2]),
      point 3 - point 0)
  left_inv coordinate := by
    rcases coordinate with ⟨⟨parameter, screen⟩, radius⟩
    apply Prod.ext
    · apply Prod.ext
      · simp
      · apply (EuclideanSpace.equiv (Fin 2) Real).injective
        funext direction
        fin_cases direction <;> simp
    · simp
  right_inv point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext direction
    fin_cases direction <;> simp
  map_add' first second := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext direction
    fin_cases direction <;> simp [add_assoc, add_left_comm]
  map_smul' scalar coordinate := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext direction
    fin_cases direction <;> simp [mul_add]

/-- The linear collar as a continuous linear equivalence. -/
def programPT06WarpedNullCollarEquiv :
    ProgramPT06WarpedNullCollarCoordinate4 ≃L[Real]
      ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarLinearEquiv.toContinuousLinearEquiv

@[simp] theorem programPT06WarpedNullCollarEquiv_apply
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    programPT06WarpedNullCollarEquiv coordinate =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        ![coordinate.1.1, coordinate.1.2 0, coordinate.1.2 1,
          coordinate.1.1 + coordinate.2] := by
  rfl

@[simp] theorem programPT06WarpedNullCollarEquiv_symm_apply
    (point : ProgramPT06AmbientCoordinate4) :
    programPT06WarpedNullCollarEquiv.symm point =
      ((point 0,
        (EuclideanSpace.equiv (Fin 2) Real).symm ![point 1, point 2]),
        point 3 - point 0) := by
  rfl

/-- The zero collar slice is exactly the explicit warped null embedding. -/
@[simp] theorem programPT06WarpedNullCollar_zeroSlice
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCollarEquiv (source, 0) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext direction
  fin_cases direction <;> simp

/-- The hyperplane defining function is the transverse collar coordinate. -/
@[simp] theorem programPT06WarpedNullHyperplaneDefiningDifferential_collar
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    programPT06WarpedNullHyperplaneDefiningDifferential
        (programPT06WarpedNullCollarEquiv coordinate) = coordinate.2 := by
  rcases coordinate with ⟨⟨parameter, screen⟩, radius⟩
  simp

/-- The derivative of the collar is its underlying continuous linear map. -/
theorem programPT06WarpedNullCollarEquiv_hasFDerivAt
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    HasFDerivAt programPT06WarpedNullCollarEquiv
      programPT06WarpedNullCollarEquiv.toContinuousLinearMap coordinate :=
  programPT06WarpedNullCollarEquiv.hasFDerivAt

theorem programPT06WarpedNullCollarEquiv_fderiv
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    fderiv Real programPT06WarpedNullCollarEquiv coordinate =
      programPT06WarpedNullCollarEquiv.toContinuousLinearMap :=
  (programPT06WarpedNullCollarEquiv_hasFDerivAt coordinate).fderiv

/-- The positive collar derivative is the fourth coordinate vector `e₃`. -/
theorem programPT06WarpedNullCollar_radialDerivative
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    fderiv Real programPT06WarpedNullCollarEquiv coordinate (0, 1) =
      programPT06AmbientCoordinateBasis 3 := by
  rw [programPT06WarpedNullCollarEquiv_fderiv]
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext direction
  fin_cases direction <;>
    simp [programPT06WarpedNullCollarEquiv,
      programPT06WarpedNullCollarLinearEquiv,
      programPT06AmbientCoordinateBasis]

/-- Outward-vector convention for the lower boundary of the future half-collar
`0 ≤ r`. -/
def programPT06WarpedNullCollarZeroBoundaryOutward :
    ProgramPT06AmbientCoordinate4 :=
  -programPT06AmbientCoordinateBasis 3

/-- The lower-boundary outward vector differs from the `e₀` rigging by the
null generator tangent to the face. -/
theorem programPT06WarpedNullCollarZeroBoundaryOutward_eq_rigging_sub_generator
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCollarZeroBoundaryOutward =
      programPT06WarpedNullHyperplaneRawTransverse source -
        programPT06WarpedNullHyperplaneGeneratorDifferential 1 := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext direction
  fin_cases direction <;>
    simp [programPT06WarpedNullCollarZeroBoundaryOutward,
      programPT06WarpedNullHyperplaneRawTransverse,
      programPT06AmbientCoordinateBasis]

/-- Subtracting the tangent generator does not change the coordinate flux. -/
theorem programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_rigging
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        programPT06WarpedNullCollarZeroBoundaryOutward
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) =
      programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullHyperplaneRawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) := by
  let frame := programPT06FiniteNullFaceGeometricTangentFrame
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit) 0 () source
  have hGeneratorFlux :
      programPT06AmbientSignedVolume.curryLeft
          (programPT06WarpedNullHyperplaneGeneratorDifferential 1) frame = 0 := by
    rw [ContinuousAlternatingMap.curryLeft_apply_apply]
    exact programPT06AmbientSignedVolume.map_eq_zero_of_eq
      (Matrix.vecCons
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1) frame)
      (i := (0 : Fin 4)) (j := (0 : Fin 3).succ)
      (by simp [frame, programPT06FiniteNullFaceGeometricTangentFrame,
        programPT06ExplicitWarpedNullHyperplaneGeometry])
      (Fin.succ_ne_zero 0).symm
  change programPT06AmbientSignedVolume.curryLeft
      programPT06WarpedNullCollarZeroBoundaryOutward frame =
    programPT06AmbientSignedVolume.curryLeft
      (programPT06WarpedNullHyperplaneRawTransverse source) frame
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_eq_rigging_sub_generator
    source]
  rw [map_sub, ContinuousAlternatingMap.sub_apply, hGeneratorFlux, sub_zero]

/-- The future lower-boundary outward convention is transverse to the null
tangent frame. -/
theorem programPT06WarpedNullCollarZeroBoundaryOutward_flux_ne_zero
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        programPT06WarpedNullCollarZeroBoundaryOutward
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) ≠ 0 := by
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_rigging]
  exact programPT06WarpedNullHyperplaneRawTransverse_flux_ne_zero source

/-- The defining coordinate increases at unit speed along the positive collar
direction. -/
theorem programPT06WarpedNullHyperplaneDefiningDifferential_radialDerivative
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    programPT06WarpedNullHyperplaneDefiningDifferential
        (fderiv Real programPT06WarpedNullCollarEquiv coordinate (0, 1)) = 1 := by
  rw [programPT06WarpedNullCollar_radialDerivative]
  simp [programPT06AmbientCoordinateBasis]

end
end P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
end JanusFormal
