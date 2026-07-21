import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D

/-! # Algebraic Dirac-spinor representation of ambient PinC(4)

The gamma representation sends the ambient Pin group to invertible complex
`4 × 4` matrices.  Multiplication by the circle phase gives a product
representation; the simultaneous central sign `(-1,-1)` acts trivially, so
the action descends to the actual diagonal `PinC(4)` quotient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D

set_option autoImplicit false
noncomputable section

open CliffordAlgebra
open scoped Matrix
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D

/-- Pin-minus action obtained by mapping Clifford units through the gamma
algebra representation. -/
def ambientPinMinusGammaRepresentation :
    AmbientCoordinatePinMinusGroup →* AmbientComplexMatrix4ˣ :=
  (Units.map ambientCliffordGammaRepresentation.toMonoidHom).comp
    pinGroup.toUnits

@[simp] theorem ambientPinMinusGammaRepresentation_coe
    (pin : AmbientCoordinatePinMinusGroup) :
    ((ambientPinMinusGammaRepresentation pin : AmbientComplexMatrix4ˣ) :
        AmbientComplexMatrix4) =
      ambientCliffordGammaRepresentation
        (pin : AmbientPinMinusCliffordAlgebra) :=
  rfl

/-- Scalar matrix action of the `U(1)` phase. -/
def ambientCircleGammaScalarRepresentation :
    Circle →* AmbientComplexMatrix4ˣ :=
  (Units.map (algebraMap Complex AmbientComplexMatrix4).toMonoidHom).comp
    Circle.toUnits

@[simp] theorem ambientCircleGammaScalarRepresentation_coe
    (phase : Circle) :
    ((ambientCircleGammaScalarRepresentation phase : AmbientComplexMatrix4ˣ) :
        AmbientComplexMatrix4) =
      algebraMap Complex AmbientComplexMatrix4 (phase : Complex) :=
  rfl

theorem ambientCircleGammaScalarRepresentation_commutes
    (phase : Circle) (matrix : AmbientComplexMatrix4ˣ) :
    ambientCircleGammaScalarRepresentation phase * matrix =
      matrix * ambientCircleGammaScalarRepresentation phase := by
  apply Units.ext
  change algebraMap Complex AmbientComplexMatrix4 (phase : Complex) *
      (matrix : AmbientComplexMatrix4) =
    (matrix : AmbientComplexMatrix4) *
      algebraMap Complex AmbientComplexMatrix4 (phase : Complex)
  exact Algebra.commutes _ _

/-- Product Pin-minus/phase action on four-component complex spinors. -/
def ambientPinCProductSpinorRepresentation :
    AmbientCoordinatePinMinusGroup × Circle →* AmbientComplexMatrix4ˣ where
  toFun element :=
    ambientPinMinusGammaRepresentation element.1 *
      ambientCircleGammaScalarRepresentation element.2
  map_one' := by simp
  map_mul' first second := by
    change
      ambientPinMinusGammaRepresentation (first.1 * second.1) *
          ambientCircleGammaScalarRepresentation (first.2 * second.2) =
        (ambientPinMinusGammaRepresentation first.1 *
            ambientCircleGammaScalarRepresentation first.2) *
          (ambientPinMinusGammaRepresentation second.1 *
            ambientCircleGammaScalarRepresentation second.2)
    rw [map_mul, map_mul]
    symm
    calc
      (ambientPinMinusGammaRepresentation first.1 *
            ambientCircleGammaScalarRepresentation first.2) *
          (ambientPinMinusGammaRepresentation second.1 *
            ambientCircleGammaScalarRepresentation second.2) =
        ambientPinMinusGammaRepresentation first.1 *
          (ambientCircleGammaScalarRepresentation first.2 *
            ambientPinMinusGammaRepresentation second.1) *
          ambientCircleGammaScalarRepresentation second.2 := by
            simp [mul_assoc]
      _ = ambientPinMinusGammaRepresentation first.1 *
          (ambientPinMinusGammaRepresentation second.1 *
            ambientCircleGammaScalarRepresentation first.2) *
          ambientCircleGammaScalarRepresentation second.2 := by
            rw [ambientCircleGammaScalarRepresentation_commutes]
      _ = (ambientPinMinusGammaRepresentation first.1 *
            ambientPinMinusGammaRepresentation second.1) *
          (ambientCircleGammaScalarRepresentation first.2 *
            ambientCircleGammaScalarRepresentation second.2) := by
            simp [mul_assoc]

theorem ambientPinCProductSpinorRepresentation_diagonalMinusOne :
    ambientPinCProductSpinorRepresentation ambientPinCDiagonalMinusOne = 1 := by
  apply Units.ext
  change ambientCliffordGammaRepresentation
        (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) *
      algebraMap Complex AmbientComplexMatrix4 (-1 : Complex) = 1
  rw [ambientPinMinusCentralSign_coe, map_neg, map_one]
  simp

private theorem ambientPinCDiagonalSubgroup_le_spinorKernel :
    ambientPinCDiagonalSubgroup ≤
      ambientPinCProductSpinorRepresentation.ker := by
  apply Subgroup.normalClosure_le_normal
  intro element hElement
  rw [Set.mem_singleton_iff.mp hElement]
  exact ambientPinCProductSpinorRepresentation_diagonalMinusOne

/-- Four-component complex spinor representation of the diagonal PinC
quotient. -/
def ambientPinCSpinorMatrixRepresentation :
    AmbientPinC4 →* AmbientComplexMatrix4ˣ :=
  QuotientGroup.lift ambientPinCDiagonalSubgroup
    ambientPinCProductSpinorRepresentation
    ambientPinCDiagonalSubgroup_le_spinorKernel

@[simp] theorem ambientPinCSpinorMatrixRepresentation_mk
    (pin : AmbientCoordinatePinMinusGroup) (phase : Circle) :
    ambientPinCSpinorMatrixRepresentation
        (QuotientGroup.mk' ambientPinCDiagonalSubgroup (pin, phase)) =
      ambientPinMinusGammaRepresentation pin *
        ambientCircleGammaScalarRepresentation phase := by
  exact QuotientGroup.lift_mk' _ _ (pin, phase)

def ambientPinCSpinorAction
    (element : AmbientPinC4) (spinor : AmbientDiracSpinor4) :
    AmbientDiracSpinor4 :=
  (ambientPinCSpinorMatrixRepresentation element : AmbientComplexMatrix4) *ᵥ
    spinor

@[simp] theorem ambientPinCSpinorAction_one
    (spinor : AmbientDiracSpinor4) :
    ambientPinCSpinorAction 1 spinor = spinor := by
  simp [ambientPinCSpinorAction, Matrix.one_mulVec]

theorem ambientPinCSpinorAction_mul
    (first second : AmbientPinC4) (spinor : AmbientDiracSpinor4) :
    ambientPinCSpinorAction (first * second) spinor =
      ambientPinCSpinorAction first
        (ambientPinCSpinorAction second spinor) := by
  simp [ambientPinCSpinorAction, Matrix.mulVec_mulVec]

def ambientCliffordGammaAction
    (vector : CoverCoordinates) (spinor : AmbientDiracSpinor4) :
    AmbientDiracSpinor4 :=
  ambientGammaMatrix vector *ᵥ spinor

theorem ambientCliffordGammaAction_sq
    (vector : CoverCoordinates) (spinor : AmbientDiracSpinor4) :
    ambientCliffordGammaAction vector
        (ambientCliffordGammaAction vector spinor) =
      ((ambientCoverPinMinusQuadraticForm vector : Real) : Complex) • spinor := by
  unfold ambientCliffordGammaAction
  rw [Matrix.mulVec_mulVec, ambientGammaMatrix_sq]
  ext index
  fin_cases index <;>
    simp [Matrix.algebraMap_matrix_apply, Matrix.mulVec, dotProduct]

structure ProgramPAmbientPinCSpinorRepresentationCertificate4D where
  spinor : Type
  spinor_eq : spinor = AmbientDiracSpinor4
  representation : AmbientPinC4 →* AmbientComplexMatrix4ˣ
  representationCanonical :
    representation = ambientPinCSpinorMatrixRepresentation
  action : AmbientPinC4 → AmbientDiracSpinor4 → AmbientDiracSpinor4
  actionCanonical : action = ambientPinCSpinorAction
  actionOne : ∀ spinor, action 1 spinor = spinor
  actionMul : ∀ first second spinor,
    action (first * second) spinor = action first (action second spinor)
  cliffordSquare : ∀ vector spinor,
    ambientCliffordGammaAction vector
        (ambientCliffordGammaAction vector spinor) =
      ((ambientCoverPinMinusQuadraticForm vector : Real) : Complex) • spinor

def programPAmbientPinCSpinorRepresentationCertificate4D :
    ProgramPAmbientPinCSpinorRepresentationCertificate4D where
  spinor := AmbientDiracSpinor4
  spinor_eq := rfl
  representation := ambientPinCSpinorMatrixRepresentation
  representationCanonical := rfl
  action := ambientPinCSpinorAction
  actionCanonical := rfl
  actionOne := ambientPinCSpinorAction_one
  actionMul := ambientPinCSpinorAction_mul
  cliffordSquare := ambientCliffordGammaAction_sq

theorem programPAmbientPinCSpinorRepresentationCertificate4D_nonempty :
    Nonempty ProgramPAmbientPinCSpinorRepresentationCertificate4D :=
  ⟨programPAmbientPinCSpinorRepresentationCertificate4D⟩

end
end P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
end JanusFormal
