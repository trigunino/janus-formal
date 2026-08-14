import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaConnection4D

/-!
# C1 canonical-coordinate section of the full Fredholm--zeta determinant bundle

The full determinant bundle has a global canonical complex coordinate.  In that
coordinate the dependent zeta section is exactly the scalar Mellin/zeta
determinant.  Therefore its C1 regularity and its connection equation are
literal consequences of the existing scalar zeta family, with no derivative
of a varying dependent fibre required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmZetaC1CoordinateSection4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 5000000
noncomputable section

open Bundle Topology
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D
open P0EFTJanusProgramPFullTensorZetaConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Coordinate of the genuine dependent full determinant zeta section. -/
def fullDeterminantZetaCoordinate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) : Complex :=
  fredholm.fullTensorDeterminantCoordinateEquiv parameter
    (fullDeterminantZetaSection fredholm zetaFamily parameter)

/-- The dependent section coordinate is exactly the intrinsic scalar zeta
determinant. -/
@[simp]
theorem fullDeterminantZetaCoordinate_eq
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    fullDeterminantZetaCoordinate fredholm zetaFamily =
      relativeHeatMellinZetaFamilyDeterminant zetaFamily := by
  funext parameter
  exact fullDeterminantZetaSection_coordinate fredholm zetaFamily parameter

/-- Canonical coordinate derivative of the full determinant section. -/
def fullDeterminantZetaCoordinateDerivative
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) : Complex :=
  relativeZetaDeterminantCoordinateDerivative
    zetaFamily.toZetaFamily parameter

/-- The genuine full determinant section is C1 in its global canonical
trivialization. -/
theorem fullDeterminantZetaCoordinate_hasDerivAt
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    HasDerivAt (fullDeterminantZetaCoordinate fredholm zetaFamily)
      (fullDeterminantZetaCoordinateDerivative zetaFamily parameter)
      parameter := by
  rw [fullDeterminantZetaCoordinate_eq]
  exact relativeZetaDeterminantCoordinate_hasDerivAt
    zetaFamily.toZetaFamily parameter

/-- The canonical coordinate family is differentiable everywhere. -/
theorem fullDeterminantZetaCoordinate_differentiable
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Differentiable Real (fullDeterminantZetaCoordinate fredholm zetaFamily) :=
  fun parameter =>
    (fullDeterminantZetaCoordinate_hasDerivAt fredholm zetaFamily parameter).
      differentiableAt

/-- The full determinant zeta section is nowhere zero, expressed inside its
actual dependent fibre. -/
theorem fullDeterminantZetaSection_ne_zero
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fullDeterminantZetaSection fredholm zetaFamily parameter ≠ 0 := by
  intro hZero
  have hCoordinate := congrArg
    (fredholm.fullTensorDeterminantCoordinateEquiv parameter) hZero
  rw [map_zero, fullDeterminantZetaSection_coordinate] at hCoordinate
  exact relativeZetaDeterminantCoordinate_ne_zero
    zetaFamily.toZetaFamily parameter hCoordinate

/-- Scalar connection equation written directly for the canonical coordinate
of the genuine full determinant section. -/
theorem fullDeterminantZetaCoordinate_parallel
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    relativeZetaConnectionAt zetaFamily.toZetaFamily parameter
        (fullDeterminantZetaCoordinate fredholm zetaFamily parameter)
        (fullDeterminantZetaCoordinateDerivative zetaFamily parameter) = 0 := by
  rw [fullDeterminantZetaCoordinate_eq]
  exact relativeZetaDeterminantCoordinate_parallel
    zetaFamily.toZetaFamily parameter

/-- Public C1 full determinant-section checkpoint. -/
theorem self_adjoint_fredholm_zeta_c1_coordinate_section_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Differentiable Real (fullDeterminantZetaCoordinate fredholm zetaFamily) ∧
    (∀ parameter,
      fullDeterminantZetaSection fredholm zetaFamily parameter ≠ 0) ∧
    (∀ parameter,
      relativeZetaConnectionAt zetaFamily.toZetaFamily parameter
          (fullDeterminantZetaCoordinate fredholm zetaFamily parameter)
          (fullDeterminantZetaCoordinateDerivative zetaFamily parameter) = 0) :=
  ⟨fullDeterminantZetaCoordinate_differentiable fredholm zetaFamily,
    fullDeterminantZetaSection_ne_zero fredholm zetaFamily,
    fullDeterminantZetaCoordinate_parallel fredholm zetaFamily⟩

end
end P0EFTJanusProgramPSelfAdjointFredholmZetaC1CoordinateSection4D
end JanusFormal
