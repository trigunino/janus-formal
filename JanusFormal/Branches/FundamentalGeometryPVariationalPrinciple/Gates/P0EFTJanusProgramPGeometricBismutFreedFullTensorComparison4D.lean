import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaConnection4D

/-!
# Geometric Bismut--Freed connection on the full Fredholm--zeta determinant line

The pathwise geometric/operator comparison is independent of the finite kernel
factor.  This file lifts it to the genuine full determinant fibre

`(Complex ⊗[Real] Det_Fred(H_a)) ⊗[Complex] Det_red(H_a)`.

The ambient Fredholm family and the reduced logarithmic-trace family are kept
as distinct typed objects; only their common zeta coordinate is used to couple
them.  Thus no reduced complement is identified definitionally with the
ambient Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPFullTensorZetaConnection4D
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {Ambient Reduced Base Tangent ZeroMode : Type*}
  [NormedAddCommGroup Ambient] [NormedSpace Real Ambient]
  [InnerProductSpace Real Ambient] [CompleteSpace Ambient]
  [NormedAddCommGroup Reduced] [NormedSpace Real Reduced]
  [InnerProductSpace Real Reduced] [CompleteSpace Reduced]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Pull the geometric connection coefficient into the genuine full
Fredholm--zeta determinant fibre. -/
def geometricFullTensorConnectionAt
    {ambientOperator : Real → Ambient →L[Real] Ambient}
    {actual reference : Real → Reduced →L[Real] Reduced}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData
      ambientOperator ZeroMode)
    (comparison : GeometricOperatorBismutFreedPathComparisonData
      actual reference Base Tangent)
    (parameter : Real) (value derivative : Complex) :
    fredholm.fullTensorDeterminantLine parameter :=
  fredholm.fullTensorDeterminantSection parameter
    (comparison.geometricConnectionAt parameter value derivative)

/-- The full geometric connection equals the already constructed full zeta
connection once the geometric/operator one-form comparison is supplied. -/
theorem geometricFullTensorConnectionAt_eq_zeta
    {ambientOperator : Real → Ambient →L[Real] Ambient}
    {actual reference : Real → Reduced →L[Real] Reduced}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData
      ambientOperator ZeroMode)
    (comparison : GeometricOperatorBismutFreedPathComparisonData
      actual reference Base Tangent)
    (parameter : Real) (value derivative : Complex) :
    geometricFullTensorConnectionAt fredholm comparison parameter value derivative =
      fullTensorZetaConnectionAt fredholm comparison.operatorFamily.zetaFamily
        parameter value derivative := by
  unfold geometricFullTensorConnectionAt fullTensorZetaConnectionAt
  congr 1
  rw [comparison.geometricConnectionAt_eq_operator]
  exact comparison.operatorFamily.connectionAt_eq_zeta parameter value derivative

/-- The full Fredholm--zeta determinant section is parallel for the pulled-back
geometric Bismut--Freed connection. -/
theorem fullTensorDeterminant_parallel_geometric
    {ambientOperator : Real → Ambient →L[Real] Ambient}
    {actual reference : Real → Reduced →L[Real] Reduced}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData
      ambientOperator ZeroMode)
    (comparison : GeometricOperatorBismutFreedPathComparisonData
      actual reference Base Tangent)
    (parameter : Real) :
    geometricFullTensorConnectionAt fredholm comparison parameter
        (relativeHeatMellinZetaFamilyDeterminant
          comparison.operatorFamily.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          comparison.operatorFamily.zetaFamily.toZetaFamily parameter) = 0 := by
  unfold geometricFullTensorConnectionAt
  rw [comparison.determinant_parallel_geometric parameter]
  simp [SelfAdjointFredholmDeterminantFamilyData.fullTensorDeterminantSection]

/-- Public geometric full determinant-line comparison checkpoint. -/
theorem geometric_bismut_freed_full_tensor_comparison_gate
    {ambientOperator : Real → Ambient →L[Real] Ambient}
    {actual reference : Real → Reduced →L[Real] Reduced}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData
      ambientOperator ZeroMode)
    (comparison : GeometricOperatorBismutFreedPathComparisonData
      actual reference Base Tangent) :
    (∀ parameter value derivative,
      geometricFullTensorConnectionAt fredholm comparison parameter value derivative =
        fullTensorZetaConnectionAt fredholm
          comparison.operatorFamily.zetaFamily parameter value derivative) ∧
    (∀ parameter,
      geometricFullTensorConnectionAt fredholm comparison parameter
          (relativeHeatMellinZetaFamilyDeterminant
            comparison.operatorFamily.zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            comparison.operatorFamily.zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨geometricFullTensorConnectionAt_eq_zeta fredholm comparison,
    fullTensorDeterminant_parallel_geometric fredholm comparison⟩

end
end P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
end JanusFormal
