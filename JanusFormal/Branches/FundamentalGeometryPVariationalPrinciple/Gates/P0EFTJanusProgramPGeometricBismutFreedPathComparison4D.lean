import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalFamilyQuillenBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D

/-!
# Pathwise geometric/operator Bismut--Freed comparison

The Program-P spectral construction produces the Bismut--Freed coefficient
from the intrinsic relative logarithmic trace.  The D11 natural-family layer
specifies the independent geometric input required before a Quillen connection
is canonical.

This file isolates the exact remaining comparison theorem on an arbitrary
geometric parameter base: after pulling the geometric Bismut--Freed one-form
back along a family path, its coefficient must equal the intrinsic operator
trace coefficient.  The circle is only one possible path and is not built into
this interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeometricBismutFreedPathComparison4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D

universe u v w x

variable {E : Type u} {Base : Type w} {Tangent : Type x}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Geometric Bismut--Freed connection one-form on an arbitrary parameter
base.  `Tangent` is deliberately abstract: later geometric layers may replace
it by the actual tangent bundle of a manifold or moduli stack. -/
structure GeometricBismutFreedOneFormData (Base Tangent : Type*) where
  oneForm : Base → Tangent → Complex

/-- One parametrized family path in the geometric base together with its
velocity. -/
structure GeometricFamilyPathData (Base Tangent : Type*) where
  point : Real → Base
  velocity : Real → Tangent

/-- Pullback of the geometric Bismut--Freed one-form to a real family path. -/
def pulledGeometricCoefficient
    (geometry : GeometricBismutFreedOneFormData Base Tangent)
    (path : GeometricFamilyPathData Base Tangent)
    (parameter : Real) : Complex :=
  geometry.oneForm (path.point parameter) (path.velocity parameter)

/-- Full natural-family/Quillen input together with the operator family and the
single comparison identity needed to identify the two connections. -/
structure GeometricOperatorBismutFreedPathComparisonData
    (actual reference : Real → E →L[Real] E)
    (Base : Type w) (Tangent : Type x) where
  analyticFamily : NaturalFamilyAnalyticUpgrade
  analyticFamilyClosed :
    ellipticFamilyInputClosed (toEllipticFamilyInputStatus analyticFamily)
  quillen : QuillenBismutFreedStatus
  quillenClosed : quillenBismutFreedClosed quillen
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  operatorFamily : RelativeBismutFreedTraceConnectionData.{u, v}
    actual reference
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      operatorFamily.operatorTrace.bismutFreedCoefficient parameter

namespace GeometricOperatorBismutFreedPathComparisonData

/-- Covariant derivative obtained by pulling back the geometric connection. -/
def geometricConnectionAt
    {actual reference : Real → E →L[Real] E}
    (data : GeometricOperatorBismutFreedPathComparisonData.{u, v, w, x}
      actual reference Base Tangent)
    (parameter : Real) (value derivative : Complex) : Complex :=
  derivative + pulledGeometricCoefficient data.geometry data.path parameter * value

/-- Once the one-form comparison is proved, the geometric pullback connection
is literally the intrinsic operator-trace connection. -/
theorem geometricConnectionAt_eq_operator
    {actual reference : Real → E →L[Real] E}
    (data : GeometricOperatorBismutFreedPathComparisonData.{u, v, w, x}
      actual reference Base Tangent)
    (parameter : Real) (value derivative : Complex) :
    data.geometricConnectionAt parameter value derivative =
      data.operatorFamily.connectionAt parameter value derivative := by
  unfold geometricConnectionAt
    P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D.RelativeBismutFreedTraceConnectionData.connectionAt
  rw [data.coefficient_agreement parameter]

/-- The intrinsic zeta determinant is therefore parallel for the pulled-back
geometric Bismut--Freed connection, not only for the operator presentation. -/
theorem determinant_parallel_geometric
    {actual reference : Real → E →L[Real] E}
    (data : GeometricOperatorBismutFreedPathComparisonData.{u, v, w, x}
      actual reference Base Tangent)
    (parameter : Real) :
    data.geometricConnectionAt parameter
        (relativeHeatMellinZetaFamilyDeterminant
          data.operatorFamily.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.operatorFamily.zetaFamily.toZetaFamily parameter) = 0 := by
  rw [data.geometricConnectionAt_eq_operator]
  exact data.operatorFamily.determinant_parallel parameter

/-- Public pathwise geometric/operator comparison checkpoint. -/
theorem geometric_operator_bismut_freed_path_comparison_gate
    {actual reference : Real → E →L[Real] E}
    (data : GeometricOperatorBismutFreedPathComparisonData.{u, v, w, x}
      actual reference Base Tangent) :
    ellipticFamilyInputClosed
        (toEllipticFamilyInputStatus data.analyticFamily) ∧
      quillenBismutFreedClosed data.quillen ∧
      (∀ parameter value derivative,
        data.geometricConnectionAt parameter value derivative =
          data.operatorFamily.connectionAt parameter value derivative) ∧
      (∀ parameter,
        data.geometricConnectionAt parameter
            (relativeHeatMellinZetaFamilyDeterminant
              data.operatorFamily.zetaFamily parameter)
            (relativeZetaDeterminantCoordinateDerivative
              data.operatorFamily.zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨data.analyticFamilyClosed,
    data.quillenClosed,
    data.geometricConnectionAt_eq_operator,
    data.determinant_parallel_geometric⟩

end GeometricOperatorBismutFreedPathComparisonData

end
end P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
end JanusFormal
