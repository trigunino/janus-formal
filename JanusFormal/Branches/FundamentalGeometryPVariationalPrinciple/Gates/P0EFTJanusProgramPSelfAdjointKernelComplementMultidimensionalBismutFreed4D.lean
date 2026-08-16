import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultidimensionalBismutFreedPathExtension4D

/-!
# Multidimensional extension of the genuine actual-kernel BF family

The preferred one-parameter BF packet is already built from the genuine spaces
`(ker H_a)ᗮ`, transported to the fixed base complement.  This file does not
replace that construction.  It asks for a multidimensional extension of its
literal reduced actual/reference pair and requires the path trace in the new
extension to be exactly the already constructed intrinsic relative trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementMultidimensionalBismutFreed4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPMultidimensionalBismutFreedPathExtension4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

private abbrev BaseReduced
    (actual : Real → E →L[Real] E) :=
  SelfAdjointKernelComplement (actual 0)

/-- A genuine multidimensional extension of one already constructed
actual-kernel BF family. -/
structure SelfAdjointKernelComplementMultidimensionalBismutFreedData
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (Base : Type*) [NormedAddCommGroup Base] [NormedSpace Real Base] where
  baseActual : Base → BaseReduced actual →L[Real] BaseReduced actual
  baseReference : Base → BaseReduced actual →L[Real] BaseReduced actual
  extension : MultidimensionalBismutFreedPathExtensionData
    pathFamily.actualGap.fixedOperator reference baseActual baseReference
  pathTrace_eq : extension.pathTrace = pathFamily.relativeTrace

namespace SelfAdjointKernelComplementMultidimensionalBismutFreedData

/-- The geometric multidimensional one-form restricts to the exact established
operator-trace BF coefficient of the genuine kernel-complement family. -/
theorem geometric_path_coefficient_eq_existing
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (data : SelfAdjointKernelComplementMultidimensionalBismutFreedData
      pathFamily Base)
    (parameter : Real) :
    pulledLinearGeometricCoefficient
        data.extension.differential.comparison.geometric.geometry
        data.extension.path parameter =
      pathFamily.toBismutFreed.operatorTrace.bismutFreedCoefficient parameter := by
  rw [data.extension.geometric_path_coefficient_eq_existing]
  rw [data.pathTrace_eq]
  rfl

/-- The multidimensional actual operator is literally an extension of the
already transported genuine reduced family. -/
theorem baseActual_on_path
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (data : SelfAdjointKernelComplementMultidimensionalBismutFreedData
      pathFamily Base)
    (parameter : Real) :
    data.baseActual (data.extension.path.point parameter) =
      pathFamily.actualGap.fixedOperator parameter :=
  data.extension.actual_operator_restriction parameter

/-- Same exact path restriction for the reference operator. -/
theorem baseReference_on_path
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (data : SelfAdjointKernelComplementMultidimensionalBismutFreedData
      pathFamily Base)
    (parameter : Real) :
    data.baseReference (data.extension.path.point parameter) = reference parameter :=
  data.extension.reference_operator_restriction parameter

/-- The local families-index two-form equals the operator-trace curvature of
this same multidimensional extension. -/
theorem localIndex_eq_operatorTraceCurvature
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (data : SelfAdjointKernelComplementMultidimensionalBismutFreedData
      pathFamily Base)
    (base first second : Base) :
    data.extension.differential.localIndex.twoForm base first second =
      ((data.extension.differential.comparison.operator.bismutFreedTraceCurvature
        base first second : Real) : Complex) :=
  data.extension.localIndex_eq_operatorTraceCurvature base first second

/-- Public genuine-kernel multidimensional BF checkpoint. -/
theorem self_adjoint_kernel_complement_multidimensional_bismut_freed_gate
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (pathFamily : SelfAdjointKernelComplementBismutFreedFamilyData
      actual reference)
    (data : SelfAdjointKernelComplementMultidimensionalBismutFreedData
      pathFamily Base) :
    (∀ parameter,
      data.baseActual (data.extension.path.point parameter) =
        pathFamily.actualGap.fixedOperator parameter) ∧
    (∀ parameter,
      data.baseReference (data.extension.path.point parameter) =
        reference parameter) ∧
    (∀ parameter,
      pulledLinearGeometricCoefficient
          data.extension.differential.comparison.geometric.geometry
          data.extension.path parameter =
        pathFamily.toBismutFreed.operatorTrace.bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      data.extension.differential.localIndex.twoForm base first second =
        ((data.extension.differential.comparison.operator.bismutFreedTraceCurvature
          base first second : Real) : Complex)) :=
  ⟨data.baseActual_on_path pathFamily,
    data.baseReference_on_path pathFamily,
    data.geometric_path_coefficient_eq_existing pathFamily,
    data.localIndex_eq_operatorTraceCurvature pathFamily⟩

end SelfAdjointKernelComplementMultidimensionalBismutFreedData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementMultidimensionalBismutFreed4D
end JanusFormal
