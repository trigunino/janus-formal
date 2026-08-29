import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatDataTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

/-!
# Mellin zeta family transported by a unitary heat frame

A unitarily conjugated nuclear heat family has the same scalar heat trace at
every parameter.  Therefore one basepoint finite-part renormalization and one
basepoint Mellin continuation can be transported to every parameter through
literal equality of trace functions.

The resulting family satisfies

```text
FP_a = FP_0,
zeta'_a(0) = zeta'_0(0),
d/da zeta'_a(0) = 0,
D_zeta(a) = D_zeta(0).
```

No new short-time subtraction, long-time estimate, Mellin integral or analytic
continuation is required once the unitary heat conjugation has been certified.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPUnitaryConjugatedMellinZetaFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatDataTransport4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

end
end P0EFTJanusProgramPUnitaryConjugatedMellinZetaFamily4D

namespace P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatDataTransport4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaComparison4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

namespace UnitaryConjugatedNuclearTraceFamilyData

/-- Base heat trace equals the moving heat trace, in the direction needed for
dependent transport. -/
theorem baseTrace_eq_movingTrace
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (parameter : Real) :
    data.baseTrace = data.movingTrace parameter :=
  (data.movingTrace_eq_baseTrace_function parameter).symm

/-- Transport one basepoint finite-part packet to a current parameter. -/
def transportedFinitePart
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (parameter : Real) :
    RelativeHeatFinitePartData (data.movingTrace parameter) :=
  baseFinitePart.transportHeatTrace
    (data.baseTrace_eq_movingTrace parameter)

@[simp]
theorem transportedFinitePart_logDeterminant
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (parameter : Real) :
    relativeHeatFinitePartLogDeterminant
        (data.transportedFinitePart baseFinitePart parameter) =
      relativeHeatFinitePartLogDeterminant baseFinitePart :=
  baseFinitePart.transportHeatTrace_logDeterminant
    (data.baseTrace_eq_movingTrace parameter)

/-- The transported finite-part family is constant in its scalar logarithm. -/
def transportedFinitePartFamily
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace) :
    RelativeHeatFinitePartFamilyData where
  heatTrace := data.movingTrace
  finitePart := data.transportedFinitePart baseFinitePart
  logDerivative := fun _ => 0
  hasDerivAt_logDeterminant := by
    intro parameter
    have hConstant :
        HasDerivAt
          (fun _ : Real => relativeHeatFinitePartLogDeterminant baseFinitePart)
          0 parameter :=
      hasDerivAt_const parameter
        (relativeHeatFinitePartLogDeterminant baseFinitePart)
    convert hConstant using 1
    funext current
    exact data.transportedFinitePart_logDeterminant baseFinitePart current

/-- Transport the basepoint Mellin continuation to a current parameter. -/
def transportedContinuation
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (parameter : Real) :
    RelativeHeatMellinZetaContinuationData
      ((data.transportedFinitePartFamily baseFinitePart).finitePart parameter) :=
  baseContinuation.transportHeatTrace
    (data.baseTrace_eq_movingTrace parameter)

@[simp]
theorem transportedContinuation_derivativeAtZero
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (parameter : Real) :
    (data.transportedContinuation baseFinitePart baseContinuation parameter).derivativeAtZero =
      baseContinuation.derivativeAtZero :=
  baseContinuation.transportHeatTrace_derivativeAtZero
    (data.baseTrace_eq_movingTrace parameter)

/-- Complete Mellin zeta family transported from one basepoint continuation. -/
def transportedMellinZetaFamily
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart) :
    RelativeHeatMellinZetaFamilyData where
  finitePartFamily := data.transportedFinitePartFamily baseFinitePart
  continuation := data.transportedContinuation baseFinitePart baseContinuation
  parameterDerivative := fun _ => 0
  hasDerivAt_zetaPrime := by
    intro parameter
    have hConstant :
        HasDerivAt
          (fun _ : Real => baseContinuation.derivativeAtZero)
          0 parameter :=
      hasDerivAt_const parameter baseContinuation.derivativeAtZero
    convert hConstant using 1
    funext current
    exact data.transportedContinuation_derivativeAtZero baseFinitePart
      baseContinuation current
  connection_realPart := by
    intro parameter
    simp [transportedFinitePartFamily]

/-- The transported zeta-prime family is constant. -/
theorem transportedMellinZetaFamily_zetaPrimeAtZero
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (parameter : Real) :
    (data.transportedMellinZetaFamily baseFinitePart baseContinuation).zetaPrimeAtZero
      parameter = baseContinuation.derivativeAtZero :=
  data.transportedContinuation_derivativeAtZero baseFinitePart baseContinuation
    parameter

/-- Its determinant connection coefficient vanishes. -/
theorem transportedMellinZetaFamily_connectionCoefficient_zero
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (parameter : Real) :
    relativeZetaConnectionCoefficient
        (data.transportedMellinZetaFamily baseFinitePart baseContinuation).toZetaFamily
          parameter = 0 :=
  rfl

/-- The complex zeta determinant coordinate is constant and equals the
basepoint Mellin determinant. -/
theorem transportedMellinZetaFamily_determinant_eq_base
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (parameter : Real) :
    relativeHeatMellinZetaFamilyDeterminant
        (data.transportedMellinZetaFamily baseFinitePart baseContinuation)
        parameter =
      relativeHeatMellinZetaDeterminant baseContinuation := by
  unfold relativeHeatMellinZetaFamilyDeterminant
    relativeZetaDeterminantCoordinate
    relativeHeatMellinZetaDeterminant relativeZetaDeterminant
  change Complex.exp
      (-(data.transportedMellinZetaFamily baseFinitePart baseContinuation).zetaPrimeAtZero
        parameter) =
    Complex.exp (-baseContinuation.derivativeAtZero)
  rw [data.transportedMellinZetaFamily_zetaPrimeAtZero baseFinitePart
    baseContinuation parameter]

/-- Public unitary Mellin-zeta transport checkpoint. -/
theorem unitary_conjugated_mellin_zeta_family_gate
    (data : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (baseFinitePart : RelativeHeatFinitePartData data.baseTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart) :
    (∀ parameter,
      relativeHeatFinitePartLogDeterminant
          ((data.transportedMellinZetaFamily baseFinitePart baseContinuation).finitePartFamily.finitePart
            parameter) =
        relativeHeatFinitePartLogDeterminant baseFinitePart) ∧
    (∀ parameter,
      (data.transportedMellinZetaFamily baseFinitePart baseContinuation).zetaPrimeAtZero
        parameter = baseContinuation.derivativeAtZero) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          (data.transportedMellinZetaFamily baseFinitePart baseContinuation).toZetaFamily
            parameter = 0) ∧
    (∀ parameter,
      relativeHeatMellinZetaFamilyDeterminant
          (data.transportedMellinZetaFamily baseFinitePart baseContinuation)
          parameter = relativeHeatMellinZetaDeterminant baseContinuation) :=
  ⟨data.transportedFinitePart_logDeterminant baseFinitePart,
    data.transportedMellinZetaFamily_zetaPrimeAtZero baseFinitePart
      baseContinuation,
    data.transportedMellinZetaFamily_connectionCoefficient_zero baseFinitePart
      baseContinuation,
    data.transportedMellinZetaFamily_determinant_eq_base baseFinitePart
      baseContinuation⟩

end UnitaryConjugatedNuclearTraceFamilyData

end
end P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D
end JanusFormal
