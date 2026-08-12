import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Mellin/zeta families anchored to one honest relative heat determinant

A parameter-dependent zeta connection must not be attached to a scalar
Candidate-A determinant merely by reusing the same notation.  This file records
an exact basepoint anchor between:

* one positive-time relative heat trace;
* one finite-part renormalization and its Mellin continuation;
* one differentiable Mellin/zeta family.

The family is required to use the same heat trace at parameter zero, the same
finite-part logarithm there and the same zeta derivative at zero.  Hence its
complex determinant coordinate and its positive metric magnitude agree with
the original scalar determinant at the basepoint.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaAnchoredFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaComparison4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- A differentiable Mellin family whose parameter-zero member is tied to one
specified relative heat determinant. -/
structure RelativeHeatMellinZetaAnchoredFamilyData
    {baseHeatTrace : HeatTime → Real}
    (baseFinitePart : RelativeHeatFinitePartData baseHeatTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart) where
  family : RelativeHeatMellinZetaFamilyData
  heatTrace_zero : family.finitePartFamily.heatTrace 0 = baseHeatTrace
  finitePart_log_zero :
    relativeHeatFinitePartLogDeterminant
        (family.finitePartFamily.finitePart 0) =
      relativeHeatFinitePartLogDeterminant baseFinitePart
  zeta_zero : (family.continuation 0).zeta = baseContinuation.zeta
  zetaPrime_zero :
    (family.continuation 0).derivativeAtZero =
      baseContinuation.derivativeAtZero

namespace RelativeHeatMellinZetaAnchoredFamilyData

/-- The complex family coordinate at parameter zero is exactly the scalar
Mellin/zeta determinant used to anchor the family. -/
theorem determinant_zero_eq_base
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    (data : RelativeHeatMellinZetaAnchoredFamilyData
      baseFinitePart baseContinuation) :
    relativeHeatMellinZetaFamilyDeterminant data.family 0 =
      relativeHeatMellinZetaDeterminant baseContinuation := by
  change
    Complex.exp (-(data.family.continuation 0).derivativeAtZero) =
      Complex.exp (-baseContinuation.derivativeAtZero)
  rw [data.zetaPrime_zero]

/-- The positive finite-part determinant of the family at zero is the original
scalar finite-part determinant. -/
theorem finitePartDeterminant_zero_eq_base
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    (data : RelativeHeatMellinZetaAnchoredFamilyData
      baseFinitePart baseContinuation) :
    relativeHeatFinitePartDeterminantFamily data.family.finitePartFamily 0 =
      relativeHeatFinitePartDeterminant baseFinitePart := by
  change
    Real.exp
        (relativeHeatFinitePartLogDeterminant
          (data.family.finitePartFamily.finitePart 0)) =
      Real.exp (relativeHeatFinitePartLogDeterminant baseFinitePart)
  rw [data.finitePart_log_zero]

/-- Basepoint norm equality, now simultaneously tied to the family coordinate
and to the original scalar heat renormalization. -/
theorem norm_determinant_zero_eq_base_finitePart
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    (data : RelativeHeatMellinZetaAnchoredFamilyData
      baseFinitePart baseContinuation) :
    ‖relativeHeatMellinZetaFamilyDeterminant data.family 0‖ =
      relativeHeatFinitePartDeterminant baseFinitePart := by
  rw [norm_relativeHeatMellinZetaFamilyDeterminant]
  exact data.finitePartDeterminant_zero_eq_base

/-- The scalar and family zeta functions are literally the same complex
function at the selected basepoint. -/
theorem zeta_zero_eq_base
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    (data : RelativeHeatMellinZetaAnchoredFamilyData
      baseFinitePart baseContinuation) :
    (data.family.continuation 0).zeta = baseContinuation.zeta :=
  data.zeta_zero

/-- Public anchored-family checkpoint. -/
theorem relative_heat_mellin_zeta_anchored_family_gate
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    (data : RelativeHeatMellinZetaAnchoredFamilyData
      baseFinitePart baseContinuation) :
    data.family.finitePartFamily.heatTrace 0 = baseHeatTrace ∧
      relativeHeatMellinZetaFamilyDeterminant data.family 0 =
        relativeHeatMellinZetaDeterminant baseContinuation ∧
      ‖relativeHeatMellinZetaFamilyDeterminant data.family 0‖ =
        relativeHeatFinitePartDeterminant baseFinitePart ∧
      (∀ parameter,
        relativeHeatFinitePartMetricWeightDerivative
            data.family.finitePartFamily parameter =
          -2 *
            (relativeZetaConnectionCoefficient
              data.family.toZetaFamily parameter).re *
            relativeHeatFinitePartMetricWeight
              data.family.finitePartFamily parameter) ∧
      (∀ parameter,
        ‖relativeZetaFinitePartPhase
          data.family.toFinitePartComparison parameter‖ = 1) :=
  ⟨data.heatTrace_zero,
    data.determinant_zero_eq_base,
    data.norm_determinant_zero_eq_base_finitePart,
    relativeHeatMellinZetaFamily_metricVariation data.family,
    relativeHeatMellinZetaFamily_phase_norm_one data.family⟩

end RelativeHeatMellinZetaAnchoredFamilyData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaAnchoredFamily4D
end JanusFormal
