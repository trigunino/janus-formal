import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNullExpansionCountertermNonDifferentiable

/-!
# Null-expansion counterterm Hessian on the regular strata

The existing first variation of `Theta * log (ell * |Theta|)` differentiates
once more on the exact open domain `Theta ≠ 0`.  Its scalar Hessian is the
symmetric form `(u, v) ↦ Theta⁻¹ * u * v`.  Multiplying by the already
declared fixed screen/gravitational coefficient gives the pointwise Hessian of
the actual ledger density.

This gate deliberately makes no claim across `Theta = 0`, where the existing
no-go excludes even a classical first derivative, and does not yet construct
the integrated null-hypersurface chart.
-/

namespace JanusFormal
namespace P0EFTJanusNullExpansionCountertermRegularStratumHessian

set_option autoImplicit false
noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNullExpansionCountertermVariation

theorem expansionCountertermDerivativeCoefficient_hasDerivAt
    (lengthScale expansion : Real)
    (hLength : 0 < lengthScale) (hExpansion : expansion ≠ 0) :
    HasDerivAt (expansionCountertermDerivativeCoefficient lengthScale)
      expansion⁻¹ expansion := by
  rcases lt_or_gt_of_ne hExpansion with hNegative | hPositive
  · have hAbs : HasDerivAt (fun x : Real => |x|) (-1) expansion :=
      hasDerivAt_abs_neg hNegative
    have hScaled : HasDerivAt (fun x : Real => lengthScale * |x|)
        (lengthScale * (-1)) expansion :=
      HasDerivAt.const_mul lengthScale hAbs
    have hArgument : lengthScale * |expansion| ≠ 0 :=
      mul_ne_zero hLength.ne' (abs_ne_zero.mpr hExpansion)
    have hLog := hScaled.log hArgument
    have hSum := hLog.add_const 1
    refine (hSum.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    · rw [abs_of_neg hNegative]
      field_simp [hLength.ne', hExpansion]
    · intro x
      rfl
  · have hAbs : HasDerivAt (fun x : Real => |x|) 1 expansion :=
      hasDerivAt_abs_pos hPositive
    have hScaled : HasDerivAt (fun x : Real => lengthScale * |x|)
        (lengthScale * 1) expansion :=
      HasDerivAt.const_mul lengthScale hAbs
    have hArgument : lengthScale * |expansion| ≠ 0 :=
      mul_ne_zero hLength.ne' (abs_ne_zero.mpr hExpansion)
    have hLog := hScaled.log hArgument
    have hSum := hLog.add_const 1
    refine (hSum.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    · rw [abs_of_pos hPositive]
      field_simp [hLength.ne', hExpansion]
    · intro x
      rfl

/-- Pointwise regular-stratum Hessian of the scalar null counterterm. -/
def expansionCountertermRegularHessian
    (expansion first second : Real) : Real :=
  expansion⁻¹ * first * second

theorem expansionCountertermRegularHessian_comm
    (expansion first second : Real) :
    expansionCountertermRegularHessian expansion first second =
      expansionCountertermRegularHessian expansion second first := by
  simp [expansionCountertermRegularHessian, mul_comm, mul_left_comm]

theorem expansionCountertermFirstVariation_hasDerivAt
    (lengthScale expansion first second : Real)
    (hLength : 0 < lengthScale) (hExpansion : expansion ≠ 0) :
    HasDerivAt
      (fun parameter =>
        first *
          expansionCountertermDerivativeCoefficient lengthScale
            (expansion + parameter * second))
      (expansionCountertermRegularHessian expansion first second)
      0 := by
  have hInner : HasDerivAt
      (fun parameter : Real => expansion + parameter * second)
      second 0 := by
    have hSum := (hasDerivAt_const (x := (0 : Real)) (c := expansion)).add
      ((hasDerivAt_id (0 : Real)).mul_const second)
    exact (hSum.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hComp : HasDerivAt
      (fun parameter : Real =>
        expansionCountertermDerivativeCoefficient lengthScale
          (expansion + parameter * second))
      (expansion⁻¹ * second) 0 := by
    have hOuter := expansionCountertermDerivativeCoefficient_hasDerivAt
      lengthScale expansion hLength hExpansion
    have hRaw := hOuter.comp_of_eq 0 hInner (by simp)
    simpa [Function.comp_def] using hRaw
  have hDerivative := hComp.const_mul first
  simpa [expansionCountertermRegularHessian, mul_assoc, mul_left_comm,
    mul_comm] using hDerivative

/-- Pointwise regular-stratum Hessian of the declared null counterterm
density, with screen measure and gravitational coefficient fixed. -/
def declaredNullCountertermRegularHessian
    (einsteinScale : Real) (data : NullBoundaryPointData)
    (expansion first second : Real) : Real :=
  fixedNullCountertermCoefficient einsteinScale data *
    expansionCountertermRegularHessian expansion first second

theorem declaredNullCountertermRegularHessian_comm
    (einsteinScale : Real) (data : NullBoundaryPointData)
    (expansion first second : Real) :
    declaredNullCountertermRegularHessian einsteinScale data
        expansion first second =
      declaredNullCountertermRegularHessian einsteinScale data
        expansion second first := by
  rw [declaredNullCountertermRegularHessian,
    declaredNullCountertermRegularHessian,
    expansionCountertermRegularHessian_comm]

theorem declaredNullCountertermFirstVariation_hasDerivAt
    (einsteinScale : Real) (data : NullBoundaryPointData)
    (expansion first second : Real) (hExpansion : expansion ≠ 0) :
    HasDerivAt
      (fun parameter =>
        fixedNullCountertermCoefficient einsteinScale data * first *
          expansionCountertermDerivativeCoefficient
            data.renormalizationLengthScale
            (expansion + parameter * second))
      (declaredNullCountertermRegularHessian einsteinScale data
        expansion first second)
      0 := by
  have hDerivative :=
    (expansionCountertermFirstVariation_hasDerivAt
      data.renormalizationLengthScale expansion first second
      data.renormalizationLengthScalePositive hExpansion).const_mul
        (fixedNullCountertermCoefficient einsteinScale data)
  simpa [declaredNullCountertermRegularHessian, mul_assoc] using hDerivative

end
end P0EFTJanusNullExpansionCountertermRegularStratumHessian
end JanusFormal
