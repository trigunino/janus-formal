import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLedger
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Null-expansion counterterm variation

For a fixed positive length scale `ℓ`, this gate differentiates the scalar
factor `θ ↦ θ log (ℓ |θ|)` at every `θ ≠ 0`.  It then lifts the result to the
already-declared null counterterm density while keeping the screen measure,
orientation sign and Einstein coefficient fixed.

The derivative coefficient is unbounded below along an explicit positive path
approaching zero.  Thus the stationary continuous extension is not covered by
the nonzero-expansion derivative formula.  No integrated generator
reparametrization invariance or Einstein--Hilbert flux cancellation is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusNullExpansionCountertermVariation

set_option autoImplicit false

noncomputable section

open Filter
open P0EFTJanusExplicitBoundaryDensityLedger

/-- Unextended scalar factor.  Lean's totalized logarithm makes its value at
zero equal to the ledger's explicitly declared continuous extension. -/
def expansionCountertermFactor (lengthScale expansion : ℝ) : ℝ :=
  expansion * Real.log (lengthScale * |expansion|)

/-- Coefficient appearing in the derivative away from zero expansion. -/
def expansionCountertermDerivativeCoefficient
    (lengthScale expansion : ℝ) : ℝ :=
  Real.log (lengthScale * |expansion|) + 1

/-- Actual one-variable derivative of `θ log (ℓ |θ|)` for `ℓ > 0`, `θ ≠ 0`. -/
theorem expansionCountertermFactor_hasDerivAt
    (lengthScale expansion : ℝ)
    (hLength : 0 < lengthScale) (hExpansion : expansion ≠ 0) :
    HasDerivAt (expansionCountertermFactor lengthScale)
      (expansionCountertermDerivativeCoefficient lengthScale expansion)
      expansion := by
  rcases lt_or_gt_of_ne hExpansion with hNegative | hPositive
  · have hAbs : HasDerivAt (fun x : ℝ => |x|) (-1) expansion :=
      hasDerivAt_abs_neg hNegative
    have hScaled :
        HasDerivAt (fun x : ℝ => lengthScale * |x|)
          (lengthScale * (-1)) expansion :=
      HasDerivAt.const_mul lengthScale hAbs
    have hArgument : lengthScale * |expansion| ≠ 0 :=
      mul_ne_zero hLength.ne' (abs_ne_zero.mpr hExpansion)
    have hProduct := (hasDerivAt_id expansion).mul (hScaled.log hArgument)
    have hAlgebra :
        1 * Real.log (lengthScale * |expansion|) +
            expansion * (lengthScale * (-1) /
              (lengthScale * |expansion|)) =
          Real.log (lengthScale * |expansion|) + 1 := by
      rw [abs_of_neg hNegative]
      field_simp [hLength.ne', hExpansion]
    simp only [id_eq] at hProduct
    rw [hAlgebra] at hProduct
    have hFunction :
        (id * fun y : ℝ => Real.log (lengthScale * |y|)) =
          expansionCountertermFactor lengthScale := by
      funext y
      simp [expansionCountertermFactor]
    rw [hFunction] at hProduct
    simpa [expansionCountertermDerivativeCoefficient] using hProduct
  · have hAbs : HasDerivAt (fun x : ℝ => |x|) 1 expansion :=
      hasDerivAt_abs_pos hPositive
    have hScaled :
        HasDerivAt (fun x : ℝ => lengthScale * |x|)
          (lengthScale * 1) expansion :=
      HasDerivAt.const_mul lengthScale hAbs
    have hArgument : lengthScale * |expansion| ≠ 0 :=
      mul_ne_zero hLength.ne' (abs_ne_zero.mpr hExpansion)
    have hProduct := (hasDerivAt_id expansion).mul (hScaled.log hArgument)
    have hAlgebra :
        1 * Real.log (lengthScale * |expansion|) +
            expansion * (lengthScale * 1 /
              (lengthScale * |expansion|)) =
          Real.log (lengthScale * |expansion|) + 1 := by
      rw [abs_of_pos hPositive]
      field_simp [hLength.ne', hExpansion]
    simp only [id_eq] at hProduct
    rw [hAlgebra] at hProduct
    have hFunction :
        (id * fun y : ℝ => Real.log (lengthScale * |y|)) =
          expansionCountertermFactor lengthScale := by
      funext y
      simp [expansionCountertermFactor]
    rw [hFunction] at hProduct
    simpa [expansionCountertermDerivativeCoefficient] using hProduct

/-- Vary only the null expansion; all other boundary data remain fixed. -/
def varyNullExpansion (data : NullBoundaryPointData) (expansion : ℝ) :
    NullBoundaryPointData :=
  { data with expansion := expansion }

/-- The ledger's fixed screen-measure and gravitational coefficient. -/
def fixedNullCountertermCoefficient
    (einsteinScale : ℝ) (data : NullBoundaryPointData) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.screenMetric|

/-- Declared ledger density, regarded as a one-variable expansion family. -/
def declaredNullCountertermExpansionFamily
    (einsteinScale : ℝ) (data : NullBoundaryPointData) (expansion : ℝ) : ℝ :=
  nullReparametrizationCountertermDensity einsteinScale
    (varyNullExpansion data expansion)

theorem varying_expansionLogFactor_eq
    (data : NullBoundaryPointData) (expansion : ℝ) :
    expansionLogFactor (varyNullExpansion data expansion) =
      expansionCountertermFactor data.renormalizationLengthScale expansion := by
  by_cases hExpansion : expansion = 0
  · simp [expansionLogFactor, expansionCountertermFactor,
      varyNullExpansion, hExpansion]
  · simp [expansionLogFactor, expansionCountertermFactor,
      varyNullExpansion, hExpansion]

/-- Exact pointwise identification with a fixed coefficient times the scalar
factor; no measure variation is hidden in this family. -/
theorem declaredNullCountertermExpansionFamily_eq
    (einsteinScale : ℝ) (data : NullBoundaryPointData) :
    declaredNullCountertermExpansionFamily einsteinScale data =
      fun expansion => fixedNullCountertermCoefficient einsteinScale data *
        expansionCountertermFactor data.renormalizationLengthScale expansion := by
  funext expansion
  simp only [declaredNullCountertermExpansionFamily,
    nullReparametrizationCountertermDensity,
    fixedNullCountertermCoefficient]
  rw [varying_expansionLogFactor_eq]
  simp [varyNullExpansion]

/-- Actual derivative of the declared density when only expansion varies. -/
theorem declaredNullCountertermExpansionFamily_hasDerivAt
    (einsteinScale : ℝ) (data : NullBoundaryPointData)
    (expansion : ℝ) (hExpansion : expansion ≠ 0) :
    HasDerivAt (declaredNullCountertermExpansionFamily einsteinScale data)
      (fixedNullCountertermCoefficient einsteinScale data *
        expansionCountertermDerivativeCoefficient
          data.renormalizationLengthScale expansion)
      expansion := by
  rw [declaredNullCountertermExpansionFamily_eq]
  exact HasDerivAt.const_mul (fixedNullCountertermCoefficient einsteinScale data)
    (expansionCountertermFactor_hasDerivAt
      data.renormalizationLengthScale expansion
      data.renormalizationLengthScalePositive hExpansion)

/-- Explicit positive path approaching zero expansion. -/
def zeroExpansionApproach (lengthScale parameter : ℝ) : ℝ :=
  Real.exp (-parameter) / lengthScale

theorem zeroExpansionApproach_pos
    (lengthScale parameter : ℝ) (hLength : 0 < lengthScale) :
    0 < zeroExpansionApproach lengthScale parameter := by
  exact div_pos (Real.exp_pos _) hLength

/-- The path really approaches the stationary section. -/
theorem zeroExpansionApproach_tendsto_zero
    (lengthScale : ℝ) :
    Tendsto (zeroExpansionApproach lengthScale) atTop (nhds 0) := by
  change Tendsto (fun parameter : ℝ => Real.exp (-parameter) / lengthScale)
    atTop (nhds 0)
  simpa using
    Real.tendsto_exp_neg_atTop_nhds_zero.div_const lengthScale

/-- Along the zero-approach path the derivative coefficient is exactly
`1 - parameter`. -/
theorem derivativeCoefficient_zeroExpansionApproach
    (lengthScale parameter : ℝ) (hLength : 0 < lengthScale) :
    expansionCountertermDerivativeCoefficient lengthScale
        (zeroExpansionApproach lengthScale parameter) = 1 - parameter := by
  have hPath := zeroExpansionApproach_pos lengthScale parameter hLength
  rw [expansionCountertermDerivativeCoefficient, abs_of_pos hPath]
  have hLengthNe : lengthScale ≠ 0 := hLength.ne'
  rw [zeroExpansionApproach]
  field_simp [hLengthNe]
  rw [Real.log_exp]
  ring

/-- Precise zero-expansion obstruction: arbitrarily far along a path that
converges to zero, the nonzero-expansion derivative coefficient lies below any
prescribed real bound. -/
theorem derivativeCoefficient_unbounded_below_along_zeroExpansionApproach
    (lengthScale : ℝ) (hLength : 0 < lengthScale)
    (bound after : ℝ) :
    ∃ parameter ≥ after,
      expansionCountertermDerivativeCoefficient lengthScale
          (zeroExpansionApproach lengthScale parameter) < bound := by
  let parameter := max after (2 - bound)
  refine ⟨parameter, le_max_left _ _, ?_⟩
  rw [derivativeCoefficient_zeroExpansionApproach lengthScale parameter hLength]
  have hParameter : 2 - bound ≤ parameter := le_max_right _ _
  linarith

end

end P0EFTJanusNullExpansionCountertermVariation
end JanusFormal
