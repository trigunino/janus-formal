import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D

/-!
# The PT-even projector preserves the canonical latitude Euler equation
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjectionEuler4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem canonicalLatitudeSecondDerivative_ptPullback
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeSecondDerivative period hPeriod
        (ptPullback period hPeriod Real field) base normal =
      canonicalLatitudeSecondDerivative period hPeriod field
        (canonicalLatitudeBasePT period base) (-normal) := by
  have hDerivative :
      canonicalLatitudeDerivative period hPeriod
          (ptPullback period hPeriod Real field) base =
        fun current => -canonicalLatitudeDerivative period hPeriod field
          (canonicalLatitudeBasePT period base) (-current) := by
    funext current
    exact canonicalLatitudeDerivative_ptPullback
      period hPeriod field base current
  unfold canonicalLatitudeSecondDerivative
  rw [hDerivative]
  change deriv (-(fun current => canonicalLatitudeDerivative period hPeriod field
    (canonicalLatitudeBasePT period base) (-current))) normal = _
  rw [deriv.neg, deriv_comp_neg]
  ring

theorem canonicalLatitudeScalarEulerResidual_ptPullback
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarEulerResidual period hPeriod massSquared
        (ptPullback period hPeriod Real field) base normal =
      canonicalLatitudeScalarEulerResidual period hPeriod massSquared field
        (canonicalLatitudeBasePT period base) (-normal) := by
  unfold canonicalLatitudeScalarEulerResidual
  rw [canonicalLatitudeSecondDerivative_ptPullback,
    canonicalLatitudeValue_ptPullback]

theorem ptPullback_preserves_canonicalLatitudeScalarEulerSolution
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field) :
    CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      (ptPullback period hPeriod Real field) := by
  intro base normal
  rw [canonicalLatitudeScalarEulerResidual_ptPullback]
  exact hField (canonicalLatitudeBasePT period base) (-normal)

theorem canonicalLatitudeValue_ptEvenProjection
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeValue period hPeriod
        (canonicalScalarPTEvenProjection period hPeriod field) base normal =
      (1 / 2 : Real) *
        (canonicalLatitudeValue period hPeriod field base normal +
          canonicalLatitudeValue period hPeriod
            (ptPullback period hPeriod Real field) base normal) := by
  rfl

theorem canonicalLatitudeDerivative_ptEvenProjection
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod
        (canonicalScalarPTEvenProjection period hPeriod field) base normal =
      (1 / 2 : Real) *
        (canonicalLatitudeDerivative period hPeriod field base normal +
          canonicalLatitudeDerivative period hPeriod
            (ptPullback period hPeriod Real field) base normal) := by
  have hValue :
      canonicalLatitudeValue period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field) base =
        fun current => (1 / 2 : Real) *
          (canonicalLatitudeValue period hPeriod field base current +
            canonicalLatitudeValue period hPeriod
              (ptPullback period hPeriod Real field) base current) := by
    funext current
    exact canonicalLatitudeValue_ptEvenProjection
      period hPeriod field base current
  unfold canonicalLatitudeDerivative
  rw [hValue, deriv_const_mul_field]
  congr 1
  exact deriv_add
    (canonicalLatitudeValue_hasDerivAt period hPeriod field base normal).differentiableAt
    (canonicalLatitudeValue_hasDerivAt period hPeriod
      (ptPullback period hPeriod Real field) base normal).differentiableAt

theorem canonicalLatitudeSecondDerivative_ptEvenProjection
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeSecondDerivative period hPeriod
        (canonicalScalarPTEvenProjection period hPeriod field) base normal =
      (1 / 2 : Real) *
        (canonicalLatitudeSecondDerivative period hPeriod field base normal +
          canonicalLatitudeSecondDerivative period hPeriod
            (ptPullback period hPeriod Real field) base normal) := by
  have hDerivative :
      canonicalLatitudeDerivative period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field) base =
        fun current => (1 / 2 : Real) *
          (canonicalLatitudeDerivative period hPeriod field base current +
            canonicalLatitudeDerivative period hPeriod
              (ptPullback period hPeriod Real field) base current) := by
    funext current
    exact canonicalLatitudeDerivative_ptEvenProjection
      period hPeriod field base current
  unfold canonicalLatitudeSecondDerivative
  rw [hDerivative, deriv_const_mul_field]
  congr 1
  exact deriv_add
    (canonicalLatitudeDerivative_hasDerivAt period hPeriod field base normal).differentiableAt
    (canonicalLatitudeDerivative_hasDerivAt period hPeriod
      (ptPullback period hPeriod Real field) base normal).differentiableAt

theorem canonicalLatitudeScalarEulerResidual_ptEvenProjection
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarEulerResidual period hPeriod massSquared
        (canonicalScalarPTEvenProjection period hPeriod field) base normal =
      (1 / 2 : Real) *
        (canonicalLatitudeScalarEulerResidual period hPeriod massSquared
            field base normal +
          canonicalLatitudeScalarEulerResidual period hPeriod massSquared
            (ptPullback period hPeriod Real field) base normal) := by
  unfold canonicalLatitudeScalarEulerResidual
  rw [canonicalLatitudeSecondDerivative_ptEvenProjection,
    canonicalLatitudeValue_ptEvenProjection]
  ring

theorem canonicalScalarPTEvenProjection_preserves_euler
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field) :
    CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      (canonicalScalarPTEvenProjection period hPeriod field) := by
  have hPT := ptPullback_preserves_canonicalLatitudeScalarEulerSolution
    period hPeriod massSquared field hField
  intro base normal
  rw [canonicalLatitudeScalarEulerResidual_ptEvenProjection,
    hField base normal, hPT base normal]
  ring

theorem projectedCompleteMetricStokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) :=
  projectedCompleteMetricStokes_of_euler period hPeriod massSquared field test
    (canonicalScalarPTEvenProjection_preserves_euler
      period hPeriod massSquared field hField)
    (canonicalScalarPTEvenProjection_preserves_euler
      period hPeriod massSquared test hTest)

end
end P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjectionEuler4D
end JanusFormal
