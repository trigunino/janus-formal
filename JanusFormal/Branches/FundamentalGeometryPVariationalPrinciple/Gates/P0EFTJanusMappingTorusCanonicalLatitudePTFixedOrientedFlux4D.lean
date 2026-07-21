import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeOrientedFluxOddSymmetry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothPTFieldAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D

/-!
# PT-fixed scalar fields have zero oriented Green flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudeOrientedFluxOddSymmetry4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Fundamental-domain PT as a measurable involution. -/
def canonicalLatitudeBasePTMeasurableEquiv :
    CanonicalLatitudeBase ≃ᵐ CanonicalLatitudeBase where
  toFun := canonicalLatitudeBasePT period
  invFun := canonicalLatitudeBasePT period
  left_inv := canonicalLatitudeBasePT_involutive period
  right_inv := canonicalLatitudeBasePT_involutive period
  measurable_toFun := canonicalLatitudeBasePT_measurable period
  measurable_invFun := canonicalLatitudeBasePT_measurable period

/-- PT reverses the chosen normal coordinate after returning time to the
canonical fundamental domain. -/
theorem reflectedSpherePT_quotientNormalLatitude
    (base : CanonicalLatitudeBase) (normal : Real) :
    reflectedSpherePT period hPeriod
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal) =
      quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod
          (canonicalLatitudeBasePT period base)) (-normal) := by
  unfold reflectedSpherePT quotientNormalLatitude
  rw [mappingTorusTimeReversal_mk, mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨-1, ?_⟩
  apply MappingTorusCover.ext
  · rw [vadd_fiber]
    simp only [normalLatitudeCover, canonicalLatitudeAnchor,
      canonicalLatitudeBasePT]
    change sphereReflection.symm
        (equatorialLatitude
          (P0EFTJanusMappingTorusSmoothAtlasFrontier.equatorialTwoSphereHomeomorph.symm
            base.1) (-normal)) = _
    rw [sphereReflection_symm, sphereReflection_equatorialLatitude]
    simp
  · rw [vadd_time]
    change (period - base.2) + ((-1 : Int) : Real) * period = -base.2
    norm_num
    ring

theorem canonicalLatitudeValue_ptPullback
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeValue period hPeriod
        (ptPullback period hPeriod Real field) base normal =
      canonicalLatitudeValue period hPeriod field
        (canonicalLatitudeBasePT period base) (-normal) := by
  unfold canonicalLatitudeValue canonicalNormalSlice
  rw [ptPullback_apply, reflectedSpherePT_quotientNormalLatitude]

theorem canonicalLatitudeDerivative_ptPullback
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod
        (ptPullback period hPeriod Real field) base normal =
      -canonicalLatitudeDerivative period hPeriod field
        (canonicalLatitudeBasePT period base) (-normal) := by
  have hValue :
      canonicalLatitudeValue period hPeriod
          (ptPullback period hPeriod Real field) base =
        fun current => canonicalLatitudeValue period hPeriod field
          (canonicalLatitudeBasePT period base) (-current) := by
    funext current
    exact canonicalLatitudeValue_ptPullback period hPeriod field base current
  unfold canonicalLatitudeDerivative
  rw [hValue, deriv_comp_neg]

/-- Both fields lie in the same PT-even scalar sector. -/
def CanonicalLatitudeScalarPTFixed
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  ptPullback period hPeriod Real field = field

theorem canonicalLatitudeScalarGreenCurrent_basePT_eq_neg_of_ptFixed
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTest : CanonicalLatitudeScalarPTFixed period hPeriod test)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test
        (canonicalLatitudeBasePT period base) 0 =
      -canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  have hFieldValue := canonicalLatitudeValue_ptPullback
    period hPeriod field base 0
  have hTestValue := canonicalLatitudeValue_ptPullback
    period hPeriod test base 0
  have hFieldDerivative := canonicalLatitudeDerivative_ptPullback
    period hPeriod field base 0
  have hTestDerivative := canonicalLatitudeDerivative_ptPullback
    period hPeriod test base 0
  rw [hField] at hFieldValue hFieldDerivative
  rw [hTest] at hTestValue hTestDerivative
  simp only [neg_zero] at hFieldValue hTestValue hFieldDerivative hTestDerivative
  have hFieldDerivative' :
      canonicalLatitudeDerivative period hPeriod field
          (canonicalLatitudeBasePT period base) 0 =
        -canonicalLatitudeDerivative period hPeriod field base 0 := by
    linarith
  have hTestDerivative' :
      canonicalLatitudeDerivative period hPeriod test
          (canonicalLatitudeBasePT period base) 0 =
        -canonicalLatitudeDerivative period hPeriod test base 0 := by
    linarith
  unfold canonicalLatitudeScalarGreenCurrent
  rw [← hFieldValue, ← hTestValue, hFieldDerivative', hTestDerivative']
  ring

def ptFixedGreenCurrentOddSymmetry
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTest : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    CanonicalLatitudeGreenCurrentOddSymmetry period hPeriod field test where
  symmetry := canonicalLatitudeBasePTMeasurableEquiv period
  measurePreserving := canonicalLatitudeBasePT_measurePreserving period hPeriod
  current_odd :=
    canonicalLatitudeScalarGreenCurrent_basePT_eq_neg_of_ptFixed
      period hPeriod field test hField hTest

theorem twoSheetOrientedFlux_zero_of_ptFixed
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTest : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    twoSheetOrientedScalarCurrentIntegral period hPeriod field test = 0 :=
  twoSheetOrientedFlux_zero_of_oddSymmetry period hPeriod field test
    (ptFixedGreenCurrentOddSymmetry period hPeriod field test hField hTest)

theorem completeMetricStokes_of_euler_of_ptFixed
    (massSquared : Real) (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test :=
  completeMetricStokes_of_euler_of_oddSymmetry period hPeriod massSquared
    field test hFieldEuler hTestEuler
      (ptFixedGreenCurrentOddSymmetry period hPeriod field test hFieldPT hTestPT)

end
end P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
end JanusFormal
