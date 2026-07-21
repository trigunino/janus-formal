import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Canonical projection to the PT-fixed scalar sector
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Reynolds projector for the order-two PT action. -/
def canonicalScalarPTEvenProjection
    (field : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real :=
  (1 / 2 : Real) •
    (field + ptPullback period hPeriod Real field)

theorem canonicalScalarPTEvenProjection_ptFixed
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalLatitudeScalarPTFixed period hPeriod
      (canonicalScalarPTEvenProjection period hPeriod field) := by
  unfold CanonicalLatitudeScalarPTFixed canonicalScalarPTEvenProjection
  change (ptPullbackLinearMap period hPeriod Real)
      ((1 / 2 : Real) • (field + ptPullback period hPeriod Real field)) = _
  rw [map_smul, map_add]
  change (1 / 2 : Real) •
      (ptPullback period hPeriod Real field +
        ptPullback period hPeriod Real
          (ptPullback period hPeriod Real field)) =
    (1 / 2 : Real) • (field + ptPullback period hPeriod Real field)
  rw [ptPullback_involutive, add_comm]

theorem canonicalScalarPTEvenProjection_eq_self_of_ptFixed
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarPTFixed period hPeriod field) :
    canonicalScalarPTEvenProjection period hPeriod field = field := by
  unfold canonicalScalarPTEvenProjection
  rw [hField]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change (1 / 2 : Real) * (field point + field point) = field point
  ring

theorem canonicalScalarPTEvenProjection_eq_self_iff
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalScalarPTEvenProjection period hPeriod field = field ↔
      CanonicalLatitudeScalarPTFixed period hPeriod field := by
  constructor
  · intro hProjection
    have hFixed := canonicalScalarPTEvenProjection_ptFixed period hPeriod field
    unfold CanonicalLatitudeScalarPTFixed at hFixed ⊢
    rw [hProjection] at hFixed
    exact hFixed
  · exact canonicalScalarPTEvenProjection_eq_self_of_ptFixed
      period hPeriod field

theorem canonicalScalarPTEvenProjection_idempotent
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalScalarPTEvenProjection period hPeriod
        (canonicalScalarPTEvenProjection period hPeriod field) =
      canonicalScalarPTEvenProjection period hPeriod field :=
  canonicalScalarPTEvenProjection_eq_self_of_ptFixed period hPeriod _
    (canonicalScalarPTEvenProjection_ptFixed period hPeriod field)

theorem projectedTwoSheetOrientedFlux_eq_zero
    (field test : SmoothQuotientField period hPeriod Real) :
    twoSheetOrientedScalarCurrentIntegral period hPeriod
        (canonicalScalarPTEvenProjection period hPeriod field)
        (canonicalScalarPTEvenProjection period hPeriod test) = 0 :=
  twoSheetOrientedFlux_zero_of_ptFixed period hPeriod _ _
    (canonicalScalarPTEvenProjection_ptFixed period hPeriod field)
    (canonicalScalarPTEvenProjection_ptFixed period hPeriod test)

theorem projectedCompleteMetricStokes_of_euler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      (canonicalScalarPTEvenProjection period hPeriod field))
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      (canonicalScalarPTEvenProjection period hPeriod test)) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) :=
  completeMetricStokes_of_euler_of_ptFixed period hPeriod massSquared _ _
    hFieldEuler hTestEuler
    (canonicalScalarPTEvenProjection_ptFixed period hPeriod field)
    (canonicalScalarPTEvenProjection_ptFixed period hPeriod test)

end
end P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D
end JanusFormal
