import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D

/-! # Integrated oriented scalar current on the two cut-boundary sheets -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGaussianNormalEmbeddedHypersurface
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The deck-related second lift of the fundamental-domain boundary point. -/
def canonicalLatitudeCutBoundarySecondLift
    (base : CanonicalLatitudeBase) :=
  orientationDeck period hPeriod
    (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

def firstSheetOrientedScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  orientedCutLiftFlux .increasing
    (cutBoundaryScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base))

def secondSheetOrientedScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  orientedCutLiftFlux .decreasing
    (cutBoundaryScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBoundarySecondLift period hPeriod base))

theorem secondSheetOrientedScalarCurrent_eq_first
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    secondSheetOrientedScalarCurrent period hPeriod field test base =
      firstSheetOrientedScalarCurrent period hPeriod field test base := by
  rw [secondSheetOrientedScalarCurrent, firstSheetOrientedScalarCurrent,
    canonicalLatitudeCutBoundarySecondLift,
    cutBoundaryScalarCurrent_deck]
  exact orientedCutLiftFlux_opposite _

def firstSheetOrientedScalarCurrentIntegral
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base, firstSheetOrientedScalarCurrent period hPeriod field test base
    ∂canonicalLatitudeBaseMeasure period

def secondSheetOrientedScalarCurrentIntegral
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base, secondSheetOrientedScalarCurrent period hPeriod field test base
    ∂canonicalLatitudeBaseMeasure period

def twoSheetOrientedScalarCurrentIntegral
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  firstSheetOrientedScalarCurrentIntegral period hPeriod field test +
    secondSheetOrientedScalarCurrentIntegral period hPeriod field test

theorem secondSheetOrientedScalarCurrentIntegral_eq_first
    (field test : SmoothQuotientField period hPeriod Real) :
    secondSheetOrientedScalarCurrentIntegral period hPeriod field test =
      firstSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  unfold secondSheetOrientedScalarCurrentIntegral
    firstSheetOrientedScalarCurrentIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    secondSheetOrientedScalarCurrent_eq_first period hPeriod field test base

theorem twoSheetOrientedScalarCurrentIntegral_eq_two_mul_first
    (field test : SmoothQuotientField period hPeriod Real) :
    twoSheetOrientedScalarCurrentIntegral period hPeriod field test =
      2 * firstSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [twoSheetOrientedScalarCurrentIntegral,
    secondSheetOrientedScalarCurrentIntegral_eq_first]
  ring

theorem firstSheetOrientedScalarCurrentIntegral_eq_current
    (field test : SmoothQuotientField period hPeriod Real) :
    firstSheetOrientedScalarCurrentIntegral period hPeriod field test =
      ∫ base, cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  unfold firstSheetOrientedScalarCurrentIntegral
    firstSheetOrientedScalarCurrent orientedCutLiftFlux
  simp [NormalOrientation.sign]

/-- Exact two-sheet oriented form of the half-collar FTC identity. -/
theorem two_mul_productHalfCollarIntegral_eq_neg_twoSheetOrientedCurrent
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * (∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂canonicalLatitudeBaseMeasure period) =
      -twoSheetOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [productHalfCollarIntegral_eq_neg_firstSheetBoundaryCurrent,
    twoSheetOrientedScalarCurrentIntegral_eq_two_mul_first,
    firstSheetOrientedScalarCurrentIntegral_eq_current]
  ring

end
end P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
end JanusFormal
