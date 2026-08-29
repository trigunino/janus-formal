import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Third jet of a genuine holonomic atlas transition

Scalar-curvature transition requires differentiating the Levi--Civita
connection law.  The resulting third derivative of the coordinate transition
cancels after antisymmetrization.  This gate exposes that genuine third jet
and the exact symmetry responsible for the cancellation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- A genuine holonomic coordinate transition is `C³` at its selected
overlap point. -/
theorem holonomicCoordinateTransitionAt_contDiffAt_three
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    ContDiffAt Real 3
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint)
      firstCoordinate :=
  ((holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.contMDiffAt.contDiffAt).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)

/-- Third Fréchet derivative of the genuine coordinate transition.  The first
argument is the derivative direction of the Hessian-valued map; the last two
are the Hessian directions. -/
def holonomicCoordinateTransitionThirdDerivativeAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (firstVector secondVector thirdVector : Vector4) : Vector4 :=
  fderiv Real
      (fderiv Real
        (fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint)))
      firstCoordinate firstVector secondVector thirdVector

/-- The two outer directions of the transition third jet commute.  This is
the precise symmetry that removes the `D³` terms from the Riemann
antisymmetrization. -/
theorem holonomicCoordinateTransitionThirdDerivativeAt_swap_outer
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (firstVector secondVector thirdVector : Vector4) :
    holonomicCoordinateTransitionThirdDerivativeAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
        firstVector secondVector thirdVector =
      holonomicCoordinateTransitionThirdDerivativeAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
        secondVector firstVector thirdVector := by
  have hFirstDerivative :
      ContDiffAt Real 2
        (fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint))
        firstCoordinate :=
    (holonomicCoordinateTransitionAt_contDiffAt_three period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.fderiv_right (m := 2) (by norm_num)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq
      firstVector secondVector
  exact congrArg
    (fun derivative : Vector4 →L[Real] Vector4 =>
      derivative thirdVector) hSymmetric

end

end P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D
end JanusFormal
