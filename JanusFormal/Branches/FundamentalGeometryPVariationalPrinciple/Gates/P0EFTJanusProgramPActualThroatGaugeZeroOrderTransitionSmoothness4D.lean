import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D

/-!
# Smoothness of the zero-order actual throat tangent-frame transitions

For two fixed centered tangent trivializations, their model-fiber transition
and its inverse vary smoothly on the common base set when read as continuous
linear maps.

This is only regularity of an order-zero frame change.  No first- or
second-jet transition law, base-chart descent, gauge transformation, normal
geometry or global Levi--Civita connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Smooth model-fiber transitions -/

/-- With the two centered frames fixed, their actual tangent transition is
`C∞` on the overlap when coerced to a continuous linear map.  This does not
differentiate any extracted field or jet. -/
theorem throatGaugeTangentTrivializationTransitionAt_contMDiffOn
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real,
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod =>
        (throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  change ContMDiffOn throatCoverModelWithCorners
    𝓘(Real,
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
    (fun current : EffectiveThroat period hPeriod =>
      (firstTrivialization.coordChangeL Real secondTrivialization current :
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates))
    (firstTrivialization.baseSet ∩ secondTrivialization.baseSet)
  exact contMDiffOn_coordChangeL
    (IB := throatCoverModelWithCorners) (n := ∞)
      firstTrivialization secondTrivialization

/-- The inverse actual tangent transition is likewise `C∞` as a continuous
linear map on the same overlap.  This remains an order-zero frame-regularity
statement and supplies no jet overlap law. -/
theorem throatGaugeTangentTrivializationTransitionAt_symm_contMDiffOn
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real,
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod =>
        ((throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).symm :
            ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  change ContMDiffOn throatCoverModelWithCorners
    𝓘(Real,
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
    (fun current : EffectiveThroat period hPeriod =>
      ((firstTrivialization.coordChangeL Real secondTrivialization current).symm :
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates))
    (firstTrivialization.baseSet ∩ secondTrivialization.baseSet)
  exact contMDiffOn_symm_coordChangeL
    (IB := throatCoverModelWithCorners) (n := ∞)
      firstTrivialization secondTrivialization

end
end P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D
end JanusFormal
