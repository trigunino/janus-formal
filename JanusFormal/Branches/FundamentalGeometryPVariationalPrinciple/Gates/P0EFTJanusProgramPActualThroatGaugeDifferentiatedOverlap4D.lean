import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D

/-!
# Differentiated overlap congruence for the actual throat gauge covector

After transporting the first centered-frame representative by the exact dual
frame transition, it agrees with the second representative throughout their
common base set.  Their first manifold derivatives within that same overlap
therefore agree by congruence.

These statements do not expand a product rule for the varying transition and
do not provide base-chart jet descent, a gauge-transformation law, normal
geometry or a global Levi--Civita connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D

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

/-- Common base set of two centered throat tangent trivializations. -/
def throatGaugeCenteredTrivializationOverlap
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor).baseSet

/-! ## Transported representative -/

/-- The first centered-frame covector, transported into the second centered
frame by the actual contragredient tangent-trivialization transition. -/
def throatGaugeCovectorCoordinatesTransported
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    FramedCovector ThroatCoverCoordinates :=
  throatGaugeCovectorTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current
    (throatGaugeCovectorCoordinates period hPeriod potential component
      firstAnchor current)

/-- On the double overlap, the transported first-frame representative is
exactly the second-frame representative.  This is the underlying order-zero
identity used below. -/
theorem throatGaugeCovectorCoordinatesTransported_eq
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :
    throatGaugeCovectorCoordinatesTransported period hPeriod potential
        component firstAnchor secondAnchor current =
      throatGaugeCovectorCoordinates period hPeriod potential component
        secondAnchor current := by
  simpa only [throatGaugeCovectorCoordinatesTransported,
    throatGaugeCovectorTrivializationTransitionAt] using
    (throatGaugeCovectorCoordinates_eq_dual_transition
      period hPeriod potential component firstAnchor secondAnchor current
        hCurrent).symm

/-- Function-level form of the transported-representative equality on the
common trivialization overlap. -/
theorem throatGaugeCovectorCoordinatesTransported_eqOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    Set.EqOn
      (throatGaugeCovectorCoordinatesTransported period hPeriod potential
        component firstAnchor secondAnchor)
      (throatGaugeCovectorCoordinates period hPeriod potential component
        secondAnchor)
      (throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) := by
  intro current hCurrent
  exact throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
    component firstAnchor secondAnchor current hCurrent

/-- The transported representative is `C∞` within the double overlap.  The
proof uses its exact equality there with the smooth second-frame
representative; it asserts no explicit differentiated product formula. -/
theorem throatGaugeCovectorCoordinatesTransported_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates)) ∞
      (throatGaugeCovectorCoordinatesTransported period hPeriod potential
        component firstAnchor secondAnchor)
      (throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) := by
  have hEq := throatGaugeCovectorCoordinatesTransported_eqOn period hPeriod
    potential component firstAnchor secondAnchor
  apply
    (throatGaugeCovectorCoordinates_contMDiffOn_baseSet
      period hPeriod potential component secondAnchor).congr_mono
  · exact hEq
  · exact inter_subset_right

/-! ## Within-overlap derivative congruence -/

/-- The transported and second-frame representatives have exactly the same
candidate manifold derivatives within their overlap.  This is derivative
congruence, not an expanded transition/product-rule formula. -/
theorem throatGaugeCovectorCoordinatesTransported_hasMFDerivWithinAt_iff
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (derivative : ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates) :
    HasMFDerivWithinAt throatCoverModelWithCorners
        (modelWithCornersSelf Real (FramedCovector ThroatCoverCoordinates))
        (throatGaugeCovectorCoordinatesTransported period hPeriod potential
          component firstAnchor secondAnchor)
        (throatGaugeCenteredTrivializationOverlap period hPeriod
          firstAnchor secondAnchor) current derivative ↔
      HasMFDerivWithinAt throatCoverModelWithCorners
        (modelWithCornersSelf Real (FramedCovector ThroatCoverCoordinates))
        (throatGaugeCovectorCoordinates period hPeriod potential component
          secondAnchor)
        (throatGaugeCenteredTrivializationOverlap period hPeriod
          firstAnchor secondAnchor) current derivative := by
  have hEq := throatGaugeCovectorCoordinatesTransported_eqOn period hPeriod
    potential component firstAnchor secondAnchor
  constructor
  · intro hDerivative
    exact hDerivative.congr_mono
      (fun _ hPoint => (hEq hPoint).symm)
      (hEq hCurrent).symm (Subset.rfl)
  · intro hDerivative
    exact hDerivative.congr_mono
      (fun _ hPoint => hEq hPoint) (hEq hCurrent) (Subset.rfl)

end
end P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
end JanusFormal
