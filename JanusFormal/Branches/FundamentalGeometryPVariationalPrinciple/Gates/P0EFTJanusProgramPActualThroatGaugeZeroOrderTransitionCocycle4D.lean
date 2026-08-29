import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D

/-!
# Zero-order cocycle for the actual throat tangent-frame transitions

The tangent-trivialization transition already used by the actual throat gauge
covector satisfies its identity, inverse and triple-overlap laws.  Its
contragredient action on model covectors consequently satisfies the same
triple-overlap cocycle.

These are only algebraic fiber/frame laws of order zero.  No first- or
second-jet overlap, base-chart descent, `U(1)^2` gauge transformation, normal
geometry or global Levi--Civita connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D

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

/-! ## The dual transition -/

/-- Contragredient action of the actual tangent-frame transition on model
covectors.  This is a change of tangent trivialization, not a gauge
transformation. -/
def throatGaugeCovectorTrivializationTransitionAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    FramedCovector ThroatCoverCoordinates ≃L[Real]
      FramedCovector ThroatCoverCoordinates :=
  (throatGaugeTangentTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current).arrowCongr
    (ContinuousLinearEquiv.refl Real Real)

/-! ## Tangent-frame groupoid laws -/

/-- On its base set, the transition from a centered tangent trivialization to
itself is the identity.  This is only an order-zero fiber statement. -/
theorem throatGaugeTangentTrivializationTransitionAt_self
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) :
    throatGaugeTangentTrivializationTransitionAt period hPeriod
        anchor anchor current =
      ContinuousLinearEquiv.refl Real ThroatCoverCoordinates := by
  let trivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor
  change current ∈ trivialization.baseSet at hCurrent
  change trivialization.coordChangeL Real trivialization current = _
  rw [← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
    (R := Real) trivialization trivialization ⟨hCurrent, hCurrent⟩]
  simp

/-- Reversing two centered tangent trivializations gives exactly the inverse
transition on their common base set.  No chart or jet law is inferred. -/
theorem throatGaugeTangentTrivializationTransitionAt_symm
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :
    (throatGaugeTangentTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current).symm =
      throatGaugeTangentTrivializationTransitionAt period hPeriod
        secondAnchor firstAnchor current := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  change current ∈
    firstTrivialization.baseSet ∩ secondTrivialization.baseSet at hCurrent
  change
    (firstTrivialization.coordChangeL Real secondTrivialization current).symm =
      secondTrivialization.coordChangeL Real firstTrivialization current
  exact Bundle.Trivialization.symm_coordChangeL
    firstTrivialization secondTrivialization ⟨hCurrent.2, hCurrent.1⟩

/-- The actual tangent-frame transitions compose on every triple overlap.
This is the exact order-zero Cech cocycle in the model tangent fiber. -/
theorem throatGaugeTangentTrivializationTransitionAt_cocycle
    (firstAnchor secondAnchor thirdAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) secondAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) thirdAnchor).baseSet)) :
    (throatGaugeTangentTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current).trans
      (throatGaugeTangentTrivializationTransitionAt period hPeriod
        secondAnchor thirdAnchor current) =
      throatGaugeTangentTrivializationTransitionAt period hPeriod
        firstAnchor thirdAnchor current := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  let thirdTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) thirdAnchor
  change current ∈
    firstTrivialization.baseSet ∩
      (secondTrivialization.baseSet ∩ thirdTrivialization.baseSet) at hCurrent
  change
    (firstTrivialization.coordChangeL Real secondTrivialization current).trans
        (secondTrivialization.coordChangeL Real thirdTrivialization current) =
      firstTrivialization.coordChangeL Real thirdTrivialization current
  rw [← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := Real) firstTrivialization secondTrivialization
        ⟨hCurrent.1, hCurrent.2.1⟩,
    ← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := Real) secondTrivialization thirdTrivialization
        ⟨hCurrent.2.1, hCurrent.2.2⟩,
    ← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := Real) firstTrivialization thirdTrivialization
        ⟨hCurrent.1, hCurrent.2.2⟩]
  let firstEquiv :=
    firstTrivialization.continuousLinearEquivAt Real current hCurrent.1
  let secondEquiv :=
    secondTrivialization.continuousLinearEquivAt Real current hCurrent.2.1
  let thirdEquiv :=
    thirdTrivialization.continuousLinearEquivAt Real current hCurrent.2.2
  change
    (firstEquiv.symm.trans secondEquiv).trans
        (secondEquiv.symm.trans thirdEquiv) =
      firstEquiv.symm.trans thirdEquiv
  apply ContinuousLinearEquiv.ext
  funext vector
  simp only [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-! ## Dual cocycle -/

/-- The contragredient covector transitions compose in the same order on a
triple overlap.  The inverse required for covariance is already built into
`arrowCongr`; this proves no higher-order jet or gauge cocycle. -/
theorem throatGaugeCovectorTrivializationTransitionAt_cocycle
    (firstAnchor secondAnchor thirdAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) secondAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) thirdAnchor).baseSet)) :
    (throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current).trans
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
        secondAnchor thirdAnchor current) =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor thirdAnchor current := by
  have hTangent := throatGaugeTangentTrivializationTransitionAt_cocycle
    period hPeriod firstAnchor secondAnchor thirdAnchor current hCurrent
  apply ContinuousLinearEquiv.ext
  funext covector
  apply ContinuousLinearMap.ext
  intro vector
  simp only [throatGaugeCovectorTrivializationTransitionAt,
    ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.refl_apply]
  rw [← hTangent]
  simp

end
end P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
end JanusFormal
