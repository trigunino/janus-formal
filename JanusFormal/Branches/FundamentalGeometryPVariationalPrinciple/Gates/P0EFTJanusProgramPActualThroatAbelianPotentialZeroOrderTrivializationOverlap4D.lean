import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D

/-!
# Zero-order tangent-frame overlap for the actual throat gauge covector

The reconstructed throat gauge covector obeys the exact dual transition law
between two centered tangent trivializations at every common point of their
base sets.  This is only a fiber/frame overlap statement of order zero.

No first- or second-jet overlap law, base-chart transition law, global descent,
or `U(1)^2` gauge-transformation law is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D

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

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-! ## Actual tangent-frame transition -/

/-- The genuine model-fiber transition from the tangent trivialization
centered at `firstAnchor` to the one centered at `secondAnchor`, evaluated at
the same throat point.  This is a tangent-frame transition, not a gauge
transformation. -/
def throatGaugeTangentTrivializationTransitionAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor).coordChangeL Real
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor) current

/-! ## Zero-order overlap law -/

/-- On a common trivialization domain, evaluating the second-frame covector
on the transitioned vector gives the first-frame value.  This is only the
order-zero fiber law; it asserts no jet, base-chart, or gauge-change law. -/
theorem throatGaugeCovectorCoordinates_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (vector : ThroatCoverCoordinates) :
    throatGaugeCovectorCoordinates period hPeriod potential component
        secondAnchor current
        (throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current vector) =
      throatGaugeCovectorCoordinates period hPeriod potential component
        firstAnchor current vector := by
  rw [throatGaugeCovectorCoordinates_eq_trivializedPullback
      period hPeriod potential component secondAnchor current hCurrent.2,
    throatGaugeCovectorCoordinates_eq_trivializedPullback
      period hPeriod potential component firstAnchor current hCurrent.1]
  simp only [ContinuousLinearMap.comp_apply]
  unfold throatGaugeTangentTrivializationTransitionAt
  rw [← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
    (R := Real) _ _ hCurrent]
  let firstEquiv :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor).continuousLinearEquivAt
        Real current hCurrent.1
  let secondEquiv :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor).continuousLinearEquivAt
        Real current hCurrent.2
  change potential.toFun component current
      (secondEquiv.symm (secondEquiv (firstEquiv.symm vector))) =
    potential.toFun component current (firstEquiv.symm vector)
  rw [secondEquiv.symm_apply_apply]

/-- Equivalently, changing tangent frames acts on the reconstructed covector
by the contragredient `arrowCongr` action.  This remains an order-zero frame
overlap statement, with no jet, base-chart, or gauge-transformation content. -/
theorem throatGaugeCovectorCoordinates_eq_dual_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :
    throatGaugeCovectorCoordinates period hPeriod potential component
        secondAnchor current =
      (throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).arrowCongr
        (ContinuousLinearEquiv.refl Real Real)
        (throatGaugeCovectorCoordinates period hPeriod potential component
          firstAnchor current) := by
  apply ContinuousLinearMap.ext
  intro vector
  simp only [ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.refl_apply]
  have hApply := throatGaugeCovectorCoordinates_transition_apply
    period hPeriod potential component firstAnchor secondAnchor current
      hCurrent
      ((throatGaugeTangentTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current).symm vector)
  simpa using hApply

/-- The two actual Candidate-A throat potentials satisfy the same exact
zero-order dual frame-overlap law.  No overlap law for their extracted jets,
base charts, or `U(1)^2` gauge transformations is inferred. -/
theorem globalCandidateAThroatGaugeCovectorCoordinates_eq_dual_transition
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :
    throatGaugeCovectorCoordinates period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component secondAnchor current =
      (throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).arrowCongr
        (ContinuousLinearEquiv.refl Real Real)
        (throatGaugeCovectorCoordinates period hPeriod
          (globalCandidateAThroatPotentialBySector period hPeriod data sector)
          component firstAnchor current) :=
  throatGaugeCovectorCoordinates_eq_dual_transition
    period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component firstAnchor secondAnchor current hCurrent

end
end P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D
end JanusFormal
