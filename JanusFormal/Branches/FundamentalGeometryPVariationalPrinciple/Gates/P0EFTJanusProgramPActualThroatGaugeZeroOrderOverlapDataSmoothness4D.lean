import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D

/-!
# Smooth zero-order overlap data for the actual throat gauge covector

The local frame coefficients and their reconstructed model covector are smooth
throughout the centered tangent-trivialization base set.  On a double overlap,
the corresponding contragredient frame action is also smooth when read as a
continuous linear map on model covectors.

These are prerequisites for differentiating the zero-order overlap identity.
No first- or second-jet overlap law, base-chart descent, gauge transformation,
normal geometry or global Levi--Civita connection is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D

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
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D

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

/-! ## Smooth reconstructed local representatives -/

/-- Each actual local-frame coefficient is `C∞` on the whole base set of
the tangent trivialization centered at `anchor`, not only at its center. -/
theorem throatGaugeLocalCoefficient_contMDiffOn_baseSet
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod)
    (index : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (throatGaugeLocalCoefficient period hPeriod potential component anchor
        index)
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) := by
  let trivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor
  have hFrame :=
    trivialization.contMDiffOn_localFrame_baseSet
      (I := throatCoverModelWithCorners) (n := ∞)
      throatRadialReferenceBasis index
  have hSmooth :=
    (potential.contMDiff_eval component).comp_contMDiffOn hFrame
  exact hSmooth.congr fun current _ => rfl

/-- The finite coefficient expansion defining the model covector is `C∞`
on the whole centered trivialization base set.  This is still an order-zero
local representative, not a jet-overlap theorem. -/
theorem throatGaugeCovectorCoordinates_contMDiffOn_baseSet
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates)) ∞
      (throatGaugeCovectorCoordinates period hPeriod potential component
        anchor)
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) := by
  letI : IsBoundedSMul Real (FramedCovector ThroatCoverCoordinates) :=
    { dist_smul_pair' := fun scalar left right => by
        simp only [dist_eq_norm]
        rw [show scalar • left - scalar • right =
          scalar • (left - right) by exact (smul_sub scalar left right).symm]
        simpa using
          ContinuousLinearMap.opNorm_smul_le scalar (left - right)
      dist_pair_smul' := fun left right covector => by
        simp only [dist_eq_norm]
        rw [show left • covector - right • covector =
          (left - right) • covector by exact (sub_smul left right covector).symm]
        simpa using
          ContinuousLinearMap.opNorm_smul_le (left - right) covector }
  unfold throatGaugeCovectorCoordinates
  intro current hCurrent
  apply ContMDiffWithinAt.sum
  intro index _
  exact
    ((throatGaugeLocalCoefficient_contMDiffOn_baseSet
      period hPeriod potential component anchor index) current hCurrent).smul
      (contMDiffWithinAt_const (c := throatRadialReferenceCovector index))

/-! ## Smooth contragredient overlap action -/

/-- For two fixed centered frames, their contragredient action on model
covectors is `C∞` on the double overlap when coerced to a continuous linear
map.  This regularity alone does not assert a differentiated overlap law. -/
theorem throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real,
        FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod =>
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) := by
  have hInverse :=
    throatGaugeTangentTrivializationTransitionAt_symm_contMDiffOn
      period hPeriod firstAnchor secondAnchor
  have hIdentity :
      ContMDiffOn throatCoverModelWithCorners
        𝓘(Real, Real →L[Real] Real) ∞
        (fun _ : EffectiveThroat period hPeriod =>
          (ContinuousLinearEquiv.refl Real Real : Real →L[Real] Real))
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :=
    contMDiffOn_const
  simpa only [throatGaugeCovectorTrivializationTransitionAt] using
    hInverse.cle_arrowCongr hIdentity

end
end P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
end JanusFormal
