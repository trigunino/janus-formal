import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

/-!
# Deck compatibility of the explicit local intrinsic normal lift

The generator reverses the latitude parameter.  After quotient projection
this gives the exact sign law required by the sign-clutched D8 normal line.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev ThroatBase := MappingTorus (throatData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One deck turn reverses the normal parameter after passing to the
mapping-torus quotient. -/
theorem quotientNormalLatitude_deck_generator
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ anchor) normal =
      quotientNormalLatitude period hPeriod anchor (-normal) := by
  unfold quotientNormalLatitude
  rw [normalLatitudeCover_deck_generator_twist]
  exact (mappingTorusMk_isAddQuotientCoveringMap
    (sphereData period hPeriod)).map_vadd 1

/-- Tangent of the quotient latitude curve at its throat point, retaining the
chosen cover lift as local orientation data. -/
def quotientLatitudeNormalVectorAtCover
    (anchor : EffectiveThroatCover period hPeriod) :
    TangentSpace coverModelWithCorners
      (quotientNormalLatitude period hPeriod anchor 0) :=
  mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
    (quotientNormalLatitude period hPeriod anchor) 0 1

/-- Derivative of precomposition by scalar reflection at the origin. -/
theorem mfderiv_precomp_neg_one
    (curve : Real → EffectiveQuotient period hPeriod)
    (hCurve : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners
      curve 0) :
    mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (fun normal => curve (-normal)) 0 1 =
      -mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        curve 0 1 := by
  have hNeg : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real)
      (fun normal : Real => -normal) 0 :=
    (contMDiff_id.neg : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      (fun normal : Real => -normal)).mdifferentiableAt (by simp)
  have hNegDerivative :
      mfderiv (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real)
        (fun normal : Real => -normal) 0 1 = -1 := by
    rw [show (fun normal : Real => -normal) = -(id : Real → Real) by rfl]
    rw [mfderiv_neg, mfderiv_id]
    change -(1 : Real) = -(1 : Real)
    rfl
  have hCurveAtNegZero : MDifferentiableAt
      (modelWithCornersSelf Real Real) coverModelWithCorners curve (-0) := by
    simpa using hCurve
  have hComp := mfderiv_comp_apply 0 hCurveAtNegZero hNeg 1
  rw [hNegDerivative, map_neg] at hComp
  have hFunction : curve ∘ (fun normal : Real => -normal) =
      fun normal : Real => curve (-normal) := rfl
  rw [hFunction] at hComp
  have hNegZero : (-0 : Real) = 0 := neg_zero
  rw [hNegZero] at hComp
  exact hComp

/-- Exact one-turn sign law for the quotient-latitude tangent.  `HEq` records
the dependent transport between the propositionally equal quotient bases. -/
theorem quotientLatitudeNormalVectorAtCover_deck_generator
    (anchor : EffectiveThroatCover period hPeriod) :
    HEq
      (quotientLatitudeNormalVectorAtCover period hPeriod
        ((1 : Int) +ᵥ anchor))
      (-quotientLatitudeNormalVectorAtCover period hPeriod anchor) := by
  have hCurve :
      quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ anchor) =
        fun normal => quotientNormalLatitude period hPeriod anchor (-normal) := by
    funext normal
    exact quotientNormalLatitude_deck_generator
      period hPeriod anchor normal
  have hRegularity : MDifferentiableAt
      (modelWithCornersSelf Real Real) coverModelWithCorners
      (quotientNormalLatitude period hPeriod anchor) 0 :=
    (quotientNormalLatitude_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  unfold quotientLatitudeNormalVectorAtCover
  rw [hCurve]
  exact (mfderiv_precomp_neg_one period hPeriod _ hRegularity).heq

/-- The scalar-square model is invariant under the simultaneous one-turn
deck move and sign-clutched coordinate reversal. -/
theorem canonicalLocalNormalMetricModel_deck_generator
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    canonicalLocalNormalMetricModel period hPeriod
        (((1 : Int) +ᵥ anchor), -scalar) =
      canonicalLocalNormalMetricModel period hPeriod (anchor, scalar) := by
  simp [canonicalLocalNormalMetricModel, pow_two]

/-- The actual one-loop transition of the constructed normal bundle preserves
the explicit local quadratic model. -/
theorem canonicalLocalNormalMetricModel_coordChange_one_loop
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    let base := mappingTorusMk (throatData period hPeriod) anchor
    canonicalLocalNormalMetricModel period hPeriod
        (((1 : Int) +ᵥ anchor),
          (fixedThroatNormalVectorBundleCore period hPeriod).coordChange
            anchor ((1 : Int) +ᵥ anchor) base scalar) =
      canonicalLocalNormalMetricModel period hPeriod (anchor, scalar) := by
  dsimp only
  rw [one_loop_coordChange_eq_neg_id]
  exact canonicalLocalNormalMetricModel_deck_generator
    period hPeriod anchor scalar

/-- Consequently the metric square of the two explicit local orthogonal lifts
agrees across a one-turn sign transition. -/
theorem canonicalLocalOrthogonalNormalLift_square_deck_generator
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    let deckAnchor := (1 : Int) +ᵥ anchor
    let deckNormal :=
      canonicalLocalNormalClassEquiv period hPeriod deckAnchor (-scalar)
    let normal := canonicalLocalNormalClassEquiv period hPeriod anchor scalar
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (throatData period hPeriod) deckAnchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod
          deckAnchor deckNormal)
        (canonicalLocalOrthogonalNormalLift period hPeriod
          deckAnchor deckNormal) =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (throatData period hPeriod) anchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal)
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal) := by
  dsimp only
  rw [canonicalLocalOrthogonalNormalLift_square_in_coordinates]
  rw [canonicalLocalOrthogonalNormalLift_square_in_coordinates]
  ring

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
end JanusFormal
