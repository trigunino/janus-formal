import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D

/-!
# All-winding deck laws for the explicit intrinsic normal

The generator sign law is extended to every integer winding.  The resulting
curve, tangent and quadratic laws are kept separate from the final continuous
gluing of the local orthogonal lifts.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev ThroatBase := MappingTorus (throatData period hPeriod)

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

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Every deck winding acts on the quotient latitude curve by its normal-sign
character. -/
theorem quotientNormalLatitude_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod)
    (normal : Real) :
    quotientNormalLatitude period hPeriod (winding +ᵥ anchor) normal =
      quotientNormalLatitude period hPeriod anchor
        ((normalSignRepresentation winding : Real) * normal) := by
  let motive : Int → Prop := fun current => ∀ coordinate : Real,
    quotientNormalLatitude period hPeriod (current +ᵥ anchor) coordinate =
      quotientNormalLatitude period hPeriod anchor
        ((normalSignRepresentation current : Real) * coordinate)
  have hAll : motive winding := by
    refine Int.inductionOn' winding 0 ?_ (fun current _ ih => ?_)
      (fun current _ ih => ?_)
    · intro coordinate
      simp [normalSignRepresentation]
    · intro coordinate
      calc
      quotientNormalLatitude period hPeriod ((current + 1) +ᵥ anchor)
          coordinate =
        quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ
          (current +ᵥ anchor)) coordinate := by
            rw [← add_vadd]
            congr 2
            omega
      _ = quotientNormalLatitude period hPeriod (current +ᵥ anchor)
          (-coordinate) :=
        quotientNormalLatitude_deck_generator period hPeriod
          (current +ᵥ anchor) coordinate
      _ = quotientNormalLatitude period hPeriod anchor
          ((normalSignRepresentation current : Real) * (-coordinate)) :=
        ih (-coordinate)
      _ = quotientNormalLatitude period hPeriod anchor
          ((normalSignRepresentation (current + 1) : Real) * coordinate) := by
        congr 1
        rw [normal_sign_add]
        simp [normalSignRepresentation]
    · intro coordinate
      calc
      quotientNormalLatitude period hPeriod ((current - 1) +ᵥ anchor)
          coordinate =
        quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ
          ((current - 1) +ᵥ anchor)) (-coordinate) :=
        by
          simpa using
            (quotientNormalLatitude_deck_generator period hPeriod
              ((current - 1) +ᵥ anchor) (-coordinate)).symm
      _ = quotientNormalLatitude period hPeriod (current +ᵥ anchor)
          (-coordinate) := by
            rw [← add_vadd]
            congr 2
            omega
      _ = quotientNormalLatitude period hPeriod anchor
          ((normalSignRepresentation current : Real) * (-coordinate)) :=
        ih (-coordinate)
      _ = quotientNormalLatitude period hPeriod anchor
          ((normalSignRepresentation (current - 1) : Real) * coordinate) := by
        congr 1
        rw [show current = (current - 1) + 1 by omega, normal_sign_add]
        simp [normalSignRepresentation]
  exact hAll normal

/-- Exact all-winding sign law for the quotient-latitude tangent.  `HEq`
retains the dependent transport between the equal zero-latitude bases. -/
theorem quotientLatitudeNormalVectorAtCover_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    HEq
      (quotientLatitudeNormalVectorAtCover period hPeriod (winding +ᵥ anchor))
      ((normalSignRepresentation winding : Real) •
        quotientLatitudeNormalVectorAtCover period hPeriod anchor) := by
  have hRegularity : MDifferentiableAt
      (modelWithCornersSelf Real Real) coverModelWithCorners
      (quotientNormalLatitude period hPeriod anchor) 0 :=
    (quotientNormalLatitude_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  by_cases hEven : Even winding
  · have hCurve :
        quotientNormalLatitude period hPeriod (winding +ᵥ anchor) =
          quotientNormalLatitude period hPeriod anchor := by
      funext normal
      simpa [normal_sign_even winding hEven] using
        quotientNormalLatitude_deck_winding period hPeriod
          winding anchor normal
    unfold quotientLatitudeNormalVectorAtCover
    rw [hCurve]
    simp [normal_sign_even winding hEven]
  · have hCurve :
        quotientNormalLatitude period hPeriod (winding +ᵥ anchor) =
          fun normal => quotientNormalLatitude period hPeriod anchor (-normal) := by
      funext normal
      simpa [normal_sign_odd winding hEven] using
        quotientNormalLatitude_deck_winding period hPeriod
          winding anchor normal
    unfold quotientLatitudeNormalVectorAtCover
    rw [hCurve]
    rw [show (normalSignRepresentation winding : Real) = -1 by
      rw [normal_sign_odd winding hEven]
      rfl]
    rw [neg_one_smul]
    exact (mfderiv_precomp_neg_one period hPeriod _ hRegularity).heq

/-- The local scalar-square model is invariant under every sign-clutched
deck winding. -/
theorem canonicalLocalNormalMetricModel_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod)
    (scalar : Real) :
    canonicalLocalNormalMetricModel period hPeriod
        (winding +ᵥ anchor,
          (normalSignRepresentation winding : Real) * scalar) =
      canonicalLocalNormalMetricModel period hPeriod (anchor, scalar) := by
  by_cases hEven : Even winding
  · simp [canonicalLocalNormalMetricModel, normalSignRepresentation, hEven]
  · simp [canonicalLocalNormalMetricModel, normalSignRepresentation, hEven,
      pow_two]

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D
end JanusFormal
