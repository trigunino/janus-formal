import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionScalarCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

/-!
# Global algebraic canonical normal lift

The canonical quotient class inherits the all-winding sign cocycle.  Changing
the cover lift changes both the scalar coordinate and the unit normal by the
same sign, so the resulting orthogonal representative is unchanged.  This
constructs a global fiberwise-linear lift, not a nonzero global normal section.

The final total-space continuity field is reduced to its exact local chart
condition.  The transported differential-normal atlas was built from an
arbitrary pointwise equivalence, so its identification with the normalized
canonical class charts is not silently assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLift4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 200000

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
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionScalarCocycle4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private local instance throatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance throatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance quotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev ThroatTangent (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev AmbientTangent (point : EffectiveThroat period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev TangentialRange (point : EffectiveThroat period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

private abbrev LiftFamily (point : EffectiveThroat period hPeriod) :=
  DifferentialNormalFiber period hPeriod point →ₗ[Real]
    AmbientTangent period hPeriod point

private theorem dependentApply_heq
    {α : Sort _} {β γ : α → Sort _}
    (f : (point : α) → β point → γ point)
    {source target : α} (hBase : source = target)
    {first : β source} {second : β target}
    (hValue : HEq first second) :
    HEq (f source first) (f target second) := by
  cases hBase
  cases hValue
  rfl

private theorem throatPoint_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    mappingTorusMk (throatData period hPeriod) (winding +ᵥ anchor) =
      mappingTorusMk (throatData period hPeriod) anchor :=
  (mappingTorusMk_isAddQuotientCoveringMap
    (throatData period hPeriod)).map_vadd winding

/-- The canonical quotient class has the same all-winding sign character as
its canonical ambient representative. -/
theorem canonicalQuotientLatitudeNormalClass_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    HEq
      (canonicalQuotientLatitudeNormalClass period hPeriod
        (winding +ᵥ anchor))
      ((normalSignRepresentation winding : Real) •
        canonicalQuotientLatitudeNormalClass period hPeriod anchor) := by
  have hBase := throatPoint_deck_winding period hPeriod winding anchor
  have hVector := canonicalQuotientLatitudeNormal_deck_winding
    period hPeriod winding anchor
  have hQuotient : HEq
      ((TangentialRange period hPeriod
          (mappingTorusMk (throatData period hPeriod) (winding +ᵥ anchor))).mkQ
        (canonicalQuotientLatitudeNormal period hPeriod
          (winding +ᵥ anchor)))
      ((TangentialRange period hPeriod
          (mappingTorusMk (throatData period hPeriod) anchor)).mkQ
        ((normalSignRepresentation winding : Real) •
          canonicalQuotientLatitudeNormal period hPeriod anchor)) :=
    dependentApply_heq
      (fun point vector => (TangentialRange period hPeriod point).mkQ vector)
      hBase hVector
  simpa only [canonicalQuotientLatitudeNormalClass, map_smul] using hQuotient

/-- Transport one canonical local lift to a specified quotient base. -/
def canonicalOrthogonalNormalLiftFromAnchor
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point) :
    LiftFamily period hPeriod point :=
  Eq.mp (congrArg (LiftFamily period hPeriod) hPoint)
    (canonicalLocalOrthogonalNormalLift period hPeriod anchor)

theorem canonicalOrthogonalNormalLiftFromAnchor_represents
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (TangentialRange period hPeriod point).mkQ
        (canonicalOrthogonalNormalLiftFromAnchor
          period hPeriod anchor point hPoint normal) = normal := by
  cases hPoint
  exact canonicalLocalOrthogonalNormalLift_represents
    period hPeriod anchor normal

theorem canonicalOrthogonalNormalLiftFromAnchor_orthogonal
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point)
    (normal : DifferentialNormalFiber period hPeriod point)
    (tangent : ThroatTangent period hPeriod point) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalOrthogonalNormalLiftFromAnchor
          period hPeriod anchor point hPoint normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0 := by
  cases hPoint
  exact canonicalLocalOrthogonalNormalLift_orthogonal
    period hPeriod anchor normal tangent

private theorem orthogonalRepresentative_unique
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (first second : AmbientTangent period hPeriod point)
    (hFirstClass : (TangentialRange period hPeriod point).mkQ first = normal)
    (hSecondClass : (TangentialRange period hPeriod point).mkQ second = normal)
    (hFirstOrthogonal : ∀ tangent : ThroatTangent period hPeriod point,
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod point) first
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0)
    (hSecondOrthogonal : ∀ tangent : ThroatTangent period hPeriod point,
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod point) second
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0) :
    first = second := by
  have hQuotient :
      (TangentialRange period hPeriod point).mkQ first =
        (TangentialRange period hPeriod point).mkQ second :=
    hFirstClass.trans hSecondClass.symm
  have hDifference : first - second ∈ TangentialRange period hPeriod point :=
    (Submodule.Quotient.eq (TangentialRange period hPeriod point)).1 hQuotient
  rcases hDifference with ⟨tangent, hTangent⟩
  have hTangentZero : tangent = 0 :=
    intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical
      period hPeriod point tangent (fun other => by
        calc
          (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
              (fixedThroatQuotientInclusion period hPeriod point)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point tangent)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point other) =
            (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
              (fixedThroatQuotientInclusion period hPeriod point)
              (first - second)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point other) :=
              congrArg
                (fun vector =>
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
                    (fixedThroatQuotientInclusion period hPeriod point) vector
                    (mfderiv throatCoverModelWithCorners coverModelWithCorners
                      (fixedThroatQuotientInclusion period hPeriod) point other))
                hTangent
          _ = 0 := by
            rw [map_sub, sub_apply,
              hFirstOrthogonal other, hSecondOrthogonal other]
            simp)
  have hDifferenceZero : first - second = 0 := by
    rw [← hTangent, hTangentZero]
    exact map_zero _
  exact sub_eq_zero.mp hDifferenceZero

/-- The transported local orthogonal lift is independent of the chosen cover
representative. -/
theorem canonicalOrthogonalNormalLiftFromAnchor_eq
    (first second : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hFirst : mappingTorusMk (throatData period hPeriod) first = point)
    (hSecond : mappingTorusMk (throatData period hPeriod) second = point) :
    canonicalOrthogonalNormalLiftFromAnchor
        period hPeriod first point hFirst =
      canonicalOrthogonalNormalLiftFromAnchor
        period hPeriod second point hSecond := by
  apply LinearMap.ext
  intro normal
  exact orthogonalRepresentative_unique period hPeriod point normal _ _
    (canonicalOrthogonalNormalLiftFromAnchor_represents
      period hPeriod first point hFirst normal)
    (canonicalOrthogonalNormalLiftFromAnchor_represents
      period hPeriod second point hSecond normal)
    (canonicalOrthogonalNormalLiftFromAnchor_orthogonal
      period hPeriod first point hFirst normal)
    (canonicalOrthogonalNormalLiftFromAnchor_orthogonal
      period hPeriod second point hSecond normal)

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLift4D
end JanusFormal
