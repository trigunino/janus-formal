import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLift4D

/-!
# Chosen global canonical normal lift

The algebraic descent and independence of the cover representative are opaque
imports from the preceding gate.  This small gate chooses the preferred cover
lift at each quotient point and packages the resulting global family.  It does
not construct a nonzero global normal section.

Continuity of its metric square is reduced to the exact local statement in the
already installed transported differential-normal charts.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000

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
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLift4D

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

/-- Global fiberwise-linear orthogonal lift obtained from the preferred cover
representative.  This is an operator family, not a normal section. -/
def canonicalGlobalOrthogonalNormalLift
    (point : EffectiveThroat period hPeriod) :
    LiftFamily period hPeriod point :=
  canonicalOrthogonalNormalLiftFromAnchor period hPeriod
    (normalBundleIndexAt period hPeriod point) point
    (normalBundleIndexAt_projects period hPeriod point)

/-- The chosen global family agrees with the lift transported from every
cover representative of the same quotient point. -/
theorem canonicalGlobalOrthogonalNormalLift_eq_fromAnchor
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point) :
    canonicalGlobalOrthogonalNormalLift period hPeriod point =
      canonicalOrthogonalNormalLiftFromAnchor
        period hPeriod anchor point hPoint := by
  exact canonicalOrthogonalNormalLiftFromAnchor_eq period hPeriod
    (normalBundleIndexAt period hPeriod point) anchor point
    (normalBundleIndexAt_projects period hPeriod point) hPoint

theorem canonicalGlobalOrthogonalNormalLift_represents
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (TangentialRange period hPeriod point).mkQ
        (canonicalGlobalOrthogonalNormalLift period hPeriod point normal) =
      normal := by
  rw [canonicalGlobalOrthogonalNormalLift_eq_fromAnchor period hPeriod
    (normalBundleIndexAt period hPeriod point) point
    (normalBundleIndexAt_projects period hPeriod point)]
  exact canonicalOrthogonalNormalLiftFromAnchor_represents period hPeriod
    (normalBundleIndexAt period hPeriod point) point
    (normalBundleIndexAt_projects period hPeriod point) normal

theorem canonicalGlobalOrthogonalNormalLift_orthogonal
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (tangent : ThroatTangent period hPeriod point) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalGlobalOrthogonalNormalLift period hPeriod point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0 := by
  rw [canonicalGlobalOrthogonalNormalLift_eq_fromAnchor period hPeriod
    (normalBundleIndexAt period hPeriod point) point
    (normalBundleIndexAt_projects period hPeriod point)]
  exact canonicalOrthogonalNormalLiftFromAnchor_orthogonal period hPeriod
    (normalBundleIndexAt period hPeriod point) point
    (normalBundleIndexAt_projects period hPeriod point) normal tangent

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
end JanusFormal
