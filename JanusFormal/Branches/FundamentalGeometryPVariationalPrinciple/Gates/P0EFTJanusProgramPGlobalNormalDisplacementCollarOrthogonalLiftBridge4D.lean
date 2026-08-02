import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D

/-!
# Normal-displacement collar derivative and the canonical orthogonal lift

The derivative at the zero section of the descended normal graph is exactly
the existing canonical global orthogonal representative of the differential
normal class encoded by the same local displacement coordinate.  All changes
of tangent base point are displayed explicitly; no global normal orientation
is chosen.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalNormalDisplacementCollarOrthogonalLiftBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionScalarCocycle4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLift4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D

attribute [local instance 10000] instChartedSpaceCoverModelEffectiveQuotient

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance (priority := 20000) throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance (priority := 20000) throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance (priority := 20000) effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (priority := 20000) effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance (priority := 20000) normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

local instance (priority := 20000) effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (priority := 20000) effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem eqMp_heq {α β : Sort _} (h : α = β) (x : α) :
    HEq (Eq.mp h x) x := by
  cases h
  rfl

/-- Differential-normal class selected by the same local scalar coordinate
that drives the explicit collar graph. -/
def normalGraphDifferentialClass
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    DifferentialNormalFiber period hPeriod
      (mappingTorusMk (throatData period hPeriod) anchor) :=
  canonicalLocalNormalClassEquiv period hPeriod anchor
    (normalCoordinateLift period hPeriod displacement anchor)

/-- The global orthogonal lift of the graph class is the local scalar times
the canonical pushed latitude normal. -/
theorem canonicalGlobalOrthogonalNormalLift_normalGraphDifferentialClass
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    canonicalGlobalOrthogonalNormalLift period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor)
        (normalGraphDifferentialClass period hPeriod displacement anchor) =
      normalCoordinateLift period hPeriod displacement anchor •
        canonicalQuotientLatitudeNormal period hPeriod anchor := by
  rw [canonicalGlobalOrthogonalNormalLift_eq_fromAnchor period hPeriod anchor
    (mappingTorusMk (throatData period hPeriod) anchor) rfl]
  change
    ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm
        (normalGraphDifferentialClass period hPeriod displacement anchor)) •
        canonicalQuotientLatitudeNormal period hPeriod anchor =
      normalCoordinateLift period hPeriod displacement anchor •
        canonicalQuotientLatitudeNormal period hPeriod anchor
  rw [show normalGraphDifferentialClass period hPeriod displacement anchor =
      canonicalLocalNormalClassEquiv period hPeriod anchor
        (normalCoordinateLift period hPeriod displacement anchor) by rfl,
    (canonicalLocalNormalClassEquiv period hPeriod anchor).symm_apply_apply]

/-- Exact derivative of the physical normal graph at zero.  The explicit
`Eq.mp` only transports the tangent along `normalGraph_zero`. -/
theorem normalGraph_mk_mfderiv_zero_eq_canonicalGlobalOrthogonalNormalLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    Eq.mp
        (congrArg (TangentSpace coverModelWithCorners)
          (normalGraph_zero period hPeriod displacement
            (mappingTorusMk (throatData period hPeriod) anchor)))
        (mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun parameter : Real =>
            normalGraph period hPeriod displacement parameter
              (mappingTorusMk (throatData period hPeriod) anchor)) 0 1) =
      canonicalGlobalOrthogonalNormalLift period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor)
        (normalGraphDifferentialClass period hPeriod displacement anchor) := by
  let scalar := normalCoordinateLift period hPeriod displacement anchor
  let coordinate : Real → Real := fun parameter =>
    (normalGraphCoordinate period hPeriod displacement parameter anchor).1
  let latitude := quotientNormalLatitude period hPeriod anchor
  let curve : Real → EffectiveQuotient period hPeriod := fun parameter =>
    normalGraph period hPeriod displacement parameter
      (mappingTorusMk (throatData period hPeriod) anchor)
  have hCurve : curve = latitude ∘ coordinate := by
    funext parameter
    rfl
  have hLatitude : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners latitude 0 :=
    (quotientNormalLatitude_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  have hCoordinate : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) coordinate 0 := by
    exact (normalGraphCoordinate_hasDerivAt_zero period hPeriod displacement
      anchor).differentiableAt.mdifferentiableAt
  have hCoordinateValue : coordinate 0 = 0 := by
    exact normalGraphCoordinate_zero period hPeriod displacement anchor
  have hCoordinateDerivative :
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) coordinate 0 1 = scalar := by
    rw [mfderiv_eq_fderiv]
    have hFDeriv :=
      (normalGraphCoordinate_hasDerivAt_zero period hPeriod displacement anchor)
        |>.hasFDerivAt.fderiv
    change fderiv Real coordinate 0 1 = scalar
    rw [hFDeriv]
    simp [scalar]
  have hLatitudeAt : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners latitude (coordinate 0) := by
    simpa [hCoordinateValue] using hLatitude
  have hComp := mfderiv_comp_apply 0 hLatitudeAt hCoordinate 1
  rw [hCoordinateDerivative, hCoordinateValue] at hComp
  have hScaled :
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          latitude 0 scalar =
        scalar • mfderiv (modelWithCornersSelf Real Real)
          coverModelWithCorners latitude 0 1 := by
    let derivative := mfderiv (modelWithCornersSelf Real Real)
      coverModelWithCorners latitude 0
    calc
      derivative scalar = derivative
          (scalar • (1 : TangentSpace
            (modelWithCornersSelf Real Real) (0 : Real))) := by
        congr 1
        change scalar = scalar * 1
        ring
      _ = scalar • derivative 1 :=
        derivative.map_smul scalar
          (1 : TangentSpace (modelWithCornersSelf Real Real) (0 : Real))
  have hDerivative : HEq
      (mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        curve 0 1)
      (scalar • quotientLatitudeNormalVectorAtCover period hPeriod anchor) := by
    rw [hCurve]
    exact (hComp.trans hScaled).heq
  have hCanonical : HEq
      (scalar • quotientLatitudeNormalVectorAtCover period hPeriod anchor)
      (scalar • canonicalQuotientLatitudeNormal period hPeriod anchor) :=
    (canonicalQuotientLatitudeNormal_smul_heq period hPeriod anchor scalar).symm
  apply eq_of_heq
  exact
    (eqMp_heq _ _).trans
      (hDerivative.trans
        (hCanonical.trans
          (canonicalGlobalOrthogonalNormalLift_normalGraphDifferentialClass
            period hPeriod displacement anchor).symm.heq))

end
end P0EFTJanusProgramPGlobalNormalDisplacementCollarOrthogonalLiftBridge4D
end JanusFormal
