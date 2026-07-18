import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D

/-!
# Total `R^4` parametrizations of cover-coordinate balls

`OpenPartialHomeomorph.univBall`, transported through a finite-dimensional
linear equivalence, supplies the total ball parametrization required by the
canonical holonomic-chart gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D

abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D.Vector4

private def coverCoordinateBasis : Module.Basis (Fin 4) Real CoverCoordinates := by
  let basis := Module.finBasis Real CoverCoordinates
  have hDimension : Module.finrank Real CoverCoordinates = 4 := by
    simp [CoverCoordinates]
  simpa [hDimension] using basis

/-- A finite-dimensional continuous linear identification of the coordinate
vector space with the cover model. -/
private def vector4CoverEquiv : Vector4 ≃L[Real] CoverCoordinates :=
  coverCoordinateBasis.equivFun.symm.toContinuousLinearEquiv

private def vector4CoverDiffeomorph :
    Diffeomorph (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real CoverCoordinates)
      Vector4 CoverCoordinates ∞ where
  toEquiv := vector4CoverEquiv.toLinearEquiv.toEquiv
  contMDiff_toFun := by
    rw [contMDiff_iff_contDiff]
    exact vector4CoverEquiv.contDiff
  contMDiff_invFun := by
    rw [contMDiff_iff_contDiff]
    exact vector4CoverEquiv.symm.contDiff

@[simp]
private theorem vector4CoverDiffeomorph_apply (coordinate : Vector4) :
    vector4CoverDiffeomorph coordinate = vector4CoverEquiv coordinate :=
  rfl

private def componentwiseUnivBallHomeomorph
    (center : CoverCoordinates) (radius : Real) :
    OpenPartialHomeomorph CoverCoordinates CoverCoordinates :=
  (OpenPartialHomeomorph.univBall center.1 radius).prod
    (OpenPartialHomeomorph.univBall center.2 radius)

private theorem componentwiseUnivBallHomeomorph_target
    (center : CoverCoordinates) (radius : Real) (hRadius : 0 < radius) :
    (componentwiseUnivBallHomeomorph center radius).target =
      Metric.ball center radius := by
  rw [componentwiseUnivBallHomeomorph,
    OpenPartialHomeomorph.prod_target,
    OpenPartialHomeomorph.univBall_target center.1 hRadius,
    OpenPartialHomeomorph.univBall_target center.2 hRadius]
  simpa only [Prod.eta] using ball_prod_same center.1 center.2 radius

private def componentwiseUnivBallPartialDiffeomorph
    (center : CoverCoordinates) (radius : Real) (hRadius : 0 < radius) :
    PartialDiffeomorph (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real CoverCoordinates)
      CoverCoordinates CoverCoordinates ∞ where
  __ := componentwiseUnivBallHomeomorph center radius
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    have hFirst : ContDiff Real ∞
        (OpenPartialHomeomorph.univBall center.1 radius) :=
      OpenPartialHomeomorph.contDiff_univBall
    have hSecond : ContDiff Real ∞
        (OpenPartialHomeomorph.univBall center.2 radius) :=
      OpenPartialHomeomorph.contDiff_univBall
    have hSmooth : ContDiffOn Real ∞
        (Prod.map
          (OpenPartialHomeomorph.univBall center.1 radius)
          (OpenPartialHomeomorph.univBall center.2 radius))
        (Set.univ ×ˢ Set.univ) :=
      hFirst.contDiffOn.prodMap hSecond.contDiffOn
    simp only [componentwiseUnivBallHomeomorph,
      OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.univBall_source]
    apply hSmooth.congr
    rintro ⟨first, second⟩ _
    rfl
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    have hFirst : ContDiffOn Real ∞
        (OpenPartialHomeomorph.univBall center.1 radius).symm
        (Metric.ball center.1 radius) :=
      OpenPartialHomeomorph.contDiffOn_univBall_symm
    have hSecond : ContDiffOn Real ∞
        (OpenPartialHomeomorph.univBall center.2 radius).symm
        (Metric.ball center.2 radius) :=
      OpenPartialHomeomorph.contDiffOn_univBall_symm
    have hSmooth : ContDiffOn Real ∞
        (Prod.map
          (OpenPartialHomeomorph.univBall center.1 radius).symm
          (OpenPartialHomeomorph.univBall center.2 radius).symm)
        (Metric.ball center.1 radius ×ˢ
          Metric.ball center.2 radius) :=
      hFirst.prodMap hSecond
    simp only [componentwiseUnivBallHomeomorph,
      OpenPartialHomeomorph.prod_target,
      OpenPartialHomeomorph.univBall_target center.1 hRadius,
      OpenPartialHomeomorph.univBall_target center.2 hRadius]
    apply hSmooth.congr
    rintro ⟨first, second⟩ _
    rfl

private def totalBallMap (center : CoverCoordinates) (radius : Real) :
    Vector4 → CoverCoordinates :=
  fun coordinate =>
    componentwiseUnivBallHomeomorph center radius
      (vector4CoverEquiv coordinate)

private theorem totalBallMap_injective
    (center : CoverCoordinates) (radius : Real) :
    Function.Injective (totalBallMap center radius) := by
  intro first second hEqual
  apply vector4CoverEquiv.injective
  apply (componentwiseUnivBallHomeomorph center radius).injOn
  · simp [componentwiseUnivBallHomeomorph,
      OpenPartialHomeomorph.univBall_source]
  · simp [componentwiseUnivBallHomeomorph,
      OpenPartialHomeomorph.univBall_source]
  simpa only [totalBallMap] using hEqual

private theorem totalBallMap_range
    (center : CoverCoordinates) (radius : Real) (hRadius : 0 < radius) :
    Set.range (totalBallMap center radius) = Metric.ball center radius := by
  ext point
  constructor
  · rintro ⟨coordinate, rfl⟩
    have hSource : vector4CoverEquiv coordinate ∈
        (componentwiseUnivBallHomeomorph center radius).source := by
      simp [componentwiseUnivBallHomeomorph,
        OpenPartialHomeomorph.univBall_source]
    have hTarget :=
      (componentwiseUnivBallHomeomorph center radius).map_source hSource
    rwa [componentwiseUnivBallHomeomorph_target center radius hRadius] at hTarget
  · intro hPoint
    have hTarget : point ∈
        (componentwiseUnivBallHomeomorph center radius).target := by
      rwa [componentwiseUnivBallHomeomorph_target center radius hRadius]
    obtain ⟨coordinate, hCoordinate⟩ :=
      vector4CoverEquiv.surjective
        ((componentwiseUnivBallHomeomorph center radius).symm point)
    refine ⟨coordinate, ?_⟩
    rw [totalBallMap, hCoordinate]
    exact (componentwiseUnivBallHomeomorph center radius).right_inv hTarget

private theorem totalBallMap_isLocalDiffeomorph
    (center : CoverCoordinates) (radius : Real) (hRadius : 0 < radius) :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (totalBallMap center radius) := by
  intro coordinate
  have hLinear := vector4CoverDiffeomorph.isLocalDiffeomorph coordinate
  have hSource : vector4CoverEquiv coordinate ∈
      (componentwiseUnivBallPartialDiffeomorph center radius hRadius).source := by
    simp [componentwiseUnivBallPartialDiffeomorph,
      componentwiseUnivBallHomeomorph,
      OpenPartialHomeomorph.univBall_source]
  have hBall := PartialDiffeomorph.isLocalDiffeomorphAt
    (I := modelWithCornersSelf Real CoverCoordinates)
    (J := modelWithCornersSelf Real CoverCoordinates)
    (n := ∞)
    (componentwiseUnivBallPartialDiffeomorph center radius hRadius) hSource
  have hComposition := IsLocalDiffeomorphAt.comp
    (I := modelWithCornersSelf Real Vector4)
    (J := modelWithCornersSelf Real CoverCoordinates)
    (K := modelWithCornersSelf Real CoverCoordinates)
    (M := Vector4) (N := CoverCoordinates) (P := CoverCoordinates)
    (n := ∞) hLinear hBall
  convert hComposition using 1
  funext point
  rfl

/-- The canonical total parametrization of a positive-radius cover ball. -/
def totalR4BallParametrization
    (center : CoverCoordinates) (radius : Real) (hRadius : 0 < radius) :
    TotalR4BallParametrization center radius where
  toFun := totalBallMap center radius
  at_zero := by
    simp [totalBallMap, componentwiseUnivBallHomeomorph]
  injective := totalBallMap_injective center radius
  range_eq_ball := totalBallMap_range center radius hRadius
  isLocalDiffeomorph :=
    totalBallMap_isLocalDiffeomorph center radius hRadius

/-- The formerly conditional analytic input is available unconditionally. -/
theorem totalR4BallParametrizationsExist :
    TotalR4BallParametrizationsExist := by
  intro center radius hRadius
  exact ⟨totalR4BallParametrization center radius hRadius⟩

/-- Every point of the effective quotient lies on a canonical holonomic
chart. -/
theorem canonicalHolonomicChartThroughEveryPoint
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalHolonomicChartThroughEveryPoint period hPeriod :=
  canonicalHolonomicChartThroughEveryPoint_of_totalR4BallParametrizations
    period hPeriod totalR4BallParametrizationsExist

/-- The canonical holonomic charts form a realizable atlas cover. -/
theorem canonicalHolonomicAtlasCoverRealizable
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalHolonomicAtlasCoverRealizable period hPeriod :=
  (canonicalHolonomicAtlasCoverRealizable_iff_chartThroughEveryPoint
    period hPeriod).2
      (canonicalHolonomicChartThroughEveryPoint period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
end JanusFormal
