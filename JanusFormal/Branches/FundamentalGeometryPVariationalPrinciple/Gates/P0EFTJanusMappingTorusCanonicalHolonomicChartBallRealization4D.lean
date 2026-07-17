import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.StdBasis
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D

/-!
# Holonomic charts from total ball parametrizations

The quotient projection and the inverse of a cover chart are local
diffeomorphisms.  Thus a total smooth parametrization of a sufficiently small
coordinate ball gives the total holonomic patch required downstream.  The
only residual datum below is the standard analytic diffeomorphism from
`R^4` onto an open ball; Mathlib currently has no bundled version of it.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D

set_option autoImplicit false

noncomputable section

open Set Metric
open Module
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private theorem smoothOrder_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by
  simp

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

@[implicit_reducible] local instance :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A genuine total parametrization of one cover-model ball.  Injectivity and
the exact range make this stronger than the local-diffeomorphism property used
below. -/
structure TotalR4BallParametrization
    (center : CoverCoordinates) (radius : Real) where
  toFun : Vector4 → CoverCoordinates
  at_zero : toFun 0 = center
  injective : Function.Injective toFun
  range_eq_ball : Set.range toFun = Metric.ball center radius
  isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real CoverCoordinates) ∞ toFun

/-- Exact analytic input absent from the current Mathlib API. -/
def TotalR4BallParametrizationsExist : Prop :=
  ∀ (center : CoverCoordinates) (radius : Real), 0 < radius →
    Nonempty (TotalR4BallParametrization center radius)

private def coordinateFrame
    (coordinateMap : Vector4 → EffectiveQuotient period hPeriod)
    (hMap : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap)
    (coordinate : Vector4) :
    Module.Basis Index4 Real
      (TangentSpace coverModelWithCorners (coordinateMap coordinate)) :=
  (Pi.basisFun Real Index4).map
    (hMap.mfderivToContinuousLinearEquiv smoothOrder_ne_zero
      coordinate).toLinearEquiv

private theorem coordinateFrame_eq_mfderiv
    (coordinateMap : Vector4 → EffectiveQuotient period hPeriod)
    (hMap : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap)
    (coordinate : Vector4) (index : Index4) :
    coordinateFrame period hPeriod coordinateMap hMap coordinate index =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        coordinateMap coordinate
          (Pi.single index (1 : Real) : Vector4) := by
  rw [← hMap.mfderivToContinuousLinearEquiv_coe smoothOrder_ne_zero coordinate]
  unfold coordinateFrame
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact congrFun
    (ContinuousLinearEquiv.coe_toLinearEquiv
      (hMap.mfderivToContinuousLinearEquiv smoothOrder_ne_zero coordinate))
    (Pi.single index (1 : Real) : Vector4)

private def coordinateBasisTangentInput (index : Index4)
    (coordinate : Vector4) :
    TangentBundle (modelWithCornersSelf Real Vector4) Vector4 :=
  ⟨coordinate, (Pi.single index (1 : Real) : Vector4)⟩

private theorem coordinateBasisTangentInput_contMDiff (index : Index4) :
    ContMDiff (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4).tangent ∞
      (coordinateBasisTangentInput index) := by
  change ContMDiff (modelWithCornersSelf Real Vector4)
    (modelWithCornersSelf Real Vector4).tangent ∞
    ((tangentBundleModelSpaceDiffeomorph
        (modelWithCornersSelf Real Vector4) (⊤ : ℕ∞)).symm ∘
      fun coordinate : Vector4 =>
        (coordinate, (Pi.single index (1 : Real) : Vector4)))
  have hPair : ContMDiff (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real (Vector4 × Vector4)) ∞
      (fun coordinate : Vector4 =>
        (coordinate, (Pi.single index (1 : Real) : Vector4))) :=
    (contMDiff_id
      (I := modelWithCornersSelf Real Vector4) (n := ∞)).prodMk_space
      (contMDiff_const
        (I := modelWithCornersSelf Real Vector4)
        (I' := modelWithCornersSelf Real Vector4)
        (n := ∞) (c := (Pi.single index (1 : Real) : Vector4)))
  rw [modelWithCornersSelf_prod] at hPair
  exact (tangentBundleModelSpaceDiffeomorph
      (modelWithCornersSelf Real Vector4) (⊤ : ℕ∞)).symm.contMDiff.comp
    hPair

private theorem coordinateFrame_contMDiff
    (coordinateMap : Vector4 → EffectiveQuotient period hPeriod)
    (hMap : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap)
    (index : Index4) :
    ContMDiff (modelWithCornersSelf Real Vector4)
      coverModelWithCorners.tangent ∞
      (fun coordinate =>
        (⟨coordinateMap coordinate,
          coordinateFrame period hPeriod coordinateMap hMap coordinate index⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod))) := by
  have hTangent := hMap.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)
  have hComposition := hTangent.comp
    (coordinateBasisTangentInput_contMDiff index)
  change ContMDiff (modelWithCornersSelf Real Vector4)
    coverModelWithCorners.tangent ∞
    (fun coordinate =>
      (⟨coordinateMap coordinate,
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          coordinateMap coordinate
            (Pi.single index (1 : Real) : Vector4)⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod))) at hComposition
  simpa only [coordinateFrame_eq_mfderiv] using hComposition

private theorem tensorCoefficient_contDiff
    (coordinateMap : Vector4 → EffectiveQuotient period hPeriod)
    (hMap : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      tensor.tensor (coordinateMap coordinate)
        (coordinateFrame period hPeriod coordinateMap hMap coordinate first)
        (coordinateFrame period hPeriod coordinateMap hMap coordinate second)) := by
  have hTensor := tensor.tensor.contMDiff.comp hMap.contMDiff
  have hApplied := ContMDiff.clm_bundle_apply₂
    (𝕜 := Real) (B := EffectiveQuotient period hPeriod) (M := Vector4)
    (IM := modelWithCornersSelf Real Vector4) (IB := coverModelWithCorners)
    (F₁ := CoverCoordinates) (F₂ := CoverCoordinates) (F₃ := Real)
    (E₁ := fun point => TangentSpace coverModelWithCorners point)
    (E₂ := fun point => TangentSpace coverModelWithCorners point)
    (E₃ := fun _ : EffectiveQuotient period hPeriod => Real)
    (b := coordinateMap)
    (ψ := fun coordinate => tensor.tensor (coordinateMap coordinate))
    (v := fun coordinate =>
      coordinateFrame period hPeriod coordinateMap hMap coordinate first)
    (w := fun coordinate =>
      coordinateFrame period hPeriod coordinateMap hMap coordinate second)
    hTensor
    (coordinateFrame_contMDiff period hPeriod coordinateMap hMap first)
    (coordinateFrame_contMDiff period hPeriod coordinateMap hMap second)
  have hCoordinates :=
    ((trivializationAt Real
        (Bundle.Trivial (EffectiveQuotient period hPeriod) Real)
        (coordinateMap 0)).contMDiff_iff (fun _ => by simp)).1 hApplied
  rw [← contMDiff_iff_contDiff]
  simpa [Bundle.Trivial.trivialization, Bundle.Trivial.homeomorphProd] using
    hCoordinates.2

/-- Every total smooth local diffeomorphism from `R^4` supplies the complete
holonomic frame package used by the local Levi--Civita gate. -/
def smoothHolonomicFrameChart4OfLocalDiffeomorph
    (coordinateMap : Vector4 → EffectiveQuotient period hPeriod)
    (hMap : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap) :
    SmoothHolonomicFrameChart4 period hPeriod where
  coordinateMap := coordinateMap
  coordinateMap_contMDiff := hMap.contMDiff
  frame := coordinateFrame period hPeriod coordinateMap hMap
  frame_eq_coordinateDerivative :=
    coordinateFrame_eq_mfderiv period hPeriod coordinateMap hMap
  frame_contMDiff := coordinateFrame_contMDiff period hPeriod coordinateMap hMap
  tensorCoefficient_contDiff :=
    tensorCoefficient_contDiff period hPeriod coordinateMap hMap

private def coverExtChartPartialDiffeomorph
    (anchor : EffectiveCover period hPeriod) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates)
      (EffectiveCover period hPeriod) CoverCoordinates ∞ where
  toPartialEquiv := extChartAt coverModelWithCorners anchor
  open_source := isOpen_extChartAt_source (I := coverModelWithCorners) anchor
  open_target := isOpen_extChartAt_target (I := coverModelWithCorners) anchor
  contMDiffOn_toFun := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
      (I := coverModelWithCorners) (n := ∞) (x := anchor)
  contMDiffOn_invFun :=
    contMDiffOn_extChartAt_symm
      (I := coverModelWithCorners) (n := ∞) anchor

private def localDiffeomorphOfLE
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [TopologicalSpace H] [TopologicalSpace H']
    (I : ModelWithCorners Real E H) (J : ModelWithCorners Real F H')
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {m n : WithTop ℕ∞} (hmn : m ≤ n) {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) :
    IsLocalDiffeomorph I J m f := by
  intro point
  rcases hf point with ⟨localChart, hPoint, hEq⟩
  exact
    ⟨{ toPartialEquiv := localChart.toPartialEquiv
       open_source := localChart.open_source
       open_target := localChart.open_target
       contMDiffOn_toFun := localChart.contMDiffOn_toFun.of_le hmn
       contMDiffOn_invFun := localChart.contMDiffOn_invFun.of_le hmn },
      hPoint, hEq⟩

private def ballQuotientCoordinateMap
    (anchor : EffectiveCover period hPeriod)
    {center : CoverCoordinates} {radius : Real}
    (parametrization : TotalR4BallParametrization center radius) :
    Vector4 → EffectiveQuotient period hPeriod :=
  fun coordinate =>
    mappingTorusMk (sphereData period hPeriod)
      ((extChartAt coverModelWithCorners anchor).symm
        (parametrization.toFun coordinate))

private theorem ballQuotientCoordinateMap_isLocalDiffeomorph
    (anchor : EffectiveCover period hPeriod)
    {center : CoverCoordinates} {radius : Real}
    (parametrization : TotalR4BallParametrization center radius)
    (hBall : Metric.ball center radius ⊆
      (extChartAt coverModelWithCorners anchor).target) :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞
      (ballQuotientCoordinateMap period hPeriod anchor parametrization) := by
  intro coordinate
  have hRange : parametrization.toFun coordinate ∈ Metric.ball center radius := by
    rw [← parametrization.range_eq_ball]
    exact Set.mem_range_self coordinate
  have hChart : IsLocalDiffeomorphAt
      (modelWithCornersSelf Real CoverCoordinates) coverModelWithCorners ∞
      (extChartAt coverModelWithCorners anchor).symm
      (parametrization.toFun coordinate) := by
    exact PartialDiffeomorph.isLocalDiffeomorphAt
      (I := modelWithCornersSelf Real CoverCoordinates)
      (J := coverModelWithCorners)
      (M := CoverCoordinates) (N := EffectiveCover period hPeriod)
      (n := ∞)
      (coverExtChartPartialDiffeomorph period hPeriod anchor).symm
      (hBall hRange)
  have hFirst : IsLocalDiffeomorphAt
      (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞
      ((extChartAt coverModelWithCorners anchor).symm ∘
        parametrization.toFun) coordinate := by
    exact IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real Vector4)
      (J := modelWithCornersSelf Real CoverCoordinates)
      (K := coverModelWithCorners)
      (M := Vector4) (N := CoverCoordinates)
      (P := EffectiveCover period hPeriod) (n := ∞)
      (parametrization.isLocalDiffeomorph coordinate) hChart
  have hProjection := localDiffeomorphOfLE coverModelWithCorners
    coverModelWithCorners (m := ∞) (n := ω) (by simp)
      (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
  rw [show instChartedSpaceCoverModelEffectiveQuotient period hPeriod =
    reflectedSphereQuotientChartedSpace period hPeriod by rfl]
  change IsLocalDiffeomorphAt
    (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞
    (fun x => mappingTorusMk (sphereData period hPeriod)
      ((extChartAt coverModelWithCorners anchor).symm
        (parametrization.toFun x))) coordinate
  simpa only [Function.comp_def] using
    IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real Vector4)
      (J := coverModelWithCorners) (K := coverModelWithCorners)
      (M := Vector4) (N := EffectiveCover period hPeriod)
      (P := EffectiveQuotient period hPeriod) (n := ∞)
      hFirst (hProjection
        ((extChartAt coverModelWithCorners anchor).symm
          (parametrization.toFun coordinate)))

private theorem ballQuotientCoordinateMap_zero
    (anchor : EffectiveCover period hPeriod) {radius : Real}
    (parametrization : TotalR4BallParametrization
      (extChartAt coverModelWithCorners anchor anchor) radius) :
    ballQuotientCoordinateMap period hPeriod anchor parametrization 0 =
      mappingTorusMk (sphereData period hPeriod) anchor := by
  rw [ballQuotientCoordinateMap, parametrization.at_zero]
  rw [(extChartAt coverModelWithCorners anchor).left_inv
    (mem_extChartAt_source anchor)]

/-- The quotient local diffeomorphism closes the chart-through-every-point
gate as soon as the standard total `R^4` ball parametrization is supplied. -/
theorem canonicalHolonomicChartThroughEveryPoint_of_totalR4BallParametrizations
    (hParametrizations : TotalR4BallParametrizationsExist) :
    CanonicalHolonomicChartThroughEveryPoint period hPeriod := by
  intro point
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  let center := extChartAt coverModelWithCorners anchor anchor
  obtain ⟨radius, hRadius, hBall⟩ := Metric.isOpen_iff.1
    (isOpen_extChartAt_target (I := coverModelWithCorners) anchor) center
      (mem_extChartAt_target (I := coverModelWithCorners) anchor)
  let parametrization := Classical.choice
    (hParametrizations center radius hRadius)
  let coordinateMap :=
    ballQuotientCoordinateMap period hPeriod anchor parametrization
  have hCoordinateMap : IsLocalDiffeomorph
      (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞ coordinateMap :=
    ballQuotientCoordinateMap_isLocalDiffeomorph period hPeriod anchor
      parametrization hBall
  let patch := smoothHolonomicFrameChart4OfLocalDiffeomorph
    period hPeriod coordinateMap hCoordinateMap
  refine ⟨patch, 0, ?_⟩
  exact ballQuotientCoordinateMap_zero period hPeriod anchor parametrization

end

end P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D
end JanusFormal
