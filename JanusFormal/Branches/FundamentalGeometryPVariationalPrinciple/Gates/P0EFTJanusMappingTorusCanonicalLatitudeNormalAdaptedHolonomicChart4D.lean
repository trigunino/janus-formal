import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D

/-!
# Holonomic charts adapted to the canonical latitude normal
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeNormalAdaptedHolonomicChart4D

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def lineBasis (vector : Vector4) (hVector : vector ≠ 0) :
    Module.Basis Unit Real (Real ∙ vector) :=
  FiniteDimensional.basisSingleton Unit (finrank_span_singleton hVector)
    ⟨vector, Submodule.mem_span_singleton_self vector⟩ (by
      intro hZero
      apply hVector
      exact congrArg Subtype.val hZero)

private def lineEquiv (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) :
    (Real ∙ first) ≃ₗ[Real] (Real ∙ second) :=
  (lineBasis first hFirst).equiv (lineBasis second hSecond) (Equiv.refl Unit)

private theorem lineEquiv_first (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) :
    lineEquiv first second hFirst hSecond
        ⟨first, Submodule.mem_span_singleton_self first⟩ =
      ⟨second, Submodule.mem_span_singleton_self second⟩ := by
  have hSource :
      (⟨first, Submodule.mem_span_singleton_self first⟩ : Real ∙ first) =
        lineBasis first hFirst () := by
    apply Subtype.ext
    simp [lineBasis]
  rw [hSource]
  apply Subtype.ext
  unfold lineEquiv
  rw [Module.Basis.equiv_apply]
  simp [lineBasis]

private def linearEquivSending (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) : Vector4 ≃ₗ[Real] Vector4 :=
  Classical.choose
    (Submodule.exists_linearEquiv_restrict_eq
      (lineEquiv first second hFirst hSecond))

private theorem linearEquivSending_first (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) :
    linearEquivSending first second hFirst hSecond first = second := by
  let source : Real ∙ first :=
    ⟨first, Submodule.mem_span_singleton_self first⟩
  have hRestrict := Classical.choose_spec
    (Submodule.exists_linearEquiv_restrict_eq
      (lineEquiv first second hFirst hSecond)) source
  rw [lineEquiv_first first second hFirst hSecond] at hRestrict
  exact hRestrict.symm

private def continuousLinearEquivSending (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) : Vector4 ≃L[Real] Vector4 :=
  (linearEquivSending first second hFirst hSecond).toContinuousLinearEquiv

private theorem continuousLinearEquivSending_first (first second : Vector4)
    (hFirst : first ≠ 0) (hSecond : second ≠ 0) :
    continuousLinearEquivSending first second hFirst hSecond first = second :=
  linearEquivSending_first first second hFirst hSecond

private theorem continuousLinearEquiv_mfderiv
    (equivalence : Vector4 ≃L[Real] Vector4) (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) equivalence coordinate =
        equivalence.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact equivalence.toContinuousLinearMap.hasFDerivAt.fderiv

private theorem firstBasisVector_ne_zero :
    (Pi.single (0 : Fin 4) (1 : Real) : Vector4) ≠ 0 := by
  intro hZero
  have := congrFun hZero 0
  simpa using this

/-- A total holonomic chart centered at a canonical collar point whose
zeroth coordinate vector is exactly the canonical latitude normal. -/
structure NormalAdaptedHolonomicChart
    (base : CanonicalLatitudeBase) (normal : Real) where
  coordinateMap : Vector4 → EffectiveQuotient period hPeriod
  isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap
  at_zero : coordinateMap 0 =
    quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base) normal
  derivative_normal :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      coordinateMap 0 (Pi.single 0 1) =
        canonicalLatitudeNormalVector period hPeriod base normal

/-- Every canonical latitude point admits a total normal-adapted holonomic
chart; no overlap or field equation is assumed. -/
theorem normalAdaptedHolonomicChart_exists
    (base : CanonicalLatitudeBase) (normal : Real) :
    Nonempty (NormalAdaptedHolonomicChart period hPeriod base normal) := by
  let anchor := normalLatitudeCover period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal
  let center := extChartAt coverModelWithCorners anchor anchor
  obtain ⟨radius, hRadius, hBall⟩ := Metric.isOpen_iff.1
    (isOpen_extChartAt_target (I := coverModelWithCorners) anchor) center
      (mem_extChartAt_target (I := coverModelWithCorners) anchor)
  let parametrization := totalR4BallParametrization center radius hRadius
  let baseMap := realizedBallQuotientCoordinateMap period hPeriod anchor parametrization
  have hBase : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ baseMap :=
    realizedBallQuotientCoordinateMap_isLocalDiffeomorph period hPeriod anchor
      parametrization hBall
  let baseDerivative :=
    hBase.mfderivToContinuousLinearEquiv (by simp) 0
  let targetPreimage := baseDerivative.symm
    (canonicalLatitudeNormalVector period hPeriod base normal)
  have hNormal : canonicalLatitudeNormalVector period hPeriod base normal ≠ 0 := by
    intro hZero
    have hUnit := intrinsicMetric_canonicalLatitudeNormalVector_self
      period hPeriod base normal
    rw [hZero] at hUnit
    simpa using hUnit
  have hPreimage : targetPreimage ≠ 0 := by
    intro hZero
    apply hNormal
    calc
      canonicalLatitudeNormalVector period hPeriod base normal =
          baseDerivative targetPreimage :=
        (baseDerivative.apply_symm_apply _).symm
      _ = 0 := by rw [hZero, map_zero]
  let reparametrization := continuousLinearEquivSending
    (Pi.single 0 1 : Vector4) targetPreimage firstBasisVector_ne_zero hPreimage
  let coordinateMap := baseMap ∘ reparametrization
  have hReparametrization : IsLocalDiffeomorph
      (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) ∞ reparametrization :=
    reparametrization.toDiffeomorph.isLocalDiffeomorph
  have hCoordinateMap : IsLocalDiffeomorph
      (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞ coordinateMap :=
    fun coordinate => IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real Vector4)
      (J := modelWithCornersSelf Real Vector4)
      (K := coverModelWithCorners)
      (M := Vector4) (N := Vector4)
      (P := EffectiveQuotient period hPeriod) (n := ∞)
      (hReparametrization coordinate) (hBase (reparametrization coordinate))
  refine ⟨{
    coordinateMap := coordinateMap
    isLocalDiffeomorph := hCoordinateMap
    at_zero := ?_
    derivative_normal := ?_ }⟩
  · change baseMap (reparametrization 0) = _
    rw [map_zero]
    change baseMap 0 = mappingTorusMk (reflectedSphereData period hPeriod) anchor
    simpa [center, baseMap] using
      (realizedBallQuotientCoordinateMap_zero period hPeriod anchor parametrization)
  · have hChain := mfderiv_comp_apply_of_eq
      (I := modelWithCornersSelf Real Vector4)
      (I' := modelWithCornersSelf Real Vector4)
      (I'' := coverModelWithCorners)
      (f := reparametrization) (g := baseMap)
      (x := (0 : Vector4)) (y := (0 : Vector4))
      (hBase.mdifferentiable (by simp) 0)
      (hReparametrization.mdifferentiable (by simp) 0)
      (map_zero reparametrization)
      (Pi.single 0 1 : Vector4)
    have hReparametrizationZero : reparametrization 0 = 0 := map_zero _
    have hReparametrizationBasis :
        reparametrization (Pi.single 0 1 : Vector4) = targetPreimage := by
      dsimp [reparametrization]
      exact continuousLinearEquivSending_first _ _ _ _
    have hMFDerivBasis :
        mfderiv (modelWithCornersSelf Real Vector4)
            (modelWithCornersSelf Real Vector4) reparametrization 0
              (Pi.single 0 1 : Vector4) = targetPreimage := by
      rw [continuousLinearEquiv_mfderiv]
      exact hReparametrizationBasis
    change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        coordinateMap 0 (Pi.single 0 1) = _
    rw [hChain]
    rw [hMFDerivBasis]
    change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      baseMap 0 targetPreimage = _
    rw [← hBase.mfderivToContinuousLinearEquiv_coe (by simp) 0]
    exact baseDerivative.apply_symm_apply _

end
end P0EFTJanusMappingTorusCanonicalLatitudeNormalAdaptedHolonomicChart4D
end JanusFormal
