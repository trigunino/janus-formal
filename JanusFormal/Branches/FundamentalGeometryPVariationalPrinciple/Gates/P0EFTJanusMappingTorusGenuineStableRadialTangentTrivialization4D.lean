import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusStableRadialTangentTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

/-!
# Genuine pointwise stable radial tangent equivalence on the D8 cover

The stable radial equivalence is precomposed with the derivative of the
actual sphere diffeomorphism and with the derivative of the genuine cover
product diffeomorphism.  Its application is therefore expressed by the true
ambient immersion derivative, rather than only by an abstract product model.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
open P0EFTJanusMappingTorusStableRadialTangentTrivialization4D
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev SphereCoordinates := EuclideanSpace Real (Fin 3)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- The homeomorphism used to define `UnitThreeSphere`, with its genuine
smooth structures on source and target. -/
def unitThreeSphereDiffeomorph :
    UnitThreeSphere ≃ₘ⟮(𝓡 3), (𝓡 3)⟯ StandardSphere where
  toEquiv := unitThreeSphereHomeomorph.toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph

/-- Derivative equivalence of the actual sphere diffeomorphism. -/
def sphereDiffeomorphDerivativeEquiv
    (point : UnitThreeSphere) :
    SphereCoordinates ≃L[Real] SphereCoordinates :=
  (unitThreeSphereDiffeomorph).mfderivToContinuousLinearEquiv (by simp) point

/-- The derivative of the actual ambient sphere map factors through the
standard-sphere inclusion derivative. -/
theorem sphereAmbientDerivative_factor
    (point : UnitThreeSphere) :
    mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point =
      (sphereInclusionDerivative point).comp
        (sphereDiffeomorphDerivativeEquiv point :
          SphereCoordinates →L[Real] SphereCoordinates) := by
  have hInclusionSmooth : ContMDiff (𝓡 3) 𝓘(Real, EuclideanR4) ∞
      ((↑) : StandardSphere → EuclideanR4) :=
    contMDiff_coe_sphere
  have hInclusion : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point) :=
    hInclusionSmooth.mdifferentiableAt (by simp)
  have hSphere : MDifferentiableAt (𝓡 3) (𝓡 3)
      unitThreeSphereHomeomorph point :=
    (unitThreeSphereDiffeomorph).mdifferentiable (by simp) point
  change mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point =
    (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4)
      ((↑) : StandardSphere → EuclideanR4)
      (unitThreeSphereHomeomorph point)).comp
      (mfderiv (𝓡 3) (𝓡 3) unitThreeSphereHomeomorph point)
  have hMap : sphereAmbientMap =
      ((↑) : StandardSphere → EuclideanR4) ∘
        unitThreeSphereHomeomorph := by
    rfl
  rw [hMap]
  exact mfderiv_comp point hInclusion hSphere

/-- Stable radial equivalence after inserting the derivative of the genuine
sphere diffeomorphism. -/
def genuineRadialProductEquiv
    (point : EffectiveCover period hPeriod) :
    CoverCoordinates ≃L[Real] EuclideanR4 :=
  (ContinuousLinearEquiv.prodCongr
      (sphereDiffeomorphDerivativeEquiv point.fiber)
      (ContinuousLinearEquiv.refl Real Real)).trans
    (stableRadialTangentEquiv period hPeriod point)

theorem genuineRadialProductEquiv_apply
    (point : EffectiveCover period hPeriod) (input : CoverCoordinates) :
    genuineRadialProductEquiv period hPeriod point input =
      sphereInclusionDerivative point.fiber
          (sphereDiffeomorphDerivativeEquiv point.fiber input.1) +
        input.2 • sphereAmbientMap point.fiber := by
  change stableRadialTangentEquiv period hPeriod point
      (sphereDiffeomorphDerivativeEquiv point.fiber input.1, input.2) = _
  rw [stableRadialTangentEquiv_apply, stableRadialTangentMap_apply]

/-- Pointwise continuous-linear equivalence on the genuine tangent fiber of
the actual smooth D8 cover.  Smooth dependence on the base is not asserted. -/
def genuineStableRadialTangentEquiv
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real] EuclideanR4 :=
  (coverProductDerivativeEquiv period hPeriod point).trans
    (genuineRadialProductEquiv period hPeriod point)

/-- Exact application formula through the true ambient immersion
derivative. -/
theorem genuineStableRadialTangentEquiv_apply
    (point : EffectiveCover period hPeriod)
    (vector : CoverTangent period hPeriod point) :
    genuineStableRadialTangentEquiv period hPeriod point vector =
      (coverAmbientDerivative period hPeriod point vector).1 +
        (coverAmbientDerivative period hPeriod point vector).2 •
          sphereAmbientMap point.fiber := by
  change genuineRadialProductEquiv period hPeriod point
      (coverProductDerivativeEquiv period hPeriod point vector) = _
  rw [genuineRadialProductEquiv_apply,
    coverAmbientDerivative_apply_product]
  rw [sphereAmbientDerivative_factor]
  rfl

/-- On the actual throat, the canonical latitude normal is the reflected
ambient basis vector in the genuine radial frame. -/
theorem genuineStableRadialTangentEquiv_latitudeNormal
    (anchor : EffectiveThroatCover period hPeriod) :
    genuineStableRadialTangentEquiv period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) =
      EuclideanSpace.single (0 : Fin 4) 1 := by
  rw [genuineStableRadialTangentEquiv_apply,
    coverAmbientDerivative_latitudeNormal]
  simp

/-- The genuine radial frame transforms by the spatial reflection under one
actual deck turn. -/
theorem genuineStableRadialTangentEquiv_deckGenerator
    (point : EffectiveCover period hPeriod)
    (vector : CoverTangent period hPeriod point) :
    genuineStableRadialTangentEquiv period hPeriod ((1 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point vector) =
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        (genuineStableRadialTangentEquiv period hPeriod point vector) := by
  rw [genuineStableRadialTangentEquiv_apply,
    genuineStableRadialTangentEquiv_apply]
  have hDerivative := congrArg (fun derivative => derivative vector)
    (coverAmbientDerivative_deckGenerator_natural period hPeriod point)
  simp only [ContinuousLinearMap.comp_apply,
    coverAmbientDeckGeneratorLinear_apply] at hDerivative
  rw [hDerivative]
  have hSphere :
      sphereAmbientMap (((1 : Int) +ᵥ point).fiber) =
        P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
          (sphereAmbientMap point.fiber) := by
    rw [show ((1 : Int) +ᵥ point).fiber = sphereReflection point.fiber by
      simp [sphereData, reflectedSphereData]]
    exact unitSphereEuclideanPoint_reflection point.fiber
  rw [hSphere, map_add, map_smul]

/-- The exact ambient operator carried by an arbitrary deck winding.  Integer
powers are essential here: negative windings use the inverse reflection, not
a separately postulated action. -/
def genuineStableRadialDeckOperator (winding : Int) :
    EuclideanR4 ≃L[Real] EuclideanR4 :=
  euclideanReflection.toContinuousLinearEquiv ^ winding

private abbrev ambientReflection : EuclideanR4 ≃L[Real] EuclideanR4 :=
  euclideanReflection.toContinuousLinearEquiv

private theorem ambientReflection_mul_self :
    ambientReflection * ambientReflection = 1 := by
  apply ContinuousLinearEquiv.ext
  funext vector
  exact euclideanReflection_involutive vector

private theorem ambientReflection_inv :
    ambientReflection⁻¹ = ambientReflection :=
  inv_eq_of_mul_eq_one_right ambientReflection_mul_self

private theorem genuineStableRadialDeckOperator_add_one_apply
    (winding : Int) (vector : EuclideanR4) :
    genuineStableRadialDeckOperator (winding + 1) vector =
      ambientReflection
        (genuineStableRadialDeckOperator winding vector) := by
  change (ambientReflection ^ (winding + 1)) vector =
    ambientReflection ((ambientReflection ^ winding) vector)
  rw [show winding + 1 = 1 + winding by omega, zpow_one_add]
  rfl

private theorem genuineStableRadialDeckOperator_sub_one_apply
    (winding : Int) (vector : EuclideanR4) :
    genuineStableRadialDeckOperator (winding - 1) vector =
      ambientReflection
        (genuineStableRadialDeckOperator winding vector) := by
  change (ambientReflection ^ (winding - 1)) vector =
    ambientReflection ((ambientReflection ^ winding) vector)
  rw [show winding - 1 = (-1 : Int) + winding by omega, zpow_add]
  simp only [zpow_neg, zpow_one, ambientReflection_inv]
  rfl

private theorem mfderiv_deck_add
    (first second : Int) (point : EffectiveCover period hPeriod) :
    mfderiv coverModelWithCorners coverModelWithCorners
        ((first + second) +ᵥ ·) point =
      (mfderiv coverModelWithCorners coverModelWithCorners
        (first +ᵥ ·) (second +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (second +ᵥ ·) point) := by
  have hFirst : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (first +ᵥ ·) (second +ᵥ point) :=
    (reflectedSphereCover_deck_contMDiff period hPeriod first).mdifferentiableAt
      (by simp)
  have hSecond : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (second +ᵥ ·) point :=
    (reflectedSphereCover_deck_contMDiff period hPeriod second).mdifferentiableAt
      (by simp)
  calc
    _ = mfderiv coverModelWithCorners coverModelWithCorners
        ((first +ᵥ ·) ∘ (second +ᵥ ·)) point := by
      apply mfderiv_congr
      funext current
      exact add_vadd first second current
    _ = _ := mfderiv_comp point hFirst hSecond

/-- The genuine stable radial frame is natural under every integer deck
winding.  The proof derives both positive and negative windings from the
actual generator derivative; the latter use involutivity of the same ambient
reflection. -/
theorem genuineStableRadialTangentEquiv_deckWinding
    (winding : Int) (point : EffectiveCover period hPeriod)
    (vector : CoverTangent period hPeriod point) :
    genuineStableRadialTangentEquiv period hPeriod (winding +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point vector) =
      genuineStableRadialDeckOperator winding
        (genuineStableRadialTangentEquiv period hPeriod point vector) := by
  let motive : Int → Prop := fun current =>
    genuineStableRadialTangentEquiv period hPeriod (current +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (current +ᵥ ·) point vector) =
      genuineStableRadialDeckOperator current
        (genuineStableRadialTangentEquiv period hPeriod point vector)
  change motive winding
  refine Int.inductionOn' winding 0 ?_ (fun current _ ih => ?_)
      (fun current _ ih => ?_)
  · change genuineStableRadialTangentEquiv period hPeriod ((0 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((0 : Int) +ᵥ ·) point vector) = _
    have hZero : ((0 : Int) +ᵥ · : EffectiveCover period hPeriod →
        EffectiveCover period hPeriod) = id := by
      funext current
      simp
    rw [show (0 : Int) +ᵥ point = point by simp]
    rw [hZero, mfderiv_id]
    rfl
  · have hGenerator :=
      genuineStableRadialTangentEquiv_deckGenerator period hPeriod
        (current +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (current +ᵥ ·) point vector)
    have hDerivative := congrArg (fun derivative => derivative vector)
      (mfderiv_deck_add period hPeriod 1 current point)
    have hDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + current) +ᵥ ·) point vector =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) (current +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                (current +ᵥ ·) point vector) :=
      hDerivative
    rw [← hDerivative'] at hGenerator
    rw [← add_vadd] at hGenerator
    have hStep : motive (current + 1) := by
      rw [show current + 1 = 1 + current by omega]
      rw [ih] at hGenerator
      have hOperator :=
        genuineStableRadialDeckOperator_add_one_apply current
          (genuineStableRadialTangentEquiv period hPeriod point vector)
      rw [show current + 1 = 1 + current by omega] at hOperator
      exact hGenerator.trans
        hOperator.symm
    exact hStep
  · have hGenerator :=
      genuineStableRadialTangentEquiv_deckGenerator period hPeriod
        ((current - 1) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((current - 1) +ᵥ ·) point vector)
    have hDerivative := congrArg (fun derivative => derivative vector)
      (mfderiv_deck_add period hPeriod 1 (current - 1) point)
    have hDerivative' :
        mfderiv coverModelWithCorners coverModelWithCorners
            ((1 + (current - 1)) +ᵥ ·) point vector =
          mfderiv coverModelWithCorners coverModelWithCorners
            ((1 : Int) +ᵥ ·) ((current - 1) +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                ((current - 1) +ᵥ ·) point vector) :=
      hDerivative
    rw [← hDerivative'] at hGenerator
    rw [← add_vadd] at hGenerator
    have hIndex : 1 + (current - 1) = current := by omega
    rw [hIndex] at hGenerator
    have hReflected := congrArg (fun output => ambientReflection output) hGenerator
    have hBack :
        genuineStableRadialTangentEquiv period hPeriod
            ((current - 1) +ᵥ point)
            (mfderiv coverModelWithCorners coverModelWithCorners
              ((current - 1) +ᵥ ·) point vector) =
          ambientReflection
            (genuineStableRadialTangentEquiv period hPeriod
              (current +ᵥ point)
              (mfderiv coverModelWithCorners coverModelWithCorners
                (current +ᵥ ·) point vector)) := by
      rw [← euclideanReflection_involutive
        (genuineStableRadialTangentEquiv period hPeriod
          ((current - 1) +ᵥ point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            ((current - 1) +ᵥ ·) point vector))]
      exact hReflected.symm
    rw [ih] at hBack
    exact hBack.trans
      (genuineStableRadialDeckOperator_sub_one_apply current
        (genuineStableRadialTangentEquiv period hPeriod point vector)).symm

end

end P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
end JanusFormal
