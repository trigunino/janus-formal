import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Intrinsic smooth Lorentz tensor on the D8 cover

The cover is immersed in the ambient product `ℝ⁴ × ℝ`.  Its derivative is
packaged as a smooth bundle-hom section; the product Minkowski form is then
pulled back through that derivative.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Set Bundle Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothPTInvolution

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private abbrev AmbientCoordinates := ModelProd EuclideanR4 Real

private instance ambientNormedAddCommGroup :
    NormedAddCommGroup AmbientCoordinates :=
  inferInstanceAs (NormedAddCommGroup (EuclideanR4 × Real))

private instance ambientNormedSpace : NormedSpace Real AmbientCoordinates :=
  inferInstanceAs (NormedSpace Real (EuclideanR4 × Real))

private abbrev AmbientModel := AmbientCoordinates
private abbrev ambientModelWithCorners :
    ModelWithCorners Real AmbientCoordinates AmbientModel :=
  𝓘(Real, AmbientCoordinates)

def sphereAmbientMap (point : UnitThreeSphere) : EuclideanR4 :=
  (unitThreeSphereHomeomorph point).1

theorem sphereAmbientMap_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, EuclideanR4) ∞ sphereAmbientMap := by
  exact contMDiff_coe_sphere.comp
    (chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
      unitThreeSphereHomeomorph)

/-- Global smooth immersion map of the packaged cover into `ℝ⁴ × ℝ`. -/
def coverAmbientMap (point : EffectiveCover period hPeriod) :
    AmbientCoordinates :=
  (sphereAmbientMap point.fiber, point.time)

theorem coverAmbientMap_contMDiff :
    ContMDiff coverModelWithCorners ambientModelWithCorners ∞
      (coverAmbientMap period hPeriod) := by
  have hCoverToProduct :=
    chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (sphereData period hPeriod))
  have hFiber : ContMDiff coverModelWithCorners (𝓡 3) ∞
      (fun point : EffectiveCover period hPeriod => point.fiber) := by
    simpa using hCoverToProduct.fst
  have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveCover period hPeriod => point.time) := by
    simpa using hCoverToProduct.snd
  exact (sphereAmbientMap_contMDiff.comp hFiber).prodMk_space hTime

private abbrev CoverIntrinsicTangent
    (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CoverAmbientFiber :=
  Bundle.Trivial (EffectiveCover period hPeriod) AmbientCoordinates

private abbrev CoverAmbientHomFiber
    (point : EffectiveCover period hPeriod) :=
  CoverIntrinsicTangent period hPeriod point →L[Real]
    CoverAmbientFiber period hPeriod point

/-- The true manifold derivative of the ambient cover immersion. -/
def coverAmbientDerivative
    (point : EffectiveCover period hPeriod) :
    CoverAmbientHomFiber period hPeriod point :=
  mfderiv coverModelWithCorners ambientModelWithCorners
    (coverAmbientMap period hPeriod) point

/-- Product-coordinate derivative of the cover chart.  This public map keeps
downstream calculations away from the private ambient model instances. -/
def coverProductDerivative
    (point : EffectiveCover period hPeriod) :
    CoverIntrinsicTangent period hPeriod point →L[Real] CoverCoordinates :=
  mfderiv coverModelWithCorners coverModelWithCorners
    (coverHomeomorphProd (sphereData period hPeriod)) point

private def productAmbientMap (point : UnitThreeSphere × Real) :
    AmbientCoordinates :=
  (sphereAmbientMap point.1, point.2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Factorization of the true ambient derivative through the public product
coordinates of the mapping-torus cover. -/
theorem coverAmbientDerivative_factor
    (point : EffectiveCover period hPeriod) :
    coverAmbientDerivative period hPeriod point =
      ((mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point.fiber).prodMap
        (ContinuousLinearMap.id Real Real)).comp
        (coverProductDerivative period hPeriod point) := by
  have hSphere : MDifferentiableAt (𝓡 3) 𝓘(Real, EuclideanR4)
      sphereAmbientMap point.fiber :=
    sphereAmbientMap_contMDiff.mdifferentiableAt (by simp)
  have hTime : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (id : Real → Real) point.time :=
    mdifferentiableAt_id
  have hProduct : MDifferentiableAt coverModelWithCorners
      ambientModelWithCorners productAmbientMap (point.fiber, point.time) := by
    change MDifferentiableAt coverModelWithCorners
      𝓘(Real, EuclideanR4 × Real) (Prod.map sphereAmbientMap id)
      (point.fiber, point.time)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hSphere.prodMap hTime
  have hCover : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners
      (coverHomeomorphProd (sphereData period hPeriod)) point :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (sphereData period hPeriod))).mdifferentiableAt
        (by simp)
  have hMap : coverAmbientMap period hPeriod =
      productAmbientMap ∘
        coverHomeomorphProd (sphereData period hPeriod) := by
    rfl
  have hProductDerivative :
      mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4 × Real)
          (Prod.map sphereAmbientMap id) (point.fiber, point.time) =
        (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap
          point.fiber).prodMap (ContinuousLinearMap.id Real Real) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    rw [mfderiv_prodMap hSphere hTime, mfderiv_id]
    rfl
  rw [show coverAmbientDerivative period hPeriod point =
      mfderiv coverModelWithCorners ambientModelWithCorners
        (coverAmbientMap period hPeriod) point by rfl, hMap,
    mfderiv_comp point hProduct hCover,
    show productAmbientMap = Prod.map sphereAmbientMap id by rfl]
  change (mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4 × Real)
      (Prod.map sphereAmbientMap id) (point.fiber, point.time)).comp
      (coverProductDerivative period hPeriod point) = _
  rw [hProductDerivative]

/-- Pointwise form of `coverAmbientDerivative_factor`. -/
theorem coverAmbientDerivative_apply_product
    (point : EffectiveCover period hPeriod)
    (vector : CoverIntrinsicTangent period hPeriod point) :
    coverAmbientDerivative period hPeriod point vector =
      (mfderiv (𝓡 3) 𝓘(Real, EuclideanR4) sphereAmbientMap point.fiber
          (coverProductDerivative period hPeriod point vector).1,
        (coverProductDerivative period hPeriod point vector).2) := by
  rw [coverAmbientDerivative_factor]
  rfl

private def ambientTimeReverseLinear :
    AmbientCoordinates →L[Real] AmbientCoordinates :=
  (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl Real EuclideanR4)
    (ContinuousLinearEquiv.neg Real)).toContinuousLinearMap

@[simp]
private theorem ambientTimeReverseLinear_apply
    (point : AmbientCoordinates) :
    ambientTimeReverseLinear point = (point.1, -point.2) := by
  rfl

private def ambientTimeReverseMap
    (point : AmbientCoordinates) : AmbientCoordinates :=
  ambientTimeReverseLinear point

private theorem ambientTimeReverseMap_mfderiv
    (point : AmbientCoordinates) :
    mfderiv ambientModelWithCorners ambientModelWithCorners
        ambientTimeReverseMap point = ambientTimeReverseLinear := by
  rw [mfderiv_eq_fderiv]
  exact ambientTimeReverseLinear.hasFDerivAt.fderiv

/-- The true ambient immersion derivative is natural under cover time
reversal: its spatial component is fixed and its time component changes
sign.  This theorem lives here because the ambient model is intentionally
private to this gate. -/
theorem coverAmbientDerivative_timeReverse_components
    (point : EffectiveCover period hPeriod)
    (vector : CoverIntrinsicTangent period hPeriod point) :
    (coverAmbientDerivative period hPeriod
        (timeReverseCover (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (timeReverseCover (sphereData period hPeriod)) point vector)).1 =
        (coverAmbientDerivative period hPeriod point vector).1 ∧
      (coverAmbientDerivative period hPeriod
        (timeReverseCover (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (timeReverseCover (sphereData period hPeriod)) point vector)).2 =
        -(coverAmbientDerivative period hPeriod point vector).2 := by
  have hCover := coverAmbientMap_contMDiff period hPeriod
  have hReverse := reflectedSphereCover_timeReverse_contMDiff period hPeriod
  have hAmbient : ContMDiff ambientModelWithCorners ambientModelWithCorners ∞
      ambientTimeReverseMap :=
    ambientTimeReverseLinear.contDiff.contMDiff
  have hMaps :
      coverAmbientMap period hPeriod ∘
          timeReverseCover (sphereData period hPeriod) =
        ambientTimeReverseMap ∘ coverAmbientMap period hPeriod := by
    funext current
    apply Prod.ext <;> rfl
  have hLeftMap := mfderiv_comp point
    (hCover.mdifferentiable (by simp)
      (timeReverseCover (sphereData period hPeriod) point))
    (hReverse.mdifferentiable (by simp) point)
  have hLeft := DFunLike.congr_fun hLeftMap vector
  have hRightMap := mfderiv_comp point
    (hAmbient.mdifferentiable (by simp)
      (coverAmbientMap period hPeriod point))
    (hCover.mdifferentiable (by simp) point)
  have hRight := DFunLike.congr_fun hRightMap vector
  have hDerivativeMapsMap :=
    mfderiv_congr (I := coverModelWithCorners)
      (I' := ambientModelWithCorners) (x := point) hMaps
  have hDerivativeMaps := DFunLike.congr_fun hDerivativeMapsMap vector
  have hNatural := hLeft.symm.trans (hDerivativeMaps.trans hRight)
  rw [ambientTimeReverseMap_mfderiv] at hNatural
  change coverAmbientDerivative period hPeriod
      (timeReverseCover (sphereData period hPeriod) point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (timeReverseCover (sphereData period hPeriod)) point vector) =
    ambientTimeReverseLinear
      (coverAmbientDerivative period hPeriod point vector) at hNatural
  rw [ambientTimeReverseLinear_apply] at hNatural
  constructor
  · simpa only using
      congrArg (fun current : AmbientCoordinates => current.1) hNatural
  · simpa only using
      congrArg (fun current : AmbientCoordinates => current.2) hNatural

/-- The derivative of the immersion varies smoothly as a tangent-bundle hom. -/
def coverAmbientDerivativeSection :
    ContMDiffSection coverModelWithCorners
      (CoverCoordinates →L[Real] AmbientCoordinates) ∞
      (CoverAmbientHomFiber period hPeriod) where
  toFun := coverAmbientDerivative period hPeriod
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_section]
    have hMapAt : ContMDiffAt coverModelWithCorners
        ambientModelWithCorners ∞ (coverAmbientMap period hPeriod) point :=
      coverAmbientMap_contMDiff period hPeriod point
    have hDerivative := hMapAt.mfderiv_const
      (m := ∞) (n := ∞) (by simp)
    simp only [coverAmbientDerivative, hom_trivializationAt_apply]
    convert hDerivative using 1 <;> try rfl
    funext x
    apply ContinuousLinearMap.ext
    intro vector
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl

/-- Postcomposition of the true immersion derivative by a fixed ambient
continuous linear map is again a smooth bundle-hom section. -/
def postcomposeCoverAmbientDerivativeSection
    (operator : AmbientCoordinates →L[Real] AmbientCoordinates) :
    ContMDiffSection coverModelWithCorners
      (CoverCoordinates →L[Real] AmbientCoordinates) ∞
      (CoverAmbientHomFiber period hPeriod) where
  toFun := fun point =>
    operator.comp (coverAmbientDerivative period hPeriod point)
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_section]
    have hDerivative :=
      (coverAmbientDerivativeSection period hPeriod).contMDiff point
    rw [contMDiffAt_section] at hDerivative
    have hPostcomposition : ContDiff Real ∞
        (fun derivative : CoverCoordinates →L[Real] AmbientCoordinates =>
          operator.comp derivative) :=
      contDiff_const.clm_comp contDiff_id
    have hComposition :=
      hPostcomposition.comp_contMDiffAt hDerivative
    convert hComposition using 1 <;> try rfl
    funext x
    apply ContinuousLinearMap.ext
    intro vector
    simp [hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates]
    by_cases hx : x ∈
        (trivializationAt CoverCoordinates
          (CoverIntrinsicTangent period hPeriod) point).baseSet
    · have hx' : x ∈ (chartAt CoverModel point).source := by
        simpa only [CoverIntrinsicTangent,
          TangentBundle.trivializationAt_baseSet] using hx
      rfl
    · have hx' : x ∉ (chartAt CoverModel point).source := by
        simpa only [CoverIntrinsicTangent,
          TangentBundle.trivializationAt_baseSet] using hx
      rfl

private abbrev AmbientCovector :=
  AmbientCoordinates →L[Real] Real

private abbrev CoverModelHom :=
  CoverCoordinates →L[Real] AmbientCoordinates

private abbrev CoverModelCovector :=
  CoverCoordinates →L[Real] Real

private local instance ambientCovectorNormedTopology :
    TopologicalSpace AmbientCovector :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private local instance coverModelCovectorNormedTopology :
    TopologicalSpace CoverModelCovector :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private abbrev CoverModelTensor :=
  CoverCoordinates →L[Real] CoverModelCovector

private def realRieszMap (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace Real E] :
    E →L[Real] (E →L[Real] Real) :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 fun x y => by
    change ‖inner Real x y‖ ≤ 1 * ‖x‖ * ‖y‖
    simpa using (norm_inner_le_norm (𝕜 := Real) x y)

private theorem realRieszMap_bijective (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E] : Function.Bijective (realRieszMap E) := by
  constructor
  · intro x y hxy
    apply (InnerProductSpace.toDual Real E).injective
    apply ContinuousLinearMap.ext
    intro z
    change inner Real x z = inner Real y z
    exact congrArg (fun functional => functional z) hxy
  · intro functional
    obtain ⟨x, hx⟩ := (InnerProductSpace.toDual Real E).surjective functional
    refine ⟨x, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change inner Real x z = functional z
    exact congrArg (fun covector => covector z) hx

private def realRieszEquiv (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace Real E] [CompleteSpace E]
    [FiniteDimensional Real E] : E ≃L[Real] (E →L[Real] Real) :=
  (LinearEquiv.ofBijective (realRieszMap E).toLinearMap
    (realRieszMap_bijective E)).toContinuousLinearEquiv

@[simp]
private theorem realRieszEquiv_apply (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E] [FiniteDimensional Real E] (x y : E) :
    realRieszEquiv E x y = inner Real x y := by
  rfl

private def ambientSpatialMusical :
    EuclideanR4 ≃L[Real] (EuclideanR4 →L[Real] Real) :=
  realRieszEquiv EuclideanR4

private def ambientTimeMusical :
    Real ≃L[Real] (Real →L[Real] Real) :=
  (ContinuousLinearEquiv.neg Real).trans
    (realRieszEquiv Real)

/-- Ambient product Minkowski musical equivalence. -/
private def ambientMinkowskiMusical :
    AmbientCoordinates ≃L[Real] AmbientCovector :=
  (ContinuousLinearEquiv.prodCongr ambientSpatialMusical
    ambientTimeMusical).trans (ContinuousLinearMap.coprodEquivL Real)

private def covectorPrecomposition (derivative : CoverModelHom) :
    AmbientCovector →L[Real] CoverModelCovector :=
  derivative.precomp Real

private def metricAfterDerivative (derivative : CoverModelHom) :
    CoverCoordinates →L[Real] AmbientCovector :=
  ambientMinkowskiMusical.toContinuousLinearMap.comp derivative

/-- Pull back the fixed ambient Minkowski form through one linear map. -/
private def pullbackAmbientMinkowski
    (derivative : CoverModelHom) : CoverModelTensor :=
  (covectorPrecomposition derivative).comp
    (metricAfterDerivative derivative)

private theorem pullbackAmbientMinkowski_contDiff :
    ContDiff Real ∞ pullbackAmbientMinkowski := by
  have hIdentity : ContMDiff
      (modelWithCornersSelf Real CoverModelHom)
      (modelWithCornersSelf Real CoverModelHom) ∞
      (fun derivative : CoverModelHom => derivative) :=
    contMDiff_id
  have hLeft := (hIdentity.clm_precomp (F₃ := Real)).contDiff
  have hRight : ContDiff Real ∞ metricAfterDerivative := by
    exact (contDiff_const.clm_comp contDiff_id)
  change ContDiff Real ∞ (fun derivative : CoverModelHom =>
    (derivative.precomp Real).comp
      (metricAfterDerivative derivative))
  exact hLeft.clm_comp hRight

@[simp]
private theorem pullbackAmbientMinkowski_apply
    (derivative : CoverModelHom) (first second : CoverCoordinates) :
    pullbackAmbientMinkowski derivative first second =
      inner Real (derivative first).1 (derivative second).1 -
        (derivative first).2 * (derivative second).2 := by
  change ambientMinkowskiMusical (derivative first)
    (derivative second) = _
  have hMusical : ambientMinkowskiMusical (derivative first) =
      (ambientSpatialMusical (derivative first).1).coprod
        (ambientTimeMusical (derivative first).2) := by
    rfl
  rw [hMusical]
  change (ambientSpatialMusical (derivative first).1)
      (derivative second).1 +
    (ambientTimeMusical (derivative first).2)
      (derivative second).2 = _
  simp only [ambientSpatialMusical, ambientTimeMusical,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply,
    realRieszEquiv_apply, Real.inner_apply]
  ring

private abbrev CoverIntrinsicCovector
    (point : EffectiveCover period hPeriod) :=
  CoverIntrinsicTangent period hPeriod point →L[Real] Real

private abbrev CoverIntrinsicTensorFiber
    (point : EffectiveCover period hPeriod) :=
  CoverIntrinsicTangent period hPeriod point →L[Real]
    CoverIntrinsicCovector period hPeriod point

/-- The intrinsic cover tensor obtained by pulling back the ambient product
Minkowski form through the true manifold derivative. -/
def intrinsicCoverLorentzTensorValue
    (point : EffectiveCover period hPeriod) :
    CoverIntrinsicTensorFiber period hPeriod point :=
  pullbackAmbientMinkowski (coverAmbientDerivative period hPeriod point)

/-- The ambient pullback tensor is a genuine smooth covariant two-tensor
section of the cover tangent bundle. -/
def intrinsicCoverLorentzTensor :
    ContMDiffSection coverModelWithCorners CoverModelTensor ∞
      (CoverIntrinsicTensorFiber period hPeriod) where
  toFun := intrinsicCoverLorentzTensorValue period hPeriod
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_section]
    have hDerivative :=
      (coverAmbientDerivativeSection period hPeriod).contMDiff point
    rw [contMDiffAt_section] at hDerivative
    have hPullback :=
      pullbackAmbientMinkowski_contDiff.comp_contMDiffAt hDerivative
    convert hPullback using 1 <;> try rfl
    funext x
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp [intrinsicCoverLorentzTensorValue,
      pullbackAmbientMinkowski, covectorPrecomposition,
      metricAfterDerivative, hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates]
    by_cases hx : x ∈
        (trivializationAt CoverCoordinates
          (CoverIntrinsicTangent period hPeriod) point).baseSet
    · have hx' : x ∈ (chartAt CoverModel point).source := by
        simpa only [CoverIntrinsicTangent,
          TangentBundle.trivializationAt_baseSet] using hx
      simp [Trivialization.linearMapAt_apply,
        Trivialization.symmL_apply,
        TangentBundle.trivializationAt_baseSet,
        Bundle.Trivial.trivialization_baseSet,
        hom_trivializationAt_baseSet, hx',
        hom_trivializationAt_apply,
        ContinuousLinearMap.inCoordinates]
      rfl
    · have hx' : x ∉ (chartAt CoverModel point).source := by
        simpa only [CoverIntrinsicTangent,
          TangentBundle.trivializationAt_baseSet] using hx
      simp [Trivialization.linearMapAt_apply,
        Trivialization.symmL_apply,
        TangentBundle.trivializationAt_baseSet,
        Bundle.Trivial.trivialization_baseSet,
        hom_trivializationAt_baseSet, hx',
        hom_trivializationAt_apply,
        ContinuousLinearMap.inCoordinates]
      rw [Trivialization.symm_apply_of_notMem _ hx first,
        Trivialization.symm_apply_of_notMem _ hx second]
      simp

private def ambientDeckLinear :
    AmbientCoordinates ≃L[Real] AmbientCoordinates :=
  ContinuousLinearEquiv.prodCongr
    P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection.toContinuousLinearEquiv
    (ContinuousLinearEquiv.refl Real Real)

/-- Public linear part of the genuine ambient deck generator. -/
def coverAmbientDeckGeneratorLinear :
    AmbientCoordinates →L[Real] AmbientCoordinates :=
  ambientDeckLinear.toContinuousLinearMap

@[simp]
theorem coverAmbientDeckGeneratorLinear_apply
    (point : AmbientCoordinates) :
    coverAmbientDeckGeneratorLinear point =
      (P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        point.1, point.2) := by
  rfl

private def ambientTimeTranslation : AmbientCoordinates := by
  change EuclideanR4 × Real
  exact (0, period)

@[simp]
private theorem ambient_add_fst (first second : AmbientCoordinates) :
    (first + second).1 = first.1 + second.1 := by
  rfl

@[simp]
private theorem ambient_add_snd (first second : AmbientCoordinates) :
    (first + second).2 = first.2 + second.2 := by
  rfl

@[simp]
private theorem ambientTimeTranslation_fst :
    (ambientTimeTranslation period).1 = 0 := by
  rfl

@[simp]
private theorem ambientTimeTranslation_snd :
    (ambientTimeTranslation period).2 = period := by
  rfl

private def ambientDeckMap (point : AmbientCoordinates) :
    AmbientCoordinates :=
  ambientDeckLinear point + ambientTimeTranslation period

@[simp]
private theorem ambientDeckLinear_fst (point : AmbientCoordinates) :
    (ambientDeckLinear point).1 =
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        point.1 := by
  rfl

@[simp]
private theorem ambientDeckLinear_snd (point : AmbientCoordinates) :
    (ambientDeckLinear point).2 = point.2 := by
  change ContinuousLinearEquiv.refl Real Real point.2 = point.2
  rfl

@[simp]
private theorem sphereAmbientMap_reflection (point : UnitThreeSphere) :
    sphereAmbientMap (sphereReflection point) =
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        (sphereAmbientMap point) := by
  exact unitSphereEuclideanPoint_reflection point

private theorem coverAmbientMap_generator
    (point : EffectiveCover period hPeriod) :
    coverAmbientMap period hPeriod ((1 : Int) +ᵥ point) =
      ambientDeckMap period (coverAmbientMap period hPeriod point) := by
  apply Prod.ext
  · simpa [coverAmbientMap, ambientDeckMap, ambientTimeTranslation,
      ambientNormedAddCommGroup, sphereData, reflectedSphereData] using
        sphereAmbientMap_reflection point.fiber
  · simp [coverAmbientMap, ambientDeckMap, ambientTimeTranslation,
      ambientNormedAddCommGroup, sphereData, reflectedSphereData]

private theorem ambientDeckMap_contDiff :
    ContDiff Real ∞ (ambientDeckMap period) := by
  exact ambientDeckLinear.contDiff.add contDiff_const

private theorem ambientDeckMap_hasFDerivAt (point : AmbientCoordinates) :
    HasFDerivAt (ambientDeckMap period)
      ambientDeckLinear.toContinuousLinearMap point := by
  exact ambientDeckLinear.toContinuousLinearMap.hasFDerivAt.add_const
    (ambientTimeTranslation period)

@[simp]
private theorem mfderiv_ambientDeckMap (point : AmbientCoordinates) :
    mfderiv ambientModelWithCorners ambientModelWithCorners
      (ambientDeckMap period) point =
        ambientDeckLinear.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact (ambientDeckMap_hasFDerivAt period point).fderiv

/-- The true derivative of the cover immersion intertwines the genuine deck
derivative with the ambient Lorentz reflection. -/
theorem coverAmbientDerivative_generator_natural
    (point : EffectiveCover period hPeriod) :
    (coverAmbientDerivative period hPeriod ((1 : Int) +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point) =
      ambientDeckLinear.toContinuousLinearMap.comp
        (coverAmbientDerivative period hPeriod point) := by
  have hDeck : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      ((1 : Int) +ᵥ ·) point :=
    (reflectedSphereCover_deck_contMDiff period hPeriod 1).mdifferentiableAt
      (by simp)
  have hCoverAt : MDifferentiableAt coverModelWithCorners
      ambientModelWithCorners (coverAmbientMap period hPeriod) point :=
    (coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hCoverDeck : MDifferentiableAt coverModelWithCorners
      ambientModelWithCorners (coverAmbientMap period hPeriod)
        ((1 : Int) +ᵥ point) :=
    (coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hAmbient : MDifferentiableAt ambientModelWithCorners
      ambientModelWithCorners (ambientDeckMap period)
        (coverAmbientMap period hPeriod point) :=
    (ambientDeckMap_contDiff period).contMDiff.mdifferentiableAt (by simp)
  change (mfderiv coverModelWithCorners ambientModelWithCorners
      (coverAmbientMap period hPeriod) ((1 : Int) +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point) = _
  rw [← mfderiv_comp point hCoverDeck hDeck]
  have hComposite :
      (coverAmbientMap period hPeriod) ∘ ((1 : Int) +ᵥ ·) =
        (ambientDeckMap period) ∘ (coverAmbientMap period hPeriod) := by
    funext x
    exact coverAmbientMap_generator period hPeriod x
  rw [hComposite, mfderiv_comp point hAmbient hCoverAt,
    mfderiv_ambientDeckMap]
  rfl

/-- Public form of immersion-derivative naturality under the genuine deck
generator. -/
theorem coverAmbientDerivative_deckGenerator_natural
    (point : EffectiveCover period hPeriod) :
    (coverAmbientDerivative period hPeriod ((1 : Int) +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point) =
      coverAmbientDeckGeneratorLinear.comp
        (coverAmbientDerivative period hPeriod point) := by
  simpa [coverAmbientDeckGeneratorLinear] using
    coverAmbientDerivative_generator_natural period hPeriod point

/-- Postcomposition by an ambient operator commuting with the deck linear
part preserves the exact generator cocycle of the immersion derivative. -/
theorem postcomposeCoverAmbientDerivativeSection_deckGenerator_natural
    (operator : AmbientCoordinates →L[Real] AmbientCoordinates)
    (hCommutes :
      operator.comp coverAmbientDeckGeneratorLinear =
        coverAmbientDeckGeneratorLinear.comp operator)
    (point : EffectiveCover period hPeriod) :
    ((postcomposeCoverAmbientDerivativeSection period hPeriod operator)
        ((1 : Int) +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point) =
      coverAmbientDeckGeneratorLinear.comp
        ((postcomposeCoverAmbientDerivativeSection period hPeriod operator)
          point) := by
  apply ContinuousLinearMap.ext
  intro vector
  have hDerivative := congrArg (fun derivative => derivative vector)
    (coverAmbientDerivative_deckGenerator_natural period hPeriod point)
  have hOperator := congrArg (fun current => current
      (coverAmbientDerivative period hPeriod point vector)) hCommutes
  simp only [ContinuousLinearMap.comp_apply] at hDerivative hOperator
  change operator
      (coverAmbientDerivative period hPeriod ((1 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point vector)) =
    coverAmbientDeckGeneratorLinear
      (operator (coverAmbientDerivative period hPeriod point vector))
  exact (congrArg operator hDerivative).trans hOperator

private theorem ambientDeckLinear_preserves_minkowski
    (first second : AmbientCoordinates) :
    inner Real (ambientDeckLinear first).1 (ambientDeckLinear second).1 -
        (ambientDeckLinear first).2 * (ambientDeckLinear second).2 =
      inner Real first.1 second.1 - first.2 * second.2 := by
  rw [ambientDeckLinear_fst, ambientDeckLinear_fst,
    ambientDeckLinear_snd, ambientDeckLinear_snd,
    P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection.inner_map_map]

/-- The smooth pullback tensor is invariant under the actual manifold
derivative of the deck generator. -/
theorem intrinsicCoverLorentzTensor_generator_isometry
    (point : EffectiveCover period hPeriod)
    (first second : CoverIntrinsicTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod ((1 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  change pullbackAmbientMinkowski
      (coverAmbientDerivative period hPeriod ((1 : Int) +ᵥ point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point second) =
    pullbackAmbientMinkowski (coverAmbientDerivative period hPeriod point)
      first second
  rw [pullbackAmbientMinkowski_apply, pullbackAmbientMinkowski_apply]
  have hNatural := coverAmbientDerivative_generator_natural period hPeriod point
  have hFirst := congrArg (fun map => map first) hNatural
  have hSecond := congrArg (fun map => map second) hNatural
  simp only [ContinuousLinearMap.comp_apply] at hFirst hSecond
  have hPair := congrArg₂
    (fun first second : AmbientCoordinates =>
      inner Real first.1 second.1 - first.2 * second.2)
    hFirst hSecond
  exact hPair.trans (ambientDeckLinear_preserves_minkowski
    (coverAmbientDerivative period hPeriod point first)
    (coverAmbientDerivative period hPeriod point second))

/-- Pointwise formula for the intrinsic pullback tensor in ambient
space-time coordinates. -/
theorem intrinsicCoverLorentzTensor_apply
    (point : EffectiveCover period hPeriod)
    (first second : CoverIntrinsicTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod point first second =
      inner Real (coverAmbientDerivative period hPeriod point first).1
          (coverAmbientDerivative period hPeriod point second).1 -
        (coverAmbientDerivative period hPeriod point first).2 *
          (coverAmbientDerivative period hPeriod point second).2 := by
  change pullbackAmbientMinkowski
      (coverAmbientDerivative period hPeriod point) first second = _
  exact pullbackAmbientMinkowski_apply
    (coverAmbientDerivative period hPeriod point) first second

/-- The ambient pullback tensor is symmetric on every intrinsic cover
tangent fiber. -/
theorem intrinsicCoverLorentzTensor_symmetric
    (point : EffectiveCover period hPeriod)
    (first second : CoverIntrinsicTangent period hPeriod point) :
    intrinsicCoverLorentzTensor period hPeriod point first second =
      intrinsicCoverLorentzTensor period hPeriod point second first := by
  change pullbackAmbientMinkowski
      (coverAmbientDerivative period hPeriod point) first second =
    pullbackAmbientMinkowski
      (coverAmbientDerivative period hPeriod point) second first
  rw [pullbackAmbientMinkowski_apply, pullbackAmbientMinkowski_apply,
    real_inner_comm, mul_comm]

end

end P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
end JanusFormal
