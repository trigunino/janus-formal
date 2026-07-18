import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Deck-invariant Lorentz cocycle on the D8 cover

The reflection mapping-torus generator preserves the product Lorentz form on
the ambient sphere tangent and the real translation direction.  This is the
exact tensor cocycle which must be descended through the quotient tangent
bundle; it does not choose a global frame on the nonorientable quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Set Module
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

private def coordinateReflection (index : Fin 4) : Real ≃ₗᵢ[Real] Real :=
  if index = 0 then LinearIsometryEquiv.neg Real
  else LinearIsometryEquiv.refl Real Real

/-- Orthogonal reflection of the first ambient Euclidean coordinate. -/
def euclideanReflection : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4 :=
  LinearIsometryEquiv.piLpCongrRight 2 coordinateReflection

@[simp]
theorem euclideanReflection_apply
    (point : EuclideanR4) (index : Fin 4) :
    euclideanReflection point index =
      if index = 0 then -point index else point index := by
  rw [euclideanReflection, LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases hIndex : index = 0
  · simp [coordinateReflection, hIndex]
  · simp [coordinateReflection, hIndex]

@[simp]
theorem euclideanReflection_involutive (point : EuclideanR4) :
    euclideanReflection (euclideanReflection point) = point := by
  ext index
  by_cases hIndex : index = 0
  · simp [hIndex]
  · simp [hIndex]

private def unitSphereEuclideanPoint (point : UnitThreeSphere) : EuclideanR4 :=
  WithLp.toLp 2 point.1

private theorem unitSphereEuclideanPoint_ne_zero
    (point : UnitThreeSphere) : unitSphereEuclideanPoint point ≠ 0 := by
  intro hZero
  have hPointZero : point.1 = 0 := by
    apply WithLp.toLp_injective 2
    simpa [unitSphereEuclideanPoint] using hZero
  have hSphere := point.2
  rw [hPointZero] at hSphere
  norm_num [OnUnitThreeSphere, radiusSquared] at hSphere

@[simp]
theorem unitSphereEuclideanPoint_reflection
    (point : UnitThreeSphere) :
    unitSphereEuclideanPoint (sphereReflection point) =
      euclideanReflection (unitSphereEuclideanPoint point) := by
  ext index
  simp [unitSphereEuclideanPoint, sphereReflection,
    euclideanReflection_apply, reflectPoint]

/-- Ambient orthogonal model of the three-dimensional sphere tangent. -/
private abbrev SphereTangentModel (point : UnitThreeSphere) :=
  (Real ∙ unitSphereEuclideanPoint point)ᗮ

/-- The differential cocycle of the reflection on the ambient sphere tangent. -/
def sphereReflectionTangent (point : UnitThreeSphere) :
    SphereTangentModel point ≃ₗᵢ[Real]
      SphereTangentModel (sphereReflection point) where
  toFun vector := ⟨euclideanReflection vector, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
      unitSphereEuclideanPoint_reflection]
    rw [euclideanReflection.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp vector.2⟩
  invFun vector := ⟨euclideanReflection vector, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hVector :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp vector.2
    calc
      inner Real (unitSphereEuclideanPoint point)
          (euclideanReflection vector) =
          inner Real
            (euclideanReflection
              (unitSphereEuclideanPoint (sphereReflection point)))
            (euclideanReflection vector) := by
              rw [unitSphereEuclideanPoint_reflection,
                euclideanReflection_involutive]
      _ = inner Real (unitSphereEuclideanPoint (sphereReflection point)) vector :=
        euclideanReflection.inner_map_map _ _
      _ = 0 := hVector⟩
  left_inv vector := by
    apply Subtype.ext
    exact euclideanReflection_involutive vector
  right_inv vector := by
    apply Subtype.ext
    exact euclideanReflection_involutive vector
  map_add' first second := by
    apply Subtype.ext
    exact euclideanReflection.map_add (first : EuclideanR4) second
  map_smul' scalar vector := by
    apply Subtype.ext
    exact euclideanReflection.map_smul scalar (vector : EuclideanR4)
  norm_map' vector := euclideanReflection.norm_map vector

@[simp]
theorem sphereReflectionTangent_apply
    (point : UnitThreeSphere) (vector : SphereTangentModel point) :
    (sphereReflectionTangent point vector : EuclideanR4) =
      euclideanReflection vector := rfl

/-- Product tangent model: sphere tangent plus the real translation line. -/
private abbrev CoverLorentzTangent (point : EffectiveCover period hPeriod) :=
  SphereTangentModel point.fiber × Real

/-- Tangent action of the mapping-torus generator. -/
def deckGeneratorTangent (point : EffectiveCover period hPeriod) :
    CoverLorentzTangent period hPeriod point ≃L[Real]
      CoverLorentzTangent period hPeriod ((1 : Int) +ᵥ point) := by
  change (SphereTangentModel point.fiber × Real) ≃L[Real]
    (SphereTangentModel (sphereReflection point.fiber) × Real)
  exact ContinuousLinearEquiv.prodCongr
    (sphereReflectionTangent point.fiber).toContinuousLinearEquiv
    (ContinuousLinearEquiv.refl Real Real)

/-- Product Lorentz form with the mapping-torus direction timelike. -/
def coverLorentzPair
    (point : EffectiveCover period hPeriod)
    (first second : CoverLorentzTangent period hPeriod point) : Real :=
  inner Real first.1 second.1 - first.2 * second.2

theorem coverLorentzPair_symmetric
    (point : EffectiveCover period hPeriod)
    (first second : CoverLorentzTangent period hPeriod point) :
    coverLorentzPair period hPeriod point first second =
      coverLorentzPair period hPeriod point second first := by
  simp [coverLorentzPair, real_inner_comm, mul_comm]

private def spatialMusical (point : UnitThreeSphere) :
    SphereTangentModel point ≃L[Real]
      (SphereTangentModel point →L[Real] Real) :=
  (InnerProductSpace.toDual Real (SphereTangentModel point)).toContinuousLinearEquiv

private def timeLorentzMusical : Real ≃L[Real] (Real →L[Real] Real) :=
  (ContinuousLinearEquiv.neg Real).trans
    (InnerProductSpace.toDual Real Real).toContinuousLinearEquiv

/-- The product Lorentz form is a genuine musical equivalence on every cover fiber. -/
def coverLorentzMusical (point : EffectiveCover period hPeriod) :
    CoverLorentzTangent period hPeriod point ≃L[Real]
      (CoverLorentzTangent period hPeriod point →L[Real] Real) :=
  (ContinuousLinearEquiv.prodCongr
    (spatialMusical point.fiber) timeLorentzMusical).trans
      (ContinuousLinearMap.coprodEquivL Real)

@[simp]
theorem coverLorentzMusical_apply
    (point : EffectiveCover period hPeriod)
    (first second : CoverLorentzTangent period hPeriod point) :
    coverLorentzMusical period hPeriod point first second =
      coverLorentzPair period hPeriod point first second := by
  simp [coverLorentzMusical, coverLorentzPair, spatialMusical,
    timeLorentzMusical, ContinuousLinearMap.coprodEquivL,
    ContinuousLinearMap.coprodEquiv]
  change inner Real first.1 second.1 + -inner Real first.2 second.2 =
    inner Real (first.1 : EuclideanR4) (second.1 : EuclideanR4) -
      first.2 * second.2
  rw [Real.inner_apply]
  rfl

theorem coverLorentzPair_nondegenerate
    (point : EffectiveCover period hPeriod) :
    Function.Injective (coverLorentzMusical period hPeriod point) :=
  (coverLorentzMusical period hPeriod point).injective

private instance euclideanR4_finrank_fact :
    Fact (finrank Real EuclideanR4 = 3 + 1) := by
  constructor
  simp

private def sphereTangentFrame (point : UnitThreeSphere) :
    SphereTangentModel point ≃L[Real] EuclideanSpace Real (Fin 3) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
    (unitSphereEuclideanPoint_ne_zero point)).repr.toContinuousLinearEquiv

/-- Pointwise Lorentz frame used only to certify inertia; it is not asserted
to form a smooth global frame on the quotient. -/
def coverLorentzFrame (point : EffectiveCover period hPeriod) :
    CoverLorentzTangent period hPeriod point ≃L[Real] CoverCoordinates :=
  ContinuousLinearEquiv.prodCongr (sphereTangentFrame point.fiber)
    (ContinuousLinearEquiv.refl Real Real)

theorem coverLorentzPair_eq_modelMinkowski
    (point : EffectiveCover period hPeriod)
    (first second : CoverLorentzTangent period hPeriod point) :
    coverLorentzPair period hPeriod point first second =
      modelMinkowskiPair
        (coverLorentzFrame period hPeriod point first)
        (coverLorentzFrame period hPeriod point second) := by
  change inner Real first.1 second.1 - first.2 * second.2 =
    inner Real (sphereTangentFrame point.fiber first.1)
      (sphereTangentFrame point.fiber second.1) - first.2 * second.2
  congr 1
  exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) 3
    (unitSphereEuclideanPoint_ne_zero point.fiber)).repr.inner_map_map
      first.1 second.1).symm

/-- Exact generator isometry: reflection on the sphere tangent and identity
on the translation tangent preserve the Lorentz form. -/
theorem deckGenerator_preserves_coverLorentzPair
    (point : EffectiveCover period hPeriod)
    (first second : CoverLorentzTangent period hPeriod point) :
    coverLorentzPair period hPeriod ((1 : Int) +ᵥ point)
        (deckGeneratorTangent period hPeriod point first)
        (deckGeneratorTangent period hPeriod point second) =
      coverLorentzPair period hPeriod point first second := by
  change inner Real (sphereReflectionTangent point.fiber first.1)
      (sphereReflectionTangent point.fiber second.1) - first.2 * second.2 =
    inner Real first.1 second.1 - first.2 * second.2
  rw [(sphereReflectionTangent point.fiber).inner_map_map]

/-- Concrete, nonempty generator cocycle containing the tensor, its musical
equivalence, its inertia frame and its deck isometry. -/
structure DeckLorentzGeneratorCocycle where
  pair : ∀ point : EffectiveCover period hPeriod,
    CoverLorentzTangent period hPeriod point →
      CoverLorentzTangent period hPeriod point → Real
  musical : ∀ point : EffectiveCover period hPeriod,
    CoverLorentzTangent period hPeriod point ≃L[Real]
      (CoverLorentzTangent period hPeriod point →L[Real] Real)
  frame : ∀ point : EffectiveCover period hPeriod,
    CoverLorentzTangent period hPeriod point ≃L[Real] CoverCoordinates
  musical_eq_pair : ∀ point first second,
    musical point first second = pair point first second
  lorentzian : ∀ point first second,
    pair point first second =
      modelMinkowskiPair (frame point first) (frame point second)
  generatorIsometry : ∀ point first second,
    pair ((1 : Int) +ᵥ point)
        (deckGeneratorTangent period hPeriod point first)
        (deckGeneratorTangent period hPeriod point second) =
      pair point first second

def productLorentzCocycle :
    DeckLorentzGeneratorCocycle period hPeriod where
  pair := coverLorentzPair period hPeriod
  musical := coverLorentzMusical period hPeriod
  frame := coverLorentzFrame period hPeriod
  musical_eq_pair := coverLorentzMusical_apply period hPeriod
  lorentzian := coverLorentzPair_eq_modelMinkowski period hPeriod
  generatorIsometry := deckGenerator_preserves_coverLorentzPair period hPeriod

theorem deckLorentzGeneratorCocycle_nonempty :
    Nonempty (DeckLorentzGeneratorCocycle period hPeriod) :=
  ⟨productLorentzCocycle period hPeriod⟩

private abbrev CoverIntrinsicTangent
    (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CoverIntrinsicTensorFiber
    (point : EffectiveCover period hPeriod) :=
  CoverIntrinsicTangent period hPeriod point →L[Real]
    (CoverIntrinsicTangent period hPeriod point →L[Real] Real)

private abbrev SmoothIntrinsicCoverTensor :=
  ContMDiffSection coverModelWithCorners
    (CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real) ∞
    (CoverIntrinsicTensorFiber period hPeriod)

/-- First missing API bridge.  It identifies the ambient sphere tangent
model with Mathlib's intrinsic cover tangent, realizes the product form as a
smooth intrinsic tensor, and commutes with the actual deck derivative. -/
structure IntrinsicCoverTensorBridge where
  tensor : SmoothIntrinsicCoverTensor period hPeriod
  identification : ∀ point : EffectiveCover period hPeriod,
    CoverLorentzTangent period hPeriod point ≃L[Real]
      CoverIntrinsicTangent period hPeriod point
  tensor_eq_pair : ∀ point first second,
    tensor point (identification point first) (identification point second) =
      coverLorentzPair period hPeriod point first second
  generator_natural : ∀ point vector,
    mfderiv coverModelWithCorners coverModelWithCorners
        ((1 : Int) +ᵥ ·) point (identification point vector) =
      identification ((1 : Int) +ᵥ point)
        (deckGeneratorTangent period hPeriod point vector)

/-- The bridge hypotheses imply invariance of the smooth intrinsic cover
tensor under the genuine derivative of the deck generator. -/
theorem IntrinsicCoverTensorBridge.generator_isometry
    (bridge : IntrinsicCoverTensorBridge period hPeriod)
    (point : EffectiveCover period hPeriod)
    (first second : CoverIntrinsicTangent period hPeriod point) :
    bridge.tensor ((1 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point second) =
      bridge.tensor point first second := by
  obtain ⟨firstModel, rfl⟩ := (bridge.identification point).surjective first
  obtain ⟨secondModel, rfl⟩ := (bridge.identification point).surjective second
  rw [bridge.generator_natural, bridge.generator_natural,
    bridge.tensor_eq_pair, bridge.tensor_eq_pair]
  exact deckGenerator_preserves_coverLorentzPair period hPeriod
    point firstModel secondModel

/-- Second missing API bridge.  The quotient metric is a smooth descent when
its pullback by the actual quotient projection derivative is the intrinsic
deck-invariant cover tensor.  No existence assertion is attached here. -/
def IsIntrinsicSmoothDescent
    (bridge : IntrinsicCoverTensorBridge period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) : Prop :=
  ∀ point first second,
    metric.tensor.tensor
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) =
      bridge.tensor point first second

end

end P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
end JanusFormal
