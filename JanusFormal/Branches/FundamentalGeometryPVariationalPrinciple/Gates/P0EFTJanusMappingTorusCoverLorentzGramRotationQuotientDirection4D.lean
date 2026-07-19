import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientZero4D

/-!
# Quotient descent of the Lorentz--Gram rotation direction

The cover bundle-hom `A_axis ∘ dι` is the differential of the smooth
ambient-valued potential `p ↦ A_axis (ι p)`.  Its image has zero reflected
coordinate and zero time component, so the ambient deck reflection acts
trivially on it.  The potential is therefore invariant under every integer
deck winding and descends through the genuine smooth D8 quotient.  Taking its
manifold differential gives a smooth bundle-hom on the quotient whose
pullback is exactly the original cover direction.

This is the descent of the three concrete spatial-rotation directions only.
It does not construct the remaining compatibility operator or a global
exact `K/J` complex.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientDirection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private abbrev RotationAmbientCoordinates := ModelProd EuclideanR4 Real

private instance rotationAmbientNormedAddCommGroup :
    NormedAddCommGroup RotationAmbientCoordinates :=
  inferInstanceAs (NormedAddCommGroup (EuclideanR4 × Real))

private instance rotationAmbientNormedSpace :
    NormedSpace Real RotationAmbientCoordinates :=
  inferInstanceAs (NormedSpace Real (EuclideanR4 × Real))

private abbrev rotationAmbientModelWithCorners :
    ModelWithCorners Real RotationAmbientCoordinates
      RotationAmbientCoordinates :=
  𝓘(Real, RotationAmbientCoordinates)

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

private abbrev QuotientTangent
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev QuotientAmbientFiber :=
  Bundle.Trivial (EffectiveQuotient period hPeriod) RotationAmbientCoordinates

private abbrev QuotientAmbientHomFiber
    (point : EffectiveQuotient period hPeriod) :=
  QuotientTangent period hPeriod point →L[Real]
    QuotientAmbientFiber period hPeriod point

private def modelCoverAmbientSpatialRotation (axis : Fin 3) :
    RotationAmbientCoordinates →L[Real] RotationAmbientCoordinates :=
  coverAmbientSpatialRotation axis

/-- A concrete spatial rotation has no component in the reflected ambient
coordinate, hence the ambient reflection fixes its whole image. -/
private theorem euclideanAmbientSpatialRotation_zero_coordinate
    (axis : Fin 3) (point : EuclideanR4) :
    euclideanAmbientSpatialRotation axis point 0 = 0 := by
  rw [euclideanAmbientSpatialRotation_apply]
  change ambientSpatialRotation axis (WithLp.ofLp point) 0 = 0
  fin_cases axis <;> rfl

theorem euclideanReflection_euclideanAmbientSpatialRotation
    (axis : Fin 3) (point : EuclideanR4) :
    P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        (euclideanAmbientSpatialRotation axis point) =
      euclideanAmbientSpatialRotation axis point := by
  ext index
  rw [P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_apply]
  by_cases hIndex : index = 0
  · subst index
    rw [if_pos rfl,
      euclideanAmbientSpatialRotation_zero_coordinate]
    simp
  · rw [if_neg hIndex]

private theorem sphereAmbientMap_reflection
    (point : UnitThreeSphere) :
    sphereAmbientMap (sphereReflection point) =
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        (sphereAmbientMap point) := by
  exact unitSphereEuclideanPoint_reflection point

/-- Ambient-valued potential whose differential is `A_axis ∘ dι`. -/
def coverLorentzGramRotationPotential
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    RotationAmbientCoordinates :=
  modelCoverAmbientSpatialRotation axis
    (coverAmbientMap period hPeriod point)

theorem coverLorentzGramRotationPotential_contMDiff
    (axis : Fin 3) :
    ContMDiff coverModelWithCorners
      rotationAmbientModelWithCorners ∞
      (coverLorentzGramRotationPotential period hPeriod axis) := by
  exact (modelCoverAmbientSpatialRotation axis).contDiff.contMDiff.comp
    (coverAmbientMap_contMDiff period hPeriod)

/-- The potential is strictly invariant under the chosen deck generator;
the possible ambient reflection is trivial on the rotation image. -/
theorem coverLorentzGramRotationPotential_deckGenerator
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    coverLorentzGramRotationPotential period hPeriod axis
        ((1 : Int) +ᵥ point) =
      coverLorentzGramRotationPotential period hPeriod axis point := by
  apply Prod.ext
  · change euclideanAmbientSpatialRotation axis
        (sphereAmbientMap (((1 : Int) +ᵥ point).fiber)) =
      euclideanAmbientSpatialRotation axis (sphereAmbientMap point.fiber)
    rw [show ((1 : Int) +ᵥ point).fiber = sphereReflection point.fiber by
      simp [sphereData, reflectedSphereData]]
    rw [sphereAmbientMap_reflection,
      ← euclideanAmbientSpatialRotation_reflection_commutes]
    exact euclideanReflection_euclideanAmbientSpatialRotation axis _
  · rfl

/-- Strict invariance of the potential under every integer deck winding. -/
theorem coverLorentzGramRotationPotential_deckInvariant
    (axis : Fin 3) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    coverLorentzGramRotationPotential period hPeriod axis
        (winding +ᵥ point) =
      coverLorentzGramRotationPotential period hPeriod axis point := by
  let motive : Int → Prop := fun current =>
    coverLorentzGramRotationPotential period hPeriod axis
        (current +ᵥ point) =
      coverLorentzGramRotationPotential period hPeriod axis point
  change motive winding
  refine Int.inductionOn' winding 0 ?_
      (fun current _ ih => ?_) (fun current _ ih => ?_)
  · simp [motive]
  · change coverLorentzGramRotationPotential period hPeriod axis
        ((current + 1) +ᵥ point) = _
    rw [show current + 1 = 1 + current by omega, add_vadd,
      coverLorentzGramRotationPotential_deckGenerator]
    exact ih
  · have hGenerator :=
      coverLorentzGramRotationPotential_deckGenerator period hPeriod axis
        ((current - 1) +ᵥ point)
    have hIndex : 1 + (current - 1) = current := by omega
    rw [← add_vadd, hIndex] at hGenerator
    exact hGenerator.symm.trans ih

/-- The invariant potential as an existing fixed-fiber cover field. -/
def coverLorentzGramRotationInvariantPotential
    (axis : Fin 3) :
    SmoothDeckInvariantField period hPeriod RotationAmbientCoordinates where
  toFun := coverLorentzGramRotationPotential period hPeriod axis
  contMDiff_toFun :=
    coverLorentzGramRotationPotential_contMDiff period hPeriod axis
  deck_invariant :=
    coverLorentzGramRotationPotential_deckInvariant period hPeriod axis

/-- Genuine smooth descent of the ambient rotation potential to the D8
quotient. -/
def quotientLorentzGramRotationPotential
    (axis : Fin 3) :
    SmoothQuotientField period hPeriod RotationAmbientCoordinates :=
  descendSmooth period hPeriod RotationAmbientCoordinates
    (coverLorentzGramRotationInvariantPotential period hPeriod axis)

/-- The original smooth cover bundle-hom is exactly the manifold derivative
of its ambient-valued potential. -/
theorem coverLorentzGramRotationPotential_mfderiv
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    mfderiv coverModelWithCorners
        rotationAmbientModelWithCorners
        (coverLorentzGramRotationPotential period hPeriod axis) point =
      smoothCoverLorentzGramRotationHom period hPeriod axis point := by
  have hOperatorSmooth : ContMDiff
      rotationAmbientModelWithCorners rotationAmbientModelWithCorners ∞
      (modelCoverAmbientSpatialRotation axis) :=
    (modelCoverAmbientSpatialRotation axis).contDiff.contMDiff
  have hOperator : MDifferentiableAt
      rotationAmbientModelWithCorners rotationAmbientModelWithCorners
      (modelCoverAmbientSpatialRotation axis)
      (coverAmbientMap period hPeriod point) :=
    hOperatorSmooth.mdifferentiableAt (by simp)
  have hCover : MDifferentiableAt coverModelWithCorners
      rotationAmbientModelWithCorners
      (coverAmbientMap period hPeriod) point :=
    (coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp)
  change mfderiv coverModelWithCorners
      rotationAmbientModelWithCorners
      ((modelCoverAmbientSpatialRotation axis) ∘
        (coverAmbientMap period hPeriod)) point = _
  rw [mfderiv_comp point hOperator hCover]
  change (mfderiv rotationAmbientModelWithCorners
      rotationAmbientModelWithCorners
      (modelCoverAmbientSpatialRotation axis)
      (coverAmbientMap period hPeriod point)).comp
        (coverAmbientDerivative period hPeriod point) = _
  rw [mfderiv_eq_fderiv]
  rw [(modelCoverAmbientSpatialRotation axis).hasFDerivAt.fderiv]
  rfl

/-- All-winding strict naturality of the original cover bundle-hom.  The
codomain needs no transport because the rotation image is reflection-fixed. -/
theorem smoothCoverLorentzGramRotationHom_deck_natural
    (axis : Fin 3) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    (smoothCoverLorentzGramRotationHom period hPeriod axis
        (winding +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·) point) =
      smoothCoverLorentzGramRotationHom period hPeriod axis point := by
  rw [← coverLorentzGramRotationPotential_mfderiv period hPeriod,
    ← coverLorentzGramRotationPotential_mfderiv period hPeriod]
  have hPotentialAt : MDifferentiableAt coverModelWithCorners
      rotationAmbientModelWithCorners
      (coverLorentzGramRotationPotential period hPeriod axis)
      (winding +ᵥ point) :=
    (coverLorentzGramRotationPotential_contMDiff period hPeriod axis)
      |>.mdifferentiableAt (by simp)
  have hDeckAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners (winding +ᵥ ·) point :=
    (reflectedSphereCover_deck_contMDiff period hPeriod winding)
      |>.mdifferentiableAt (by simp)
  calc
    _ = mfderiv coverModelWithCorners
        rotationAmbientModelWithCorners
        ((coverLorentzGramRotationPotential period hPeriod axis) ∘
          (winding +ᵥ ·)) point :=
      (mfderiv_comp point hPotentialAt hDeckAt).symm
    _ = mfderiv coverModelWithCorners
        rotationAmbientModelWithCorners
        (coverLorentzGramRotationPotential period hPeriod axis) point := by
      apply mfderiv_congr
      funext current
      exact coverLorentzGramRotationPotential_deckInvariant
        period hPeriod axis winding current

/-- Bundle-hom direction on the true quotient, defined as the differential
of the descended potential. -/
def quotientLorentzGramRotationHom
    (axis : Fin 3) (point : EffectiveQuotient period hPeriod) :
    QuotientAmbientHomFiber period hPeriod point :=
  mfderiv coverModelWithCorners
    rotationAmbientModelWithCorners
    (quotientLorentzGramRotationPotential period hPeriod axis) point

/-- The descended direction varies smoothly as a genuine quotient
bundle-hom section. -/
def smoothQuotientLorentzGramRotationHom
    (axis : Fin 3) :
    ContMDiffSection coverModelWithCorners
      (CoverCoordinates →L[Real] RotationAmbientCoordinates) ∞
      (QuotientAmbientHomFiber period hPeriod) where
  toFun := quotientLorentzGramRotationHom period hPeriod axis
  contMDiff_toFun := by
    intro point
    rw [contMDiffAt_section]
    have hMapAt :=
      (quotientLorentzGramRotationPotential period hPeriod axis)
        |>.contMDiff_toFun point
    have hDerivative := hMapAt.mfderiv_const
      (m := ∞) (n := ∞) (by simp)
    simp only [quotientLorentzGramRotationHom,
      hom_trivializationAt_apply]
    convert hDerivative using 1 <;> try rfl
    funext current
    apply ContinuousLinearMap.ext
    intro vector
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl

/-- Pullback through the true quotient projection recovers exactly the
original cover bundle-hom direction. -/
theorem smoothQuotientLorentzGramRotationHom_pullback
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    (smoothQuotientLorentzGramRotationHom period hPeriod axis
        (mappingTorusMk (sphereData period hPeriod) point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point) =
      smoothCoverLorentzGramRotationHom period hPeriod axis point := by
  have hQuotientAt : MDifferentiableAt coverModelWithCorners
      rotationAmbientModelWithCorners
      (quotientLorentzGramRotationPotential period hPeriod axis)
      (mappingTorusMk (sphereData period hPeriod) point) :=
    (quotientLorentzGramRotationPotential period hPeriod axis)
      |>.contMDiff_toFun.mdifferentiableAt (by simp)
  have hProjectionAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod)) point :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  change (mfderiv coverModelWithCorners
      rotationAmbientModelWithCorners
      (quotientLorentzGramRotationPotential period hPeriod axis)
      (mappingTorusMk (sphereData period hPeriod) point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point) = _
  rw [← coverLorentzGramRotationPotential_mfderiv period hPeriod]
  rw [← mfderiv_comp point hQuotientAt hProjectionAt]
  apply mfderiv_congr
  funext current
  rfl

end

end P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientDirection4D
end JanusFormal
