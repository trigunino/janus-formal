import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

/-!
# Concrete spatial-rotation kernel of the cover Lorentz Gram Jacobian

The already constructed `so(3)` ambient rotations are extended trivially in
the time coordinate.  Their infinitesimal action on a cover immersion one-jet
is postcomposition.  This gate proves, component by component, that the true
Frechet Jacobian of the product-Minkowski Gram map annihilates those concrete
directions, including at the actual cover immersion derivative.

This remains a pointwise one-jet identity.  It is not a global differential
complex, a quotient statement, or a boundary theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- The existing raw-coordinate spatial rotation conjugated to the Hilbert
ambient coordinates used by the cover immersion. -/
private def euclideanSpatialRotationLinear (axis : Fin 3) :
    EuclideanR4 →ₗ[Real] EuclideanR4 :=
  (WithLp.linearEquiv 2 Real (Fin 4 → Real)).symm.toLinearMap.comp
    ((ambientSpatialRotation axis).toLinearMap.comp
      (WithLp.linearEquiv 2 Real (Fin 4 → Real)).toLinearMap)

def euclideanAmbientSpatialRotation (axis : Fin 3) :
    EuclideanR4 →L[Real] EuclideanR4 :=
  (euclideanSpatialRotationLinear axis).toContinuousLinearMap

@[simp]
theorem euclideanAmbientSpatialRotation_apply
    (axis : Fin 3) (point : EuclideanR4) :
    euclideanAmbientSpatialRotation axis point =
      WithLp.toLp 2 (ambientSpatialRotation axis (WithLp.ofLp point)) := by
  rfl

/-- The Hilbert-coordinate lift of each existing spatial generator is
skew-adjoint. -/
theorem euclideanAmbientSpatialRotation_skew
    (axis : Fin 3) (first second : EuclideanR4) :
    inner Real (euclideanAmbientSpatialRotation axis first) second +
        inner Real first (euclideanAmbientSpatialRotation axis second) = 0 := by
  let rawFirst : R4Point := WithLp.ofLp first
  let rawSecond : R4Point := WithLp.ofLp second
  have hFirst := ambientSpatialRotation_tangent axis rawFirst
  have hSecond := ambientSpatialRotation_tangent axis rawSecond
  have hSum := ambientSpatialRotation_tangent axis (rawFirst + rawSecond)
  simp only [map_add, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib] at hSum
  simp only [euclideanAmbientSpatialRotation_apply, PiLp.inner_apply,
    Real.inner_apply]
  change
    (∑ index : Fin 4,
      ambientSpatialRotation axis rawFirst index * rawSecond index) +
      ∑ index : Fin 4,
        rawFirst index * ambientSpatialRotation axis rawSecond index = 0
  have hComm :
      (∑ index : Fin 4,
        ambientSpatialRotation axis rawFirst index * rawSecond index) =
        ∑ index : Fin 4,
          rawSecond index * ambientSpatialRotation axis rawFirst index := by
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hComm]
  linear_combination hSum - hFirst - hSecond

/-- The same existing spatial rotation generator, extended by zero on
ambient time. -/
def coverAmbientSpatialRotation (axis : Fin 3) :
    CoverAmbientCoordinates →L[Real] CoverAmbientCoordinates :=
  (euclideanAmbientSpatialRotation axis).prodMap
    (0 : Real →L[Real] Real)

@[simp]
theorem coverAmbientSpatialRotation_apply
    (axis : Fin 3) (point : CoverAmbientCoordinates) :
    coverAmbientSpatialRotation axis point =
      (euclideanAmbientSpatialRotation axis point.1, 0) := by
  rfl

/-- The concrete spatial generators are skew for the product-Minkowski
pairing. -/
theorem coverAmbientSpatialRotation_lorentz_skew
    (axis : Fin 3) (first second : CoverAmbientCoordinates) :
    coverAmbientLorentzPair (coverAmbientSpatialRotation axis first) second +
        coverAmbientLorentzPair first
          (coverAmbientSpatialRotation axis second) = 0 := by
  rw [coverAmbientLorentzPair_apply, coverAmbientLorentzPair_apply]
  simp only [coverAmbientSpatialRotation_apply,
    zero_mul, mul_zero, sub_zero]
  exact euclideanAmbientSpatialRotation_skew axis first.1 second.1

/-- Infinitesimal action `R_axis(F) = A_axis ∘ F` on the same cover one-jet
space used by the concrete Gram map. -/
def coverLorentzGramRotationDirection
    (axis : Fin 3) (jet : CoverLorentzOneJet) : CoverLorentzOneJet :=
  (coverAmbientSpatialRotation axis).comp jet

@[simp]
theorem coverLorentzGramRotationDirection_apply
    (axis : Fin 3) (jet : CoverLorentzOneJet)
    (vector : CoverCoordinates) :
    coverLorentzGramRotationDirection axis jet vector =
      coverAmbientSpatialRotation axis (jet vector) := by
  rfl

/-- Pointwise `J_F ∘ R_axis = 0` for every scalar Gram component. -/
theorem coverLorentzGramComponentLinearization_rotation_zero
    (axis : Fin 3) (first second : CoverCoordinates)
    (jet : CoverLorentzOneJet) :
    coverLorentzGramComponentLinearization first second jet
        (coverLorentzGramRotationDirection axis jet) = 0 := by
  rw [coverLorentzGramComponentLinearization_apply]
  simpa only [coverLorentzGramRotationDirection_apply,
    coverAmbientLorentzPair_apply] using
    coverAmbientSpatialRotation_lorentz_skew axis
      (jet first) (jet second)

/-- The same kernel identity at the genuine cover immersion derivative. -/
theorem actualCoverLorentzGramLinearization_rotation_zero
    (axis : Fin 3) (point : EffectiveCover period hPeriod)
    (first second : CoverCoordinates) :
    coverLorentzGramComponentLinearization first second
        (coverAmbientDerivativeCoordinates period hPeriod point)
        (coverLorentzGramRotationDirection axis
          (coverAmbientDerivativeCoordinates period hPeriod point)) = 0 :=
  coverLorentzGramComponentLinearization_rotation_zero axis first second
    (coverAmbientDerivativeCoordinates period hPeriod point)

/-- The selected axis-zero generator is genuinely nonzero; this rules out a
vacuous zero gauge direction. -/
theorem coverAmbientSpatialRotation_axisZero_ne_zero :
    coverAmbientSpatialRotation (0 : Fin 3) ≠ 0 := by
  intro hZero
  have hRaw : ambientSpatialRotation (0 : Fin 3) = 0 := by
    ext point index
    have hApplied := DFunLike.congr_fun hZero
      (WithLp.toLp 2 point, 0)
    have hSpatial := congrArg (fun value => value.1 index) hApplied
    simpa only [coverAmbientSpatialRotation_apply,
      euclideanAmbientSpatialRotation_apply, WithLp.ofLp_toLp,
      zero_apply, Prod.fst, Prod.fst_zero, PiLp.zero_apply,
      Pi.zero_apply] using hSpatial
  apply ambientSpatialRotation_nonabelian
  rw [hRaw]
  funext point index
  simp [VectorField.lieBracket]

end

end P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D
end JanusFormal
