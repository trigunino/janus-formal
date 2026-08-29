import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D

/-!
# Algebraic Gauss--Weingarten germ closure

The remaining H10 geometric identity is assembled from finite regular-frame
coefficients.  The covariant acceleration is

`∂ᵢTⱼ + Γ(Tᵢ,Tⱼ)`,

and the Gauss second fundamental form is its metric pairing with the physical
unit normal.  This module proves that componentwise agreement of the already
constructed tangent, tangent derivative, Christoffel, metric and normal data
forces agreement of the complete second fundamental form and hence of the
contracted mean curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Topology

universe u v w z

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

variable {Boundary : Type v}
  [MeasurableSpace Boundary]

variable {TangentIndex : Type w} [Fintype TangentIndex]
variable {AmbientIndex : Type z} [Fintype AmbientIndex]

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D

/-- Regular-frame covariant acceleration of a graph tangent. -/
def regularFrameCovariantAcceleration
    (tangent : TangentIndex → AmbientIndex → Real)
    (tangentDerivative : TangentIndex → TangentIndex → AmbientIndex → Real)
    (christoffel : AmbientIndex → AmbientIndex → AmbientIndex → Real)
    (first second : TangentIndex) (upper : AmbientIndex) : Real :=
  tangentDerivative first second upper +
    ∑ lower₁ : AmbientIndex, ∑ lower₂ : AmbientIndex,
      tangent first lower₁ * tangent second lower₂ *
        christoffel upper lower₁ lower₂

/-- Metric pairing of the covariant graph acceleration with a normal. -/
def gaussSecondForm
    (normal : AmbientIndex → Real)
    (metric : AmbientIndex → AmbientIndex → Real)
    (acceleration : TangentIndex → TangentIndex → AmbientIndex → Real)
    (first second : TangentIndex) : Real :=
  ∑ row : AmbientIndex, ∑ column : AmbientIndex,
    normal row * metric row column * acceleration first second column

/-- Componentwise equality of the three inputs of the covariant acceleration. -/
structure SameCovariantAccelerationGermAt
    (completedTangent historicalTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real)
    (completedTangentDerivative historicalTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real)
    (completedChristoffel historicalChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real)
    (base : Variation) : Type u where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  base_mem_domain : base ∈ domain
  tangent_eq : ∀ variation, variation ∈ domain → ∀ boundary tangent ambient,
    completedTangent variation boundary tangent ambient =
      historicalTangent variation boundary tangent ambient
  tangentDerivative_eq : ∀ variation, variation ∈ domain →
    ∀ boundary first second ambient,
      completedTangentDerivative variation boundary first second ambient =
        historicalTangentDerivative variation boundary first second ambient
  christoffel_eq : ∀ variation, variation ∈ domain →
    ∀ boundary upper lower₁ lower₂,
      completedChristoffel variation boundary upper lower₁ lower₂ =
        historicalChristoffel variation boundary upper lower₁ lower₂

/-- Completed covariant acceleration field. -/
def completedCovariantAcceleration
    (completedTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real)
    (completedTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real)
    (completedChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real) :
    Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real :=
  fun variation boundary =>
    regularFrameCovariantAcceleration
      (completedTangent variation boundary)
      (completedTangentDerivative variation boundary)
      (completedChristoffel variation boundary)

/-- Historical covariant acceleration field. -/
def historicalCovariantAcceleration
    (historicalTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real)
    (historicalTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real)
    (historicalChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real) :
    Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real :=
  fun variation boundary =>
    regularFrameCovariantAcceleration
      (historicalTangent variation boundary)
      (historicalTangentDerivative variation boundary)
      (historicalChristoffel variation boundary)

/-- The finite `∂T + ΓTT` formula transports componentwise equality. -/
theorem SameCovariantAccelerationGermAt.acceleration_eq
    {completedTangent historicalTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real}
    {completedTangentDerivative historicalTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {completedChristoffel historicalChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real}
    {base : Variation}
    (germ : SameCovariantAccelerationGermAt
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel base) :
    ∀ variation, variation ∈ germ.domain → ∀ boundary first second upper,
      completedCovariantAcceleration completedTangent
          completedTangentDerivative completedChristoffel
          variation boundary first second upper =
        historicalCovariantAcceleration historicalTangent
          historicalTangentDerivative historicalChristoffel
          variation boundary first second upper := by
  intro variation hVariation boundary first second upper
  unfold completedCovariantAcceleration historicalCovariantAcceleration
    regularFrameCovariantAcceleration
  rw [germ.tangentDerivative_eq variation hVariation boundary first second upper]
  apply congrArg (fun value : Real =>
    historicalTangentDerivative variation boundary first second upper + value)
  apply Finset.sum_congr rfl
  intro lower₁ hLower₁
  apply Finset.sum_congr rfl
  intro lower₂ hLower₂
  rw [germ.tangent_eq variation hVariation boundary first lower₁,
    germ.tangent_eq variation hVariation boundary second lower₂,
    germ.christoffel_eq variation hVariation boundary upper lower₁ lower₂]

/-- Componentwise equality of normal, metric and covariant acceleration. -/
structure SameGaussSecondFormGermAt
    (completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real)
    (completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real)
    (completedAcceleration historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real)
    (base : Variation) : Type u where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  base_mem_domain : base ∈ domain
  normal_eq : ∀ variation, variation ∈ domain → ∀ boundary ambient,
    completedNormal variation boundary ambient =
      historicalNormal variation boundary ambient
  metric_eq : ∀ variation, variation ∈ domain → ∀ boundary row column,
    completedMetric variation boundary row column =
      historicalMetric variation boundary row column
  acceleration_eq : ∀ variation, variation ∈ domain →
    ∀ boundary first second ambient,
      completedAcceleration variation boundary first second ambient =
        historicalAcceleration variation boundary first second ambient

/-- Completed Gauss form field. -/
def completedGaussSecondForm
    (completedNormal : Variation → Boundary → AmbientIndex → Real)
    (completedMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real)
    (completedAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real) :
    Variation → Boundary → TangentIndex → TangentIndex → Real :=
  fun variation boundary =>
    gaussSecondForm
      (completedNormal variation boundary)
      (completedMetric variation boundary)
      (completedAcceleration variation boundary)

/-- Historical Gauss form field. -/
def historicalGaussSecondForm
    (historicalNormal : Variation → Boundary → AmbientIndex → Real)
    (historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real)
    (historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real) :
    Variation → Boundary → TangentIndex → TangentIndex → Real :=
  fun variation boundary =>
    gaussSecondForm
      (historicalNormal variation boundary)
      (historicalMetric variation boundary)
      (historicalAcceleration variation boundary)

/-- The metric pairing transports componentwise equality. -/
theorem SameGaussSecondFormGermAt.secondForm_eq
    {completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real}
    {completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real}
    {completedAcceleration historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {base : Variation}
    (germ : SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      completedAcceleration historicalAcceleration base) :
    ∀ variation, variation ∈ germ.domain → ∀ boundary first second,
      completedGaussSecondForm completedNormal completedMetric
          completedAcceleration variation boundary first second =
        historicalGaussSecondForm historicalNormal historicalMetric
          historicalAcceleration variation boundary first second := by
  intro variation hVariation boundary first second
  unfold completedGaussSecondForm historicalGaussSecondForm gaussSecondForm
  apply Finset.sum_congr rfl
  intro row hRow
  apply Finset.sum_congr rfl
  intro column hColumn
  rw [germ.normal_eq variation hVariation boundary row,
    germ.metric_eq variation hVariation boundary row column,
    germ.acceleration_eq variation hVariation boundary first second column]

/-- Build the Gauss-form comparison directly from the tangent/Christoffel
comparison and the normal/metric comparisons. -/
def SameCovariantAccelerationGermAt.toGaussSecondFormGerm
    {completedTangent historicalTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real}
    {completedTangentDerivative historicalTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {completedChristoffel historicalChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real}
    {completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real}
    {completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real}
    {base : Variation}
    (acceleration : SameCovariantAccelerationGermAt
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel base)
    (normalEq : ∀ variation, variation ∈ acceleration.domain →
      ∀ boundary ambient,
        completedNormal variation boundary ambient =
          historicalNormal variation boundary ambient)
    (metricEq : ∀ variation, variation ∈ acceleration.domain →
      ∀ boundary row column,
        completedMetric variation boundary row column =
          historicalMetric variation boundary row column) :
    SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      (completedCovariantAcceleration completedTangent
        completedTangentDerivative completedChristoffel)
      (historicalCovariantAcceleration historicalTangent
        historicalTangentDerivative historicalChristoffel)
      base where
  domain := acceleration.domain
  isOpen_domain := acceleration.isOpen_domain
  base_mem_domain := acceleration.base_mem_domain
  normal_eq := normalEq
  metric_eq := metricEq
  acceleration_eq := acceleration.acceleration_eq

/-- Add inverse induced metric equality and obtain the complete mean-curvature
germ used by the GHY factor closure. -/
def SameGaussSecondFormGermAt.toContractedMeanCurvatureGerm
    {completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real}
    {completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real}
    {completedAcceleration historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {base : Variation}
    (gauss : SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      completedAcceleration historicalAcceleration base)
    (inverseEq : ∀ variation, variation ∈ gauss.domain →
      ∀ boundary first second,
        completedInverse variation boundary first second =
          historicalInverse variation boundary first second) :
    SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      (completedGaussSecondForm completedNormal completedMetric
        completedAcceleration)
      (historicalGaussSecondForm historicalNormal historicalMetric
        historicalAcceleration)
      base where
  domain := gauss.domain
  isOpen_domain := gauss.isOpen_domain
  base_mem_domain := gauss.base_mem_domain
  inverse_eq := inverseEq
  secondForm_eq := gauss.secondForm_eq

/-- Public algebraic Gauss--Weingarten closure gate. -/
theorem candidate_a_normal_boundary_gauss_form_germ_gate
    {completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real}
    {completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real}
    {completedAcceleration historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {base : Variation}
    (germ : SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      completedAcceleration historicalAcceleration base) :
    ∀ variation, variation ∈ germ.domain → ∀ boundary first second,
      completedGaussSecondForm completedNormal completedMetric
          completedAcceleration variation boundary first second =
        historicalGaussSecondForm historicalNormal historicalMetric
          historicalAcceleration variation boundary first second :=
  germ.secondForm_eq

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D
end JanusFormal
