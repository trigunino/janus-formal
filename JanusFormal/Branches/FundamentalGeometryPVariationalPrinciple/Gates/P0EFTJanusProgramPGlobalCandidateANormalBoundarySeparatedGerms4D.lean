import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCommonGermDomain4D

/-!
# Assemble separately proved normal-boundary germs

The eight component comparisons used by H10 can be proved on eight different
open neighbourhoods.  Their finite intersection is a common germ domain.  This
module indexes the components, forms that intersection and constructs the
single `NormalBoundaryComponentwiseGermData` consumed by the terminal closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundarySeparatedGerms4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 1100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Topology

universe u v w z

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

variable {Boundary : Type v}
  [MeasurableSpace Boundary]

variable {TangentIndex : Type w} [Fintype TangentIndex]
variable {AmbientIndex : Type z} [Fintype AmbientIndex]

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryCommonGermDomain4D

/-- The eight independent geometric comparisons of the terminal H10 packet. -/
inductive NormalBoundaryGermComponent
  | tangent
  | tangentDerivative
  | christoffel
  | normal
  | metric
  | inverse
  | orientation
  | density
  deriving DecidableEq, Fintype

/-- Finite intersection of a family of open germ domains. -/
def OpenGermDomain.finiteInter
    {base : Variation}
    {Component : Type*} [Fintype Component]
    (domains : Component → OpenGermDomain base) : OpenGermDomain base where
  carrier := ⋂ component, (domains component).carrier
  isOpen_carrier := isOpen_iInter_of_finite fun component =>
    (domains component).isOpen_carrier
  base_mem_carrier := Set.mem_iInter.mpr fun component =>
    (domains component).base_mem_carrier

/-- Membership in the finite common domain implies membership in every
component domain. -/
theorem OpenGermDomain.finiteInter_mem
    {base : Variation}
    {Component : Type*} [Fintype Component]
    (domains : Component → OpenGermDomain base)
    {variation : Variation}
    (hVariation : variation ∈ (OpenGermDomain.finiteInter domains).carrier)
    (component : Component) :
    variation ∈ (domains component).carrier :=
  Set.mem_iInter.mp hVariation component

/-- Eight component comparisons, each on its own open germ domain. -/
structure NormalBoundarySeparatedGermData
    (completedTangent historicalTangent :
      Variation → Boundary → TangentIndex → AmbientIndex → Real)
    (completedTangentDerivative historicalTangentDerivative :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real)
    (completedChristoffel historicalChristoffel :
      Variation → Boundary → AmbientIndex → AmbientIndex → AmbientIndex → Real)
    (completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real)
    (completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real)
    (completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real)
    (completedOrientation historicalOrientation :
      Variation → Boundary → Real)
    (completedDensity historicalDensity :
      Variation → Boundary → Real)
    (base : Variation) : Type u where
  domain : NormalBoundaryGermComponent → OpenGermDomain base
  tangent_eq : ∀ variation,
    variation ∈ (domain .tangent).carrier → ∀ boundary tangent ambient,
      completedTangent variation boundary tangent ambient =
        historicalTangent variation boundary tangent ambient
  tangentDerivative_eq : ∀ variation,
    variation ∈ (domain .tangentDerivative).carrier →
      ∀ boundary first second ambient,
        completedTangentDerivative variation boundary first second ambient =
          historicalTangentDerivative variation boundary first second ambient
  christoffel_eq : ∀ variation,
    variation ∈ (domain .christoffel).carrier →
      ∀ boundary upper lower₁ lower₂,
        completedChristoffel variation boundary upper lower₁ lower₂ =
          historicalChristoffel variation boundary upper lower₁ lower₂
  normal_eq : ∀ variation,
    variation ∈ (domain .normal).carrier → ∀ boundary ambient,
      completedNormal variation boundary ambient =
        historicalNormal variation boundary ambient
  metric_eq : ∀ variation,
    variation ∈ (domain .metric).carrier → ∀ boundary row column,
      completedMetric variation boundary row column =
        historicalMetric variation boundary row column
  inverse_eq : ∀ variation,
    variation ∈ (domain .inverse).carrier → ∀ boundary first second,
      completedInverse variation boundary first second =
        historicalInverse variation boundary first second
  orientation_eq : ∀ variation,
    variation ∈ (domain .orientation).carrier → ∀ boundary,
      completedOrientation variation boundary =
        historicalOrientation variation boundary
  density_eq : ∀ variation,
    variation ∈ (domain .density).carrier → ∀ boundary,
      completedDensity variation boundary =
        historicalDensity variation boundary

/-- The unique common open neighbourhood of all eight component germs. -/
def NormalBoundarySeparatedGermData.commonDomain
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
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (data : NormalBoundarySeparatedGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base) : OpenGermDomain base :=
  OpenGermDomain.finiteInter data.domain

/-- The separated tangent, derivative and Christoffel comparisons form the
covariant-acceleration germ on the common domain. -/
def NormalBoundarySeparatedGermData.accelerationGerm
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
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (data : NormalBoundarySeparatedGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base) :
    SameCovariantAccelerationGermAt
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel base where
  domain := data.commonDomain.carrier
  isOpen_domain := data.commonDomain.isOpen_carrier
  base_mem_domain := data.commonDomain.base_mem_carrier
  tangent_eq := by
    intro variation hVariation
    exact data.tangent_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .tangent)
  tangentDerivative_eq := by
    intro variation hVariation
    exact data.tangentDerivative_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .tangentDerivative)
  christoffel_eq := by
    intro variation hVariation
    exact data.christoffel_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .christoffel)

/-- Assemble all eight separate germs into the terminal componentwise packet. -/
def NormalBoundarySeparatedGermData.toComponentwise
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
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (data : NormalBoundarySeparatedGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base) :
    NormalBoundaryComponentwiseGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base where
  acceleration := data.accelerationGerm
  normal_eq := by
    intro variation hVariation
    exact data.normal_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .normal)
  metric_eq := by
    intro variation hVariation
    exact data.metric_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .metric)
  inverse_eq := by
    intro variation hVariation
    exact data.inverse_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .inverse)
  orientation_eq := by
    intro variation hVariation
    exact data.orientation_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .orientation)
  density_eq := by
    intro variation hVariation
    exact data.density_eq variation
      (OpenGermDomain.finiteInter_mem data.domain hVariation .density)

/-- Eight independently local comparisons close the same two-sheet action germ. -/
def candidate_a_normal_boundary_separated_germs_terminal_gate
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
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (data : NormalBoundarySeparatedGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base)
    (measure : Measure Boundary) :=
  (data.toComponentwise).twoSheetActionGerm measure

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundarySeparatedGerms4D
end JanusFormal
