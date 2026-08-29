import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySeparatedGerms4D

/-!
# H10 component germs from `EventuallyEq`

The historical chart and section comparison theorems are naturally stated as
`EventuallyEq` at the anchor.  Such a theorem already contains an open germ:
the interior of its equality set is an open neighbourhood of the anchor.  This
module extracts that neighbourhood and converts eight eventual coefficient
identities directly into the separated-germ terminal packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryEventuallyEqGerms4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 1100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Topology

universe u v w z q

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

variable {Boundary : Type v}
  [MeasurableSpace Boundary]

variable {TangentIndex : Type w} [Fintype TangentIndex]
variable {AmbientIndex : Type z} [Fintype AmbientIndex]

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryCommonGermDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySeparatedGerms4D

/-- Canonical open representative of an eventual equality. -/
def OpenGermDomain.ofEventuallyEq
    {Target : Type q}
    {completed historical : Variation → Target}
    {base : Variation}
    (hEq : completed =ᶠ[𝓝 base] historical) : OpenGermDomain base where
  carrier := interior {variation | completed variation = historical variation}
  isOpen_carrier := isOpen_interior
  base_mem_carrier := by
    apply mem_interior_iff_mem_nhds.mpr
    exact hEq

/-- Membership in the extracted open germ gives the original equality. -/
theorem OpenGermDomain.ofEventuallyEq_apply
    {Target : Type q}
    {completed historical : Variation → Target}
    {base : Variation}
    (hEq : completed =ᶠ[𝓝 base] historical)
    {variation : Variation}
    (hVariation : variation ∈ (OpenGermDomain.ofEventuallyEq hEq).carrier) :
    completed variation = historical variation := by
  have hVariation' :
      variation ∈ interior {point | completed point = historical point} :=
    hVariation
  exact (interior_subset :
    interior {point : Variation | completed point = historical point} ⊆
      {point : Variation | completed point = historical point}) hVariation'

/-- Direct action-germ constructor from eventual equality. -/
def SameRealActionGermAt.ofEventuallyEq
    {completed historical : Variation → Real}
    {base : Variation}
    (hEq : completed =ᶠ[𝓝 base] historical) :
    SameRealActionGermAt completed historical base where
  domain := (OpenGermDomain.ofEventuallyEq hEq).carrier
  isOpen_domain := (OpenGermDomain.ofEventuallyEq hEq).isOpen_carrier
  base_mem_domain := (OpenGermDomain.ofEventuallyEq hEq).base_mem_carrier
  eqOn_domain := fun _ hVariation =>
    OpenGermDomain.ofEventuallyEq_apply hEq hVariation

/-- The eight historical component identities in their native eventual form. -/
structure NormalBoundaryEventuallyEqGermData
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
    (base : Variation) : Prop where
  tangent_eq : completedTangent =ᶠ[𝓝 base] historicalTangent
  tangentDerivative_eq :
    completedTangentDerivative =ᶠ[𝓝 base] historicalTangentDerivative
  christoffel_eq : completedChristoffel =ᶠ[𝓝 base] historicalChristoffel
  normal_eq : completedNormal =ᶠ[𝓝 base] historicalNormal
  metric_eq : completedMetric =ᶠ[𝓝 base] historicalMetric
  inverse_eq : completedInverse =ᶠ[𝓝 base] historicalInverse
  orientation_eq : completedOrientation =ᶠ[𝓝 base] historicalOrientation
  density_eq : completedDensity =ᶠ[𝓝 base] historicalDensity

/-- Component-specific open germ domains extracted from the eight eventual
identities. -/
def NormalBoundaryEventuallyEqGermData.domain
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
    (data : NormalBoundaryEventuallyEqGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base) :
    NormalBoundaryGermComponent → OpenGermDomain base
  | .tangent => OpenGermDomain.ofEventuallyEq data.tangent_eq
  | .tangentDerivative =>
      OpenGermDomain.ofEventuallyEq data.tangentDerivative_eq
  | .christoffel => OpenGermDomain.ofEventuallyEq data.christoffel_eq
  | .normal => OpenGermDomain.ofEventuallyEq data.normal_eq
  | .metric => OpenGermDomain.ofEventuallyEq data.metric_eq
  | .inverse => OpenGermDomain.ofEventuallyEq data.inverse_eq
  | .orientation => OpenGermDomain.ofEventuallyEq data.orientation_eq
  | .density => OpenGermDomain.ofEventuallyEq data.density_eq

/-- Convert eventual coefficient identities into separated open germs. -/
def NormalBoundaryEventuallyEqGermData.toSeparated
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
    (data : NormalBoundaryEventuallyEqGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base) :
    NormalBoundarySeparatedGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base where
  domain := data.domain
  tangent_eq := by
    intro variation hVariation boundary tangent ambient
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.tangent_eq hVariation
    exact congrArg (fun field => field boundary tangent ambient) hWhole
  tangentDerivative_eq := by
    intro variation hVariation boundary first second ambient
    have hWhole := OpenGermDomain.ofEventuallyEq_apply
      data.tangentDerivative_eq hVariation
    exact congrArg (fun field => field boundary first second ambient) hWhole
  christoffel_eq := by
    intro variation hVariation boundary upper lower₁ lower₂
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.christoffel_eq
      hVariation
    exact congrArg (fun field => field boundary upper lower₁ lower₂) hWhole
  normal_eq := by
    intro variation hVariation boundary ambient
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.normal_eq hVariation
    exact congrArg (fun field => field boundary ambient) hWhole
  metric_eq := by
    intro variation hVariation boundary row column
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.metric_eq hVariation
    exact congrArg (fun field => field boundary row column) hWhole
  inverse_eq := by
    intro variation hVariation boundary first second
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.inverse_eq hVariation
    exact congrArg (fun field => field boundary first second) hWhole
  orientation_eq := by
    intro variation hVariation boundary
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.orientation_eq
      hVariation
    exact congrArg (fun field => field boundary) hWhole
  density_eq := by
    intro variation hVariation boundary
    have hWhole := OpenGermDomain.ofEventuallyEq_apply data.density_eq hVariation
    exact congrArg (fun field => field boundary) hWhole

/-- Eventual component identities close the two-sheet action germ directly. -/
def candidate_a_normal_boundary_eventuallyEq_terminal_gate
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
    (data : NormalBoundaryEventuallyEqGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base)
    (measure : Measure Boundary) :=
  data.toSeparated.toComponentwise.twoSheetActionGerm measure

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryEventuallyEqGerms4D
end JanusFormal
