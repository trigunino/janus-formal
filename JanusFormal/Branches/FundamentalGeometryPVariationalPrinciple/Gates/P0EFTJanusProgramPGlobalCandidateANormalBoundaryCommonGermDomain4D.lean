import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D

/-!
# Common open domains for the normal-boundary germ comparisons

The geometric ingredients of H10 are proved by different local constructions,
so their initial neighbourhoods need not be definitionally identical.  Since
only finitely many ingredients are involved, their intersection is again an
open neighbourhood of the anchor.  This file makes the restriction operation
explicit for every layer of the componentwise H10 chain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryCommonGermDomain4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

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

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D

/-- An open neighbourhood used as a common representative of a local germ. -/
structure OpenGermDomain (base : Variation) where
  carrier : Set Variation
  isOpen_carrier : IsOpen carrier
  base_mem_carrier : base ∈ carrier

/-- Intersection of two germ domains. -/
def OpenGermDomain.inter {base : Variation}
    (first second : OpenGermDomain base) : OpenGermDomain base where
  carrier := first.carrier ∩ second.carrier
  isOpen_carrier := first.isOpen_carrier.inter second.isOpen_carrier
  base_mem_carrier := ⟨first.base_mem_carrier, second.base_mem_carrier⟩

/-- The universal germ domain, useful as the neutral element of finite
intersection constructions. -/
def OpenGermDomain.univ (base : Variation) : OpenGermDomain base where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  base_mem_carrier := Set.mem_univ base

/-- Restrict a same-action germ to a smaller open neighbourhood. -/
def SameRealActionGermAt.restrict
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameRealActionGermAt completed historical base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  eqOn_domain := fun _ hPoint => germ.eqOn_domain (hSubset hPoint)

/-- Restrict a pointwise integrand germ. -/
def SameRealIntegrandGermAt.restrict
    {completed historical : Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealIntegrandGermAt completed historical base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameRealIntegrandGermAt completed historical base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  eqOn_domain := fun variation hVariation =>
    germ.eqOn_domain variation (hSubset hVariation)

/-- Restrict a factorwise GHY germ. -/
def SameRealGHYFactorGermAt.restrict
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  orientation_eq := fun variation hVariation =>
    germ.orientation_eq variation (hSubset hVariation)
  density_eq := fun variation hVariation =>
    germ.density_eq variation (hSubset hVariation)
  meanCurvature_eq := fun variation hVariation =>
    germ.meanCurvature_eq variation (hSubset hVariation)

/-- Restrict the inverse-metric/second-form contraction germ. -/
def SameContractedMeanCurvatureGermAt.restrict
    {completedInverse historicalInverse :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {completedSecondForm historicalSecondForm :
      Variation → Boundary → TangentIndex → TangentIndex → Real}
    {base : Variation}
    (germ : SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  inverse_eq := fun variation hVariation =>
    germ.inverse_eq variation (hSubset hVariation)
  secondForm_eq := fun variation hVariation =>
    germ.secondForm_eq variation (hSubset hVariation)

/-- Restrict the regular-frame covariant-acceleration germ. -/
def SameCovariantAccelerationGermAt.restrict
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
      completedChristoffel historicalChristoffel base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameCovariantAccelerationGermAt
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  tangent_eq := fun variation hVariation =>
    germ.tangent_eq variation (hSubset hVariation)
  tangentDerivative_eq := fun variation hVariation =>
    germ.tangentDerivative_eq variation (hSubset hVariation)
  christoffel_eq := fun variation hVariation =>
    germ.christoffel_eq variation (hSubset hVariation)

/-- Restrict the Gauss second-form germ. -/
def SameGaussSecondFormGermAt.restrict
    {completedNormal historicalNormal :
      Variation → Boundary → AmbientIndex → Real}
    {completedMetric historicalMetric :
      Variation → Boundary → AmbientIndex → AmbientIndex → Real}
    {completedAcceleration historicalAcceleration :
      Variation → Boundary → TangentIndex → TangentIndex → AmbientIndex → Real}
    {base : Variation}
    (germ : SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      completedAcceleration historicalAcceleration base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ germ.domain) :
    SameGaussSecondFormGermAt
      completedNormal historicalNormal completedMetric historicalMetric
      completedAcceleration historicalAcceleration base where
  domain := domain.carrier
  isOpen_domain := domain.isOpen_carrier
  base_mem_domain := domain.base_mem_carrier
  normal_eq := fun variation hVariation =>
    germ.normal_eq variation (hSubset hVariation)
  metric_eq := fun variation hVariation =>
    germ.metric_eq variation (hSubset hVariation)
  acceleration_eq := fun variation hVariation =>
    germ.acceleration_eq variation (hSubset hVariation)

/-- Restrict the full componentwise packet. -/
def NormalBoundaryComponentwiseGermData.restrict
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
    (data : NormalBoundaryComponentwiseGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base)
    (domain : OpenGermDomain base)
    (hSubset : domain.carrier ⊆ data.acceleration.domain) :
    NormalBoundaryComponentwiseGermData
      completedTangent historicalTangent
      completedTangentDerivative historicalTangentDerivative
      completedChristoffel historicalChristoffel
      completedNormal historicalNormal completedMetric historicalMetric
      completedInverse historicalInverse
      completedOrientation historicalOrientation
      completedDensity historicalDensity base where
  acceleration := data.acceleration.restrict domain hSubset
  normal_eq := fun variation hVariation =>
    data.normal_eq variation (hSubset hVariation)
  metric_eq := fun variation hVariation =>
    data.metric_eq variation (hSubset hVariation)
  inverse_eq := fun variation hVariation =>
    data.inverse_eq variation (hSubset hVariation)
  orientation_eq := fun variation hVariation =>
    data.orientation_eq variation (hSubset hVariation)
  density_eq := fun variation hVariation =>
    data.density_eq variation (hSubset hVariation)

/-- The intersection domain embeds in both original domains. -/
theorem OpenGermDomain.inter_subset_left
    {base : Variation} (first second : OpenGermDomain base) :
    (first.inter second).carrier ⊆ first.carrier :=
  fun _ hPoint => hPoint.1

/-- The intersection domain embeds in the second original domain. -/
theorem OpenGermDomain.inter_subset_right
    {base : Variation} (first second : OpenGermDomain base) :
    (first.inter second).carrier ⊆ second.carrier :=
  fun _ hPoint => hPoint.2

/-- Public common-domain gate. -/
theorem candidate_a_normal_boundary_common_germ_domain_gate
    {base : Variation} (first second : OpenGermDomain base) :
    IsOpen (first.inter second).carrier ∧
      base ∈ (first.inter second).carrier ∧
      (first.inter second).carrier ⊆ first.carrier ∧
      (first.inter second).carrier ⊆ second.carrier :=
  ⟨(first.inter second).isOpen_carrier,
    (first.inter second).base_mem_carrier,
    first.inter_subset_left second,
    first.inter_subset_right second⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryCommonGermDomain4D
end JanusFormal
