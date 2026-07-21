import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D

/-!
# Local-section criterion for continuous ambient Pin-minus lifts

The current Clifford and orthogonal types carry no canonical topology in the
imported Mathlib API, so pointwise surjectivity alone cannot produce a
continuous lift.  This gate isolates the exact remaining topological input.

First, the Cartan--Dieudonné lift is total and projects to every genuine
reduced tangent transition.  It is a continuous overlap lift exactly when
that selected total function is continuous on the overlap.  Second, for any
chosen topologies, local continuous sections of `Pin⁻(4) → O(4)` compose with
continuous reduced transitions to give continuous lifts on open overlap
neighborhoods.  No local-section existence or Čech coherence is assumed as a
conclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientOrthogonalIsometry :=
  ambientCoverEuclideanQuadraticForm.IsometryEquiv
    ambientCoverEuclideanQuadraticForm

/-- Identity fallback outside a genuine transition source. -/
def ambientLocalSectionIdentityOrthogonalIsometry :
    AmbientOrthogonalIsometry where
  __ := LinearEquiv.refl Real CoverCoordinates
  map_app' _ := rfl

/-- Totalized reduced tangent transition.  Only its restriction to the real
overlap source has geometric meaning. -/
def ambientReducedTangentTransition
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientOrthogonalIsometry := by
  classical
  exact if hCoordinate : coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source then
      reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate
    else
      ambientLocalSectionIdentityOrthogonalIsometry

theorem ambientReducedTangentTransition_eq_on_source
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientReducedTangentTransition period hPeriod reduction first second
        coordinate =
      reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate := by
  classical
  rw [ambientReducedTangentTransition, dif_pos hCoordinate]

/-- Totalized Cartan--Dieudonné Pin-minus selection.  No regularity outside or
inside the overlap is built into classical choice. -/
def ambientPinMinusTotalPointwiseTangentTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientCoordinatePinMinusGroup := by
  classical
  exact if hCoordinate : coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source then
      ambientPinMinusPointwiseTangentTransitionLift period hPeriod reduction
        first second coordinate hCoordinate
    else
      1

/-- The total pointwise selection has the exact required projection on every
genuine overlap point. -/
theorem ambientPinMinusTotalPointwiseTangentTransitionLift_projects_on_source
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientPinMinusProjection
        (ambientPinMinusTotalPointwiseTangentTransitionLift period hPeriod
          reduction first second coordinate) =
      (reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv := by
  classical
  rw [ambientPinMinusTotalPointwiseTangentTransitionLift,
    dif_pos hCoordinate]
  exact ambientPinMinusPointwiseTangentTransitionLift_projects period hPeriod
    reduction first second coordinate hCoordinate

/-- Actual data of a continuous Pin-minus lift on a subset of one genuine
overlap.  This carries the lift function and its exact projection, not merely
readiness propositions. -/
structure AmbientPinMinusContinuousReducedTangentLiftOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (domain : Set CoverModel) where
  domain_subset_source : domain ⊆
    (ambientAtlasTransition period hPeriod first second).source
  lift : CoverModel → AmbientCoordinatePinMinusGroup
  continuousOn : ContinuousOn lift domain
  projects : ∀ coordinate (hCoordinate : coordinate ∈ domain),
    ambientPinMinusProjection (lift coordinate) =
      (reduction.orthogonalTransition period hPeriod first second coordinate
        (domain_subset_source hCoordinate)).toLinearEquiv

/-- If the explicit pointwise selection is continuous on a chosen subdomain,
it already supplies the complete local continuous lifting datum there. -/
def ambientPinMinusContinuousReducedTangentLiftOnOfPointwiseSelection
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (domain : Set CoverModel)
    (hDomain : domain ⊆
      (ambientAtlasTransition period hPeriod first second).source)
    (hContinuous : ContinuousOn
      (ambientPinMinusTotalPointwiseTangentTransitionLift period hPeriod
        reduction first second) domain) :
    AmbientPinMinusContinuousReducedTangentLiftOn period hPeriod reduction
      first second domain where
  domain_subset_source := hDomain
  lift := ambientPinMinusTotalPointwiseTangentTransitionLift period hPeriod
    reduction first second
  continuousOn := hContinuous
  projects coordinate hCoordinate :=
    ambientPinMinusTotalPointwiseTangentTransitionLift_projects_on_source
      period hPeriod reduction first second coordinate (hDomain hCoordinate)

/-- Exact continuity frontier for the selected pointwise lift: promotion to
local lifting data with the same function is equivalent to its continuity. -/
theorem ambientPinMinusPointwiseSelection_continuous_iff_promotes
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (domain : Set CoverModel)
    (hDomain : domain ⊆
      (ambientAtlasTransition period hPeriod first second).source) :
    ContinuousOn
        (ambientPinMinusTotalPointwiseTangentTransitionLift period hPeriod
          reduction first second) domain ↔
      ∃ localLift : AmbientPinMinusContinuousReducedTangentLiftOn period hPeriod
          reduction first second domain,
        localLift.lift =
          ambientPinMinusTotalPointwiseTangentTransitionLift period hPeriod
            reduction first second := by
  constructor
  · intro hContinuous
    exact ⟨ambientPinMinusContinuousReducedTangentLiftOnOfPointwiseSelection
      period hPeriod reduction first second domain hDomain hContinuous, rfl⟩
  · rintro ⟨localLift, hLift⟩
    rw [← hLift]
    exact localLift.continuousOn

/-- A continuous local section of the Pin-minus projection near one
orthogonal target, for explicitly supplied topologies. -/
structure AmbientPinMinusProjectionLocalSectionNear
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [TopologicalSpace AmbientOrthogonalIsometry]
    (target : AmbientOrthogonalIsometry) where
  carrier : Set AmbientOrthogonalIsometry
  carrier_isOpen : IsOpen carrier
  target_mem : target ∈ carrier
  localLift : AmbientOrthogonalIsometry → AmbientCoordinatePinMinusGroup
  localLift_continuousOn : ContinuousOn localLift carrier
  projects : ∀ current (_hCurrent : current ∈ carrier),
    ambientPinMinusProjection (localLift current) = current.toLinearEquiv

/-- Exact missing covering-level input: a continuous local section around
every orthogonal target. -/
def AmbientPinMinusProjectionHasLocalSections
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [TopologicalSpace AmbientOrthogonalIsometry] : Prop :=
  ∀ target : AmbientOrthogonalIsometry,
    Nonempty (AmbientPinMinusProjectionLocalSectionNear target)

/-- Continuous lift data for an arbitrary orthogonal transition function. -/
structure AmbientPinMinusContinuousLiftOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [TopologicalSpace AmbientOrthogonalIsometry]
    (domain : Set CoverModel)
    (transition : CoverModel → AmbientOrthogonalIsometry) where
  lift : CoverModel → AmbientCoordinatePinMinusGroup
  continuousOn : ContinuousOn lift domain
  projects : ∀ coordinate (_hCoordinate : coordinate ∈ domain),
    ambientPinMinusProjection (lift coordinate) =
      (transition coordinate).toLinearEquiv

/-- Local sections of the projection compose with a continuous orthogonal
transition to produce continuous lifts on open neighborhoods. -/
theorem exists_open_continuousPinMinusLiftAround_of_localSections
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [TopologicalSpace AmbientOrthogonalIsometry]
    (hSections : AmbientPinMinusProjectionHasLocalSections)
    (domain : Set CoverModel)
    (hDomainOpen : IsOpen domain)
    (transition : CoverModel → AmbientOrthogonalIsometry)
    (hTransition : ContinuousOn transition domain)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈ domain) :
    ∃ neighborhood : Set CoverModel,
      IsOpen neighborhood ∧
      coordinate ∈ neighborhood ∧
      neighborhood ⊆ domain ∧
      Nonempty (AmbientPinMinusContinuousLiftOn neighborhood transition) := by
  rcases hSections (transition coordinate) with ⟨localSection⟩
  let neighborhood := domain ∩ transition ⁻¹' localSection.carrier
  have hNeighborhoodOpen : IsOpen neighborhood :=
    hTransition.isOpen_inter_preimage hDomainOpen localSection.carrier_isOpen
  have hCoordinateNeighborhood : coordinate ∈ neighborhood :=
    ⟨hCoordinate, localSection.target_mem⟩
  refine ⟨neighborhood, hNeighborhoodOpen, hCoordinateNeighborhood,
    inter_subset_left, ?_⟩
  refine ⟨{
    lift := localSection.localLift ∘ transition
    continuousOn := localSection.localLift_continuousOn.comp
      (hTransition.mono inter_subset_left) (fun _ hCurrent => hCurrent.2)
    projects := ?_ }⟩
  intro current hCurrent
  exact localSection.projects (transition current) hCurrent.2

/-- Specialization to the genuine reduced tangent transitions.  Thus, once
the two absent topological facts are supplied—local sections of the projection
and `O(4)`-valued continuity of the existing smooth reduction—every overlap
point has an open continuous Pin-minus lift with exact tangent projection. -/
theorem exists_open_continuousReducedTangentLiftAround_of_localSections
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [TopologicalSpace AmbientOrthogonalIsometry]
    (hSections : AmbientPinMinusProjectionHasLocalSections)
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (hTransition : ContinuousOn
      (ambientReducedTangentTransition period hPeriod reduction first second)
      (ambientAtlasTransition period hPeriod first second).source)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ∃ neighborhood : Set CoverModel,
      IsOpen neighborhood ∧
      coordinate ∈ neighborhood ∧
      Nonempty (AmbientPinMinusContinuousReducedTangentLiftOn period hPeriod
        reduction first second neighborhood) := by
  rcases exists_open_continuousPinMinusLiftAround_of_localSections
      hSections
      (ambientAtlasTransition period hPeriod first second).source
      (ambientAtlasTransition period hPeriod first second).open_source
      (ambientReducedTangentTransition period hPeriod reduction first second)
      hTransition coordinate hCoordinate with
    ⟨neighborhood, hNeighborhoodOpen, hCoordinateNeighborhood,
      hNeighborhoodSource, ⟨localLift⟩⟩
  refine ⟨neighborhood, hNeighborhoodOpen, hCoordinateNeighborhood, ⟨{
    domain_subset_source := hNeighborhoodSource
    lift := localLift.lift
    continuousOn := localLift.continuousOn
    projects := ?_ }⟩⟩
  intro current hCurrent
  have hProjects := localLift.projects current hCurrent
  rw [ambientReducedTangentTransition_eq_on_source period hPeriod reduction
    first second current (hNeighborhoodSource hCurrent)] at hProjects
  exact hProjects

end

end P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D
end JanusFormal
