import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D

/-!
# Propagation of the closed ambient Pin-minus local sections

The compactness and exact-kernel gates make the local-section criterion
unconditional.  Consequently every smooth orthonormal reduction has
continuous Pin-minus lifts on open neighborhoods of all genuine overlap
points.

The current Cech interface asks in addition for one lift on each whole
overlap, normalization, triple-overlap coherence and the prescribed normal
restriction.  Local sections alone do not supply those global compatibility
data.  Once such a Cech choice is available, the existing API packages it
into a principal bundle without any further hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsPropagation4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientOrthogonalIsometry :=
  ambientCoverEuclideanQuadraticForm.IsometryEquiv
    ambientCoverEuclideanQuadraticForm

/-- Every continuous orthogonal transition has a continuous Pin-minus lift
on an open neighborhood of each point of its domain. -/
theorem exists_open_continuousPinMinusLiftAround_closed
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
      Nonempty (AmbientPinMinusContinuousLiftOn neighborhood transition) :=
  exists_open_continuousPinMinusLiftAround_of_localSections
    ambientPinMinusProjectionHasLocalSections_closed domain hDomainOpen
      transition hTransition coordinate hCoordinate

/-- Unconditional local lifting of every genuine reduced tangent transition
associated with a smooth orthonormal reduction. -/
theorem exists_open_continuousReducedTangentLiftAround_closed
    (reduction : AmbientContMDiffOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ∃ neighborhood : Set CoverModel,
      IsOpen neighborhood ∧
      coordinate ∈ neighborhood ∧
      Nonempty (AmbientPinMinusContinuousReducedTangentLiftOn period hPeriod
        reduction.toPointwise first second neighborhood) :=
  exists_open_continuousReducedTangentLiftAround_of_localSections_of_smoothReduction
    period hPeriod reduction ambientPinMinusProjectionHasLocalSections_closed
      first second coordinate hCoordinate

/-- All overlap points of a smooth reduction have the preceding open
continuous lifts; this is the strongest local Cech precursor furnished by
the local-section API. -/
theorem ambientSmoothReduction_has_open_continuousPinMinusLocalTransitions
    (reduction : AmbientContMDiffOrthonormalAtlasReduction period hPeriod) :
    ∀ first second : AmbientCover period hPeriod,
      ∀ coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source,
        ∃ neighborhood : Set CoverModel,
          IsOpen neighborhood ∧
          coordinate ∈ neighborhood ∧
          Nonempty (AmbientPinMinusContinuousReducedTangentLiftOn
            period hPeriod reduction.toPointwise first second neighborhood) := by
  intro first second coordinate hCoordinate
  exact exists_open_continuousReducedTangentLiftAround_closed
    period hPeriod reduction first second coordinate hCoordinate

/-- A global normal-compatible continuous Cech choice is exactly sufficient
for the existing principal-bundle constructor; local sections add no further
obligation at this stage. -/
theorem ambientPinMinusPrincipalBundle_nonempty_of_cechChoiceExists
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (hChoice : AmbientNormalCompatibleContinuousPinMinusCechChoiceExists
      period hPeriod reduction) :
    Nonempty (AmbientPinMinusPrincipalBundle period hPeriod reduction) := by
  rcases hChoice with ⟨choice⟩
  exact ⟨ambientPinMinusPrincipalBundleOfCechChoice
    period hPeriod reduction choice⟩

end

end P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsPropagation4D
end JanusFormal
