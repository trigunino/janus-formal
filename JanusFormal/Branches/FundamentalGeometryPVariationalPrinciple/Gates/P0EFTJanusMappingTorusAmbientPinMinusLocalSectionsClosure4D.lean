import Mathlib.Topology.Covering.Quotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusCompactness4D

/-!
# Concrete reduction for ambient Pin-minus local sections

The existing principal-bundle cores are bundles over the ambient mapping
torus.  Their local trivializations therefore do not trivialize the group
projection `Pin⁻(4) → O(4)`.

This gate records the strongest non-circular reduction supplied by the
current topology: compactness of the concrete Pin group and finiteness of the
kernel make the continuous surjective projection a covering map.  Its local
inverses then give the required local sections.  Neither compactness nor
kernel finiteness is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D
open P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D
open P0EFTJanusMappingTorusAmbientPinMinusCompactness4D

private abbrev AmbientOrthogonalIsometry :=
  ambientCoverEuclideanQuadraticForm.IsometryEquiv
    ambientCoverEuclideanQuadraticForm

private theorem ambientPinMinusProjectionHasLocalSections_of_isLocalHomeomorph
    (hLocal : IsLocalHomeomorph
      (ambientPinMinusOrthogonalProjection :
        AmbientCoordinatePinMinusGroup → AmbientOrthogonalIsometry)) :
    AmbientPinMinusProjectionHasLocalSections := by
  intro target
  rcases ambientPinMinusOrthogonalProjection_surjective target with
    ⟨lift, hLift⟩
  refine ⟨{
    carrier := (hLocal.localInverseAt lift).source
    carrier_isOpen := (hLocal.localInverseAt lift).open_source
    target_mem := ?_
    localLift := hLocal.localInverseAt lift
    localLift_continuousOn := (hLocal.localInverseAt lift).continuousOn
    projects := ?_ }⟩
  · rw [← hLift]
    exact hLocal.apply_self_mem_localInverseAt_source
  · intro current hCurrent
    have hProjection :
        ambientPinMinusOrthogonalProjection
            (hLocal.localInverseAt lift current) =
          current :=
      hLocal.apply_localInverseAt_of_mem hCurrent
    exact
      (ambientPinMinusOrthogonalProjection_toLinearEquiv
        (hLocal.localInverseAt lift current)).symm.trans
        (congrArg
          (fun orthogonal : AmbientOrthogonalIsometry =>
            orthogonal.toLinearEquiv)
          hProjection)

/-- A compact concrete Pin group with finite projection kernel has the local
sections required by the ambient criterion.  These hypotheses are strictly
about the already-defined source and projection; they do not contain local
sections or overlap lifts as assumptions. -/
theorem ambientPinMinusProjectionHasLocalSections_of_compact_finiteKernel
    (hCompact :
      IsCompact (Set.univ : Set AmbientCoordinatePinMinusGroup))
    (hKernelFinite :
      ((ambientPinMinusOrthogonalProjection.ker :
          Subgroup AmbientCoordinatePinMinusGroup) :
        Set AmbientCoordinatePinMinusGroup).Finite) :
    AmbientPinMinusProjectionHasLocalSections := by
  letI : T2Space AmbientLinearEquiv :=
    ambientLinearEquivMatrixCoordinates_isEmbedding.t2Space
  letI : T2Space AmbientOrthogonalIsometry :=
    ambientOrthogonalToLinearEquiv_isEmbedding.t2Space
  letI : CompactSpace AmbientCoordinatePinMinusGroup :=
    isCompact_univ_iff.mp hCompact
  have hQuotient :
      IsQuotientMap
        (ambientPinMinusOrthogonalProjection :
          AmbientCoordinatePinMinusGroup → AmbientOrthogonalIsometry) :=
    IsQuotientMap.of_surjective_continuous
      ambientPinMinusOrthogonalProjection_surjective
      continuous_ambientPinMinusOrthogonalProjection
  have hKernelDiscrete :
      IsDiscrete
        ((ambientPinMinusOrthogonalProjection.ker :
            Subgroup AmbientCoordinatePinMinusGroup) :
          Set AmbientCoordinatePinMinusGroup) :=
    hKernelFinite.isDiscrete
  have hCovering :
      IsCoveringMap
        (ambientPinMinusOrthogonalProjection :
          AmbientCoordinatePinMinusGroup → AmbientOrthogonalIsometry) :=
    (hQuotient.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      hKernelDiscrete).isCoveringMap
  exact
    ambientPinMinusProjectionHasLocalSections_of_isLocalHomeomorph
      hCovering.isLocalHomeomorph

/-- The exact two-element kernel theorem removes the finite-kernel hypothesis;
only compactness of the concrete Pin group remains. -/
theorem ambientPinMinusProjectionHasLocalSections_of_compact
    (hCompact :
      IsCompact (Set.univ : Set AmbientCoordinatePinMinusGroup)) :
    AmbientPinMinusProjectionHasLocalSections :=
  ambientPinMinusProjectionHasLocalSections_of_compact_finiteKernel
    hCompact ambientPinMinusOrthogonalProjection_kernel_finite

/-- The concrete Pin-minus projection now has local sections with no residual
hypothesis: its source is compact and its kernel is exactly `{±1}`. -/
theorem ambientPinMinusProjectionHasLocalSections_closed :
    AmbientPinMinusProjectionHasLocalSections :=
  ambientPinMinusProjectionHasLocalSections_of_compact
    isCompact_univ_ambientCoordinatePinMinusGroup

end

end P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D
end JanusFormal
