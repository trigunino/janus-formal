import Mathlib.LinearAlgebra.Matrix.ToLin
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D

/-!
# Continuity of the ambient Pin-minus projection

The existing morphism `ambientPinMinusProjection` lands in real linear
equivalences.  It is not silently replaced here by a bundled map to `O(4)`:
the latter would additionally require a general quadratic-preservation proof.

This gate equips `GL(4)` with its faithful matrix-coordinate topology and
`O(4)` with the induced subspace topology.  It proves continuity of the
existing twisted projection, and uses the already-proved joint smoothness of
the Whitney reduction to discharge the `O(4)`-valued transition-continuity
hypothesis in the local-section criterion.  Existence of local sections is
still an explicit hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D

set_option autoImplicit false

noncomputable section

open Set Module Topology
open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D

private abbrev AmbientPinMinusIotaRange :=
  LinearMap.range
    (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm)

/-- The canonical vector inclusion, restricted to its range, is a continuous
linear equivalence for the faithful Clifford coordinate topology. -/
def ambientPinMinusCliffordIotaRangeEquiv :
    CoverCoordinates ≃L[Real] AmbientPinMinusIotaRange :=
  (LinearEquiv.ofInjective
    (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm)
    ambientPinMinusCliffordIota_injective).toContinuousLinearEquiv

/-- The twisted Clifford conjugate, bundled in the actual range of the vector
inclusion. -/
def ambientPinMinusTwistedVectorInIotaRange
    (input : AmbientCoordinatePinMinusGroup × CoverCoordinates) :
    AmbientPinMinusIotaRange :=
  ⟨involute (input.1 : AmbientPinMinusCliffordAlgebra) *
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm input.2 *
      (↑(input.1⁻¹) : AmbientPinMinusCliffordAlgebra),
    ⟨ambientPinMinusVectorAction input.1 input.2,
      ambientPinMinusVectorAction_spec input.1 input.2⟩⟩

theorem continuous_ambientPinMinusTwistedVectorInIotaRange :
    Continuous ambientPinMinusTwistedVectorInIotaRange := by
  apply continuous_induced_rng.mpr
  have hInvolute : Continuous (fun input :
      AmbientCoordinatePinMinusGroup × CoverCoordinates =>
      involute (input.1 : AmbientPinMinusCliffordAlgebra)) := by
    have hLinear : Continuous
        (CliffordAlgebra.involute
          (Q := ambientCoverPinMinusQuadraticForm)).toLinearMap :=
      LinearMap.continuous_of_finiteDimensional _
    exact hLinear.comp (continuous_subtype_val.comp continuous_fst)
  have hIota : Continuous (fun input :
      AmbientCoordinatePinMinusGroup × CoverCoordinates =>
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm input.2) :=
    (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm).continuous_of_finiteDimensional.comp
      continuous_snd
  have hInverse : Continuous (fun input :
      AmbientCoordinatePinMinusGroup × CoverCoordinates =>
      (↑(input.1⁻¹) : AmbientPinMinusCliffordAlgebra)) :=
    continuous_subtype_val.comp (continuous_inv.comp continuous_fst)
  exact (hInvolute.mul hIota).mul hInverse

theorem ambientPinMinusVectorAction_eq_iotaRangeEquiv_symm
    (input : AmbientCoordinatePinMinusGroup × CoverCoordinates) :
    ambientPinMinusVectorAction input.1 input.2 =
      ambientPinMinusCliffordIotaRangeEquiv.symm
        (ambientPinMinusTwistedVectorInIotaRange input) := by
  apply ambientPinMinusCliffordIota_injective
  have hRange := congrArg Subtype.val
    (ambientPinMinusCliffordIotaRangeEquiv.apply_symm_apply
      (ambientPinMinusTwistedVectorInIotaRange input))
  exact (ambientPinMinusVectorAction_spec input.1 input.2).trans hRange.symm

/-- The true twisted Pin action is jointly continuous in the Pin element and
the ambient vector. -/
theorem continuous_ambientPinMinusVectorAction_uncurried :
    Continuous (fun input : AmbientCoordinatePinMinusGroup × CoverCoordinates =>
      ambientPinMinusVectorAction input.1 input.2) := by
  rw [show (fun input : AmbientCoordinatePinMinusGroup × CoverCoordinates =>
      ambientPinMinusVectorAction input.1 input.2) =
      fun input => ambientPinMinusCliffordIotaRangeEquiv.symm
        (ambientPinMinusTwistedVectorInIotaRange input) by
    funext input
    exact ambientPinMinusVectorAction_eq_iotaRangeEquiv_symm input]
  exact ambientPinMinusCliffordIotaRangeEquiv.symm.continuous.comp
    continuous_ambientPinMinusTwistedVectorInIotaRange

private def ambientCoverCoordinateBasis :
    Basis (Fin 4) Real CoverCoordinates :=
  Module.finBasisOfFinrankEq Real CoverCoordinates (by
    norm_num [CoverCoordinates])

abbrev AmbientLinearEquiv :=
  CoverCoordinates ≃ₗ[Real] CoverCoordinates

/-- Faithful `4 × 4` matrix coordinates on the existing projection target. -/
def ambientLinearEquivMatrixCoordinates
    (equiv : AmbientLinearEquiv) : Matrix (Fin 4) (Fin 4) Real :=
  LinearMap.toMatrix ambientCoverCoordinateBasis ambientCoverCoordinateBasis
    equiv.toLinearMap

theorem ambientLinearEquivMatrixCoordinates_injective :
    Function.Injective ambientLinearEquivMatrixCoordinates := by
  intro first second hMatrix
  apply LinearEquiv.ext
  exact LinearMap.congr_fun
    ((LinearMap.toMatrix ambientCoverCoordinateBasis
      ambientCoverCoordinateBasis).injective hMatrix)

/-- The usual finite-dimensional matrix-coordinate topology on `GL(4)`. -/
noncomputable instance ambientLinearEquivTopologicalSpace :
    TopologicalSpace AmbientLinearEquiv :=
  TopologicalSpace.induced ambientLinearEquivMatrixCoordinates inferInstance

theorem ambientLinearEquivMatrixCoordinates_isEmbedding :
    IsEmbedding ambientLinearEquivMatrixCoordinates :=
  { IsInducing.induced ambientLinearEquivMatrixCoordinates with
    injective := ambientLinearEquivMatrixCoordinates_injective }

private theorem continuous_ambientPinMinusVectorAction_fixed
    (tangent : CoverCoordinates) :
    Continuous (fun lift : AmbientCoordinatePinMinusGroup =>
      ambientPinMinusVectorAction lift tangent) :=
  continuous_ambientPinMinusVectorAction_uncurried.comp
    (continuous_id.prodMk continuous_const)

/-- The existing multiplicative twisted projection to `GL(4)` is continuous
for the faithful finite-dimensional topologies on source and target. -/
theorem continuous_ambientPinMinusProjection :
    Continuous ambientPinMinusProjection := by
  rw [ambientLinearEquivMatrixCoordinates_isEmbedding.continuous_iff]
  apply continuous_pi
  intro first
  apply continuous_pi
  intro second
  have hCoordinate : Continuous
      (ambientCoverCoordinateBasis.coord first) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hCoordinate.comp
    (continuous_ambientPinMinusVectorAction_fixed
      (ambientCoverCoordinateBasis second))).congr ?_
  intro lift
  simp only [Function.comp_apply, ambientLinearEquivMatrixCoordinates,
    LinearMap.toMatrix_apply, ← Basis.coord_apply]
  rfl

abbrev AmbientOrthogonalIsometry :=
  ambientCoverEuclideanQuadraticForm.IsometryEquiv
    ambientCoverEuclideanQuadraticForm

/-- The actual inclusion `O(4) → GL(4)`. -/
def ambientOrthogonalToLinearEquiv
    (equiv : AmbientOrthogonalIsometry) : AmbientLinearEquiv :=
  equiv.toLinearEquiv

/-- The honest subspace topology on the concrete `O(4)`. -/
noncomputable instance ambientOrthogonalIsometryTopologicalSpace :
    TopologicalSpace AmbientOrthogonalIsometry :=
  TopologicalSpace.induced ambientOrthogonalToLinearEquiv inferInstance

theorem ambientOrthogonalToLinearEquiv_injective :
    Function.Injective ambientOrthogonalToLinearEquiv := by
  intro first second hEqual
  cases first with
  | mk first hFirst =>
      cases second with
      | mk second hSecond =>
          simp only [ambientOrthogonalToLinearEquiv,
            QuadraticMap.IsometryEquiv.toLinearEquiv] at hEqual
          cases hEqual
          rfl

theorem ambientOrthogonalToLinearEquiv_isEmbedding :
    IsEmbedding ambientOrthogonalToLinearEquiv :=
  { IsInducing.induced ambientOrthogonalToLinearEquiv with
    injective := ambientOrthogonalToLinearEquiv_injective }

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- Joint `C∞` regularity of an orthonormal reduction implies continuity of
its genuine `O(4)`-valued overlap transition for the matrix topology above. -/
theorem ambientReducedTangentTransition_continuousOn
    (reduction : AmbientContMDiffOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (ambientReducedTangentTransition period hPeriod reduction.toPointwise
        first second)
      (ambientAtlasTransition period hPeriod first second).source := by
  rw [ambientOrthogonalToLinearEquiv_isEmbedding.continuousOn_iff,
    ambientLinearEquivMatrixCoordinates_isEmbedding.continuousOn_iff]
  apply continuousOn_pi.mpr
  intro row
  apply continuousOn_pi.mpr
  intro column
  have hApplied : ContinuousOn
      (fun coordinate =>
        reductionOrthogonalTransitionApplication period hPeriod
          reduction.toPointwise first second
          (coordinate, ambientCoverCoordinateBasis column))
      (ambientAtlasTransition period hPeriod first second).source :=
    (reduction.transition_contMDiffOn first second).continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun _ hCoordinate => ⟨hCoordinate, Set.mem_univ _⟩)
  have hCoordinate : Continuous
      (ambientCoverCoordinateBasis.coord row) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hCoordinate.comp_continuousOn hApplied).congr ?_
  intro coordinate hCoordinateSource
  simp only [Function.comp_apply, ambientOrthogonalToLinearEquiv,
    ambientLinearEquivMatrixCoordinates, LinearMap.toMatrix_apply,
    Basis.coord_apply]
  rw [ambientReducedTangentTransition_eq_on_source period hPeriod
    reduction.toPointwise first second coordinate hCoordinateSource]
  simp only [reductionOrthogonalTransitionApplication,
    hCoordinateSource, dite_true]
  rfl

/-- The local-section criterion now needs only its genuinely unresolved
input, namely existence of local sections.  Transition continuity is supplied
by the smooth Whitney-compatible reduction. -/
theorem exists_open_continuousReducedTangentLiftAround_of_localSections_of_smoothReduction
    (reduction : AmbientContMDiffOrthonormalAtlasReduction period hPeriod)
    (hSections : AmbientPinMinusProjectionHasLocalSections)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ∃ neighborhood : Set CoverModel,
      IsOpen neighborhood ∧
      coordinate ∈ neighborhood ∧
      Nonempty (AmbientPinMinusContinuousReducedTangentLiftOn period hPeriod
        reduction.toPointwise first second neighborhood) :=
  exists_open_continuousReducedTangentLiftAround_of_localSections
    period hPeriod hSections reduction.toPointwise first second
    (ambientReducedTangentTransition_continuousOn period hPeriod reduction
      first second) coordinate hCoordinate

end

end P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D
end JanusFormal
