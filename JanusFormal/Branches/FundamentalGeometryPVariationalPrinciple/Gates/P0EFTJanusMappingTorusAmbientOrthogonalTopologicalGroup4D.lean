import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D

/-!
# Topological group structure on the ambient orthogonal target

The concrete `O(4)` target already carries its induced matrix topology and
its genuine group structure.  This gate proves that multiplication and
inversion are continuous for exactly that topology.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientOrthogonalTopologicalGroup4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D
open P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D

private theorem ambientLinearEquivMatrixCoordinates_mul
    (first second : AmbientLinearEquiv) :
    ambientLinearEquivMatrixCoordinates (first * second) =
      ambientLinearEquivMatrixCoordinates first *
        ambientLinearEquivMatrixCoordinates second := by
  unfold ambientLinearEquivMatrixCoordinates
  exact LinearMap.toMatrix_mul _ first.toLinearMap second.toLinearMap

private theorem ambientLinearEquivMatrixCoordinates_symm
    (equiv : AmbientLinearEquiv) :
    ambientLinearEquivMatrixCoordinates equiv.symm =
      (ambientLinearEquivMatrixCoordinates equiv)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← ambientLinearEquivMatrixCoordinates_mul]
  unfold ambientLinearEquivMatrixCoordinates
  have hEquiv : equiv.symm * equiv = 1 := by
    apply LinearEquiv.ext
    intro (tangent : CoverCoordinates)
    exact equiv.symm_apply_apply tangent
  rw [hEquiv]
  change LinearMap.toMatrix _ _
    (1 : CoverCoordinates →ₗ[Real] CoverCoordinates) = 1
  exact LinearMap.toMatrix_one _

private theorem ambientLinearEquivMatrixCoordinates_det_ne_zero
    (equiv : AmbientLinearEquiv) :
    (ambientLinearEquivMatrixCoordinates equiv).det ≠ 0 := by
  unfold ambientLinearEquivMatrixCoordinates
  exact (LinearEquiv.isUnit_det equiv _ _).ne_zero

private theorem ambientOrthogonalMatrixCoordinates_mul
    (first second : AmbientOrthogonalIsometry) :
    ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv (first * second)) =
      ambientLinearEquivMatrixCoordinates
          (ambientOrthogonalToLinearEquiv first) *
        ambientLinearEquivMatrixCoordinates
          (ambientOrthogonalToLinearEquiv second) := by
  change ambientLinearEquivMatrixCoordinates
      (ambientOrthogonalToLinearEquiv first *
        ambientOrthogonalToLinearEquiv second) = _
  exact ambientLinearEquivMatrixCoordinates_mul _ _

private theorem ambientOrthogonalMatrixCoordinates_inv
    (equiv : AmbientOrthogonalIsometry) :
    ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv equiv⁻¹) =
      (ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv equiv))⁻¹ := by
  change ambientLinearEquivMatrixCoordinates
      (ambientOrthogonalToLinearEquiv equiv).symm = _
  exact ambientLinearEquivMatrixCoordinates_symm _

private theorem continuous_ambientOrthogonalMatrixCoordinates :
    Continuous (fun equiv : AmbientOrthogonalIsometry =>
      ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv equiv)) := by
  exact ambientLinearEquivMatrixCoordinates_isEmbedding.continuous.comp
    ambientOrthogonalToLinearEquiv_isEmbedding.continuous

/-- The faithful matrix topology on `GL(4)` is Hausdorff. -/
noncomputable instance ambientLinearEquivT2Space :
    T2Space AmbientLinearEquiv :=
  ambientLinearEquivMatrixCoordinates_isEmbedding.t2Space

/-- The induced faithful matrix topology on the concrete `O(4)` is
Hausdorff. -/
noncomputable instance ambientOrthogonalIsometryT2Space :
    T2Space AmbientOrthogonalIsometry :=
  ambientOrthogonalToLinearEquiv_isEmbedding.t2Space

/-- Multiplication on the concrete ambient orthogonal group is continuous in
its faithful matrix-coordinate topology. -/
theorem continuous_ambientOrthogonalIsometry_mul :
    Continuous (fun pair :
      AmbientOrthogonalIsometry × AmbientOrthogonalIsometry =>
        pair.1 * pair.2) := by
  rw [ambientOrthogonalToLinearEquiv_isEmbedding.continuous_iff,
    ambientLinearEquivMatrixCoordinates_isEmbedding.continuous_iff]
  change Continuous (fun pair :
    AmbientOrthogonalIsometry × AmbientOrthogonalIsometry =>
      ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv (pair.1 * pair.2)))
  have hCoordinates := continuous_ambientOrthogonalMatrixCoordinates
  have hProduct :=
    (hCoordinates.comp continuous_fst).matrix_mul
      (hCoordinates.comp continuous_snd)
  simpa only [Function.comp_apply] using hProduct.congr fun pair =>
    (ambientOrthogonalMatrixCoordinates_mul pair.1 pair.2).symm

/-- Inversion on the concrete ambient orthogonal group is continuous in its
faithful matrix-coordinate topology. -/
theorem continuous_ambientOrthogonalIsometry_inv :
    Continuous (fun equiv : AmbientOrthogonalIsometry => equiv⁻¹) := by
  rw [ambientOrthogonalToLinearEquiv_isEmbedding.continuous_iff,
    ambientLinearEquivMatrixCoordinates_isEmbedding.continuous_iff]
  change Continuous (fun equiv : AmbientOrthogonalIsometry =>
    ambientLinearEquivMatrixCoordinates
      (ambientOrthogonalToLinearEquiv equiv⁻¹))
  have hMatrixInverse : Continuous (fun equiv : AmbientOrthogonalIsometry =>
      (ambientLinearEquivMatrixCoordinates
        (ambientOrthogonalToLinearEquiv equiv))⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro equiv
    have hScalarInverse : ContinuousAt Ring.inverse
        (ambientLinearEquivMatrixCoordinates
          (ambientOrthogonalToLinearEquiv equiv)).det := by
      simpa only [Ring.inverse_eq_inv'] using
        continuousAt_inv₀
          (ambientLinearEquivMatrixCoordinates_det_ne_zero
            (ambientOrthogonalToLinearEquiv equiv))
    exact ContinuousAt.comp'
      (f := fun candidate : AmbientOrthogonalIsometry =>
        ambientLinearEquivMatrixCoordinates
          (ambientOrthogonalToLinearEquiv candidate))
      (g := fun matrix : Matrix (Fin 4) (Fin 4) Real => matrix⁻¹)
      (continuousAt_matrix_inv
        (ambientLinearEquivMatrixCoordinates
          (ambientOrthogonalToLinearEquiv equiv)) hScalarInverse)
      continuous_ambientOrthogonalMatrixCoordinates.continuousAt
  simpa only [Function.comp_apply] using hMatrixInverse.congr fun equiv =>
    (ambientOrthogonalMatrixCoordinates_inv equiv).symm

/-- The existing concrete `O(4)` target is an honest topological group. -/
noncomputable instance ambientOrthogonalIsometryIsTopologicalGroup :
    IsTopologicalGroup AmbientOrthogonalIsometry where
  continuous_mul := continuous_ambientOrthogonalIsometry_mul
  continuous_inv := continuous_ambientOrthogonalIsometry_inv

end

end P0EFTJanusMappingTorusAmbientOrthogonalTopologicalGroup4D
end JanusFormal
