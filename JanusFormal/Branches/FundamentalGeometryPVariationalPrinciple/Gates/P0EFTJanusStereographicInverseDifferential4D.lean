import Mathlib.Geometry.Manifold.Instances.Sphere
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D

/-! # Stereographic inverse differential

The chart convention in Mathlib has scale one at the origin. Its conformal
factor is therefore `4 / (‖w‖² + 4)`, not the factor for unit-scale projection.
-/

namespace JanusFormal
namespace P0EFTJanusStereographicInverseDifferential4D

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Exact derivative on the ambient space, before restricting to the pole's
orthogonal complement. -/
theorem stereoInvFunAux_fderiv_apply (v w u : E) :
    fderiv Real (stereoInvFunAux v) w u =
      (-(‖w‖ ^ 2 + 4)⁻¹ ^ 2 * (2 * ⟪w, u⟫)) •
          ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v) +
        (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • u + (2 * ⟪w, u⟫) • v) := by
  have hNorm := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hDenom := hNorm.add_const (4 : Real)
  have hNe : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hInverse := (hasDerivAt_inv hNe).comp_hasFDerivAt w hDenom
  have hNumerator := ((hasFDerivAt_id w).const_smul (4 : Real)).add
    ((hNorm.sub_const (4 : Real)).smul_const v)
  have hDerivative := (hInverse.smul hNumerator).fderiv
  change fderiv Real (stereoInvFunAux v) w = _ at hDerivative
  have hApply := congrArg (fun derivative : E →L[Real] E => derivative u) hDerivative
  simpa [smul_smul, mul_assoc, add_comm, add_left_comm, add_assoc] using hApply

/-- On the pole's orthogonal complement the inverse stereographic chart is
conformal, with its actual Mathlib normalization. -/
theorem stereoInvFunAux_fderiv_inner
    (v w u z : E) (hv : ‖v‖ = 1)
    (hw : ⟪v, w⟫ = 0) (hu : ⟪v, u⟫ = 0) (hz : ⟪v, z⟫ = 0) :
    ⟪fderiv Real (stereoInvFunAux v) w u,
      fderiv Real (stereoInvFunAux v) w z⟫ =
      (4 / (‖w‖ ^ 2 + 4)) ^ 2 * ⟪u, z⟫ := by
  have hwv : ⟪w, v⟫ = 0 := by rwa [real_inner_comm]
  have huv : ⟪u, v⟫ = 0 := by rwa [real_inner_comm]
  simp only [stereoInvFunAux_fderiv_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial, hw, hz, hwv, huv,
    real_inner_self_eq_norm_sq, hv]
  rw [real_inner_comm u w]
  field_simp
  ring

/-- The derivative is tangent to the sphere, as required for the radial
cone Gram matrix to split into its spatial and radial blocks. -/
theorem stereoInvFunAux_inner_fderiv
    (v w u : E) (hv : ‖v‖ = 1)
    (hw : ⟪v, w⟫ = 0) (hu : ⟪v, u⟫ = 0) :
    ⟪stereoInvFunAux v w, fderiv Real (stereoInvFunAux v) w u⟫ = 0 := by
  have hwv : ⟪w, v⟫ = 0 := by rwa [real_inner_comm]
  simp only [stereoInvFunAux_fderiv_apply, stereoInvFunAux_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial, hw, hu, hwv, real_inner_self_eq_norm_sq, hv]
  field_simp
  ring

/-- Differential of the radial extension used in the exact-volume formula. -/
theorem stereoCone_fderiv_apply (v w u : E) (radius speed : Real) :
    fderiv Real (fun point : E × Real => point.2 • stereoInvFunAux v point.1)
        (w, radius) (u, speed) =
      radius • fderiv Real (stereoInvFunAux v) w u + speed • stereoInvFunAux v w := by
  have hChart := (contDiff_stereoInvFunAux (v := v) (m := 1)).differentiable
    (by simp)
  have hFst : HasFDerivAt (Prod.fst : E × Real → E)
      (ContinuousLinearMap.fst Real E Real) (w, radius) := hasFDerivAt_fst
  have hSnd : HasFDerivAt (Prod.snd : E × Real → Real)
      (ContinuousLinearMap.snd Real E Real) (w, radius) := hasFDerivAt_snd
  have hDerivative := (hSnd.smul
    ((hChart w).hasFDerivAt.comp (w, radius) hFst)).fderiv
  change fderiv Real (fun point : E × Real => point.2 • stereoInvFunAux v point.1)
    (w, radius) = _ at hDerivative
  have hApply := congrArg (fun derivative : (E × Real) →L[Real] E =>
    derivative (u, speed)) hDerivative
  simpa using hApply

/-- Exact block-diagonal cone Gram form: three conformal spatial directions
and a unit radial direction, with no mixed term. -/
theorem stereoCone_fderiv_inner
    (v w u z : E) (radius firstSpeed secondSpeed : Real) (hv : ‖v‖ = 1)
    (hw : ⟪v, w⟫ = 0) (hu : ⟪v, u⟫ = 0) (hz : ⟪v, z⟫ = 0) :
    ⟪fderiv Real (fun point : E × Real => point.2 • stereoInvFunAux v point.1)
        (w, radius) (u, firstSpeed),
      fderiv Real (fun point : E × Real => point.2 • stereoInvFunAux v point.1)
        (w, radius) (z, secondSpeed)⟫ =
      radius ^ 2 * (4 / (‖w‖ ^ 2 + 4)) ^ 2 * ⟪u, z⟫ +
        firstSpeed * secondSpeed := by
  have hOrth : w ∈ (Real ∙ v)ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    rwa [real_inner_comm]
  have hUnit : ‖stereoInvFunAux v w‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using stereoInvFunAux_mem hv hOrth
  have hLeft : ⟪fderiv Real (stereoInvFunAux v) w u, stereoInvFunAux v w⟫ = 0 := by
    rw [real_inner_comm]
    exact stereoInvFunAux_inner_fderiv v w u hv hw hu
  simp only [stereoCone_fderiv_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial,
    stereoInvFunAux_fderiv_inner v w u z hv hw hu hz,
    stereoInvFunAux_inner_fderiv v w z hv hw hz, hLeft,
    real_inner_self_eq_norm_sq, hUnit]
  ring

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

local instance : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩

private def stereographicOrthogonalEmbedding (pole : StandardSphere) :
    Space3 →ₗᵢ[Real] EuclideanR4 :=
  (Real ∙ (pole : EuclideanR4))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere pole)).repr.symm.toLinearIsometry

private theorem stereographicOrthogonalEmbedding_orthogonal
    (pole : StandardSphere) (coordinate : Space3) :
    ⟪(pole : EuclideanR4), stereographicOrthogonalEmbedding pole coordinate⟫ = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere pole)).repr.symm coordinate).property

/-- Concrete chart metric for the very inverse map used by Gate568. -/
theorem stereographicInverseVector_fderiv_inner
    (pole : StandardSphere) (coordinate first second : Space3) :
    ⟪fderiv Real (stereographicInverseVector pole) coordinate first,
      fderiv Real (stereographicInverseVector pole) coordinate second⟫ =
      (4 / (‖coordinate‖ ^ 2 + 4)) ^ 2 * ⟪first, second⟫ := by
  let embedding := stereographicOrthogonalEmbedding pole
  have hChart := (contDiff_stereoInvFunAux (v := (pole : EuclideanR4))
    (m := 1)).differentiable (by simp)
  have hDerivative := ((hChart (embedding coordinate)).hasFDerivAt.comp coordinate
    (embedding.toContinuousLinearMap.hasFDerivAt)).fderiv
  change fderiv Real (stereographicInverseVector pole) coordinate = _ at hDerivative
  rw [hDerivative]
  change ⟪fderiv Real (stereoInvFunAux (pole : EuclideanR4)) (embedding coordinate)
      (embedding first),
    fderiv Real (stereoInvFunAux (pole : EuclideanR4)) (embedding coordinate)
      (embedding second)⟫ = _
  rw [stereoInvFunAux_fderiv_inner _ _ _ _ (norm_eq_of_mem_sphere pole)
    (stereographicOrthogonalEmbedding_orthogonal pole coordinate)
    (stereographicOrthogonalEmbedding_orthogonal pole first)
    (stereographicOrthogonalEmbedding_orthogonal pole second)]
  rw [embedding.norm_map coordinate, embedding.inner_map_map first second]

/-- Spatial metric matrix pulled back by the concrete inverse chart. -/
def stereographicSpatialGram (pole : StandardSphere) (coordinate : Space3) :
    Matrix (Fin 3) (Fin 3) Real := fun first second =>
  ⟪fderiv Real (stereographicInverseVector pole) coordinate
      (EuclideanSpace.basisFun (Fin 3) Real first),
    fderiv Real (stereographicInverseVector pole) coordinate
      (EuclideanSpace.basisFun (Fin 3) Real second)⟫

theorem stereographicSpatialGram_eq_diagonal (pole : StandardSphere) (coordinate : Space3) :
    stereographicSpatialGram pole coordinate =
      Matrix.diagonal (fun _ : Fin 3 => (4 / (‖coordinate‖ ^ 2 + 4)) ^ 2) := by
  classical
  ext first second
  rw [stereographicSpatialGram, stereographicInverseVector_fderiv_inner]
  rw [EuclideanSpace.basisFun_inner]
  simp only [EuclideanSpace.basisFun_apply]
  by_cases h : first = second
  · subst second; simp
  · simp [h]

theorem stereographicSpatialGram_det (pole : StandardSphere) (coordinate : Space3) :
    (stereographicSpatialGram pole coordinate).det =
      (4 / (‖coordinate‖ ^ 2 + 4)) ^ 6 := by
  rw [stereographicSpatialGram_eq_diagonal, Matrix.det_diagonal]
  simp
  ring

/-- The positive metric volume density is explicitly evaluated. The remaining
measure bridge must identify the cone-integrated density of Gate568 with it. -/
theorem stereographicSpatialGram_volume (pole : StandardSphere) (coordinate : Space3) :
    Real.sqrt |(stereographicSpatialGram pole coordinate).det| =
      (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3 := by
  rw [stereographicSpatialGram_det, abs_of_nonneg (by positivity),
    show (4 / (‖coordinate‖ ^ 2 + 4)) ^ 6 =
      ((4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

theorem stereographic_inverse_differential_gate (pole : StandardSphere) (coordinate : Space3) :
    stereographicSpatialGram pole coordinate =
        Matrix.diagonal (fun _ : Fin 3 => (4 / (‖coordinate‖ ^ 2 + 4)) ^ 2) ∧
      Real.sqrt |(stereographicSpatialGram pole coordinate).det| =
        (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3 :=
  ⟨stereographicSpatialGram_eq_diagonal pole coordinate,
    stereographicSpatialGram_volume pole coordinate⟩

end
end P0EFTJanusStereographicInverseDifferential4D
end JanusFormal
