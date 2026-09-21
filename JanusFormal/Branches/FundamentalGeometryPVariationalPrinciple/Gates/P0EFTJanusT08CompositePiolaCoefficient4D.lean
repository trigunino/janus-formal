import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D

/-!
# T08: weighted Piola equations on regular auxiliary-coordinate patches

We reuse the actual T06 differential Piola identity on the three-dimensional
throat coordinate space. A locally invertible auxiliary map has divergence-
free cofactor vectors. Their weighted divergences vanish precisely when the
coefficient has zero derivative, hence is constant on connected open patches.
This is a local differential calculation, not a global realization theorem
or an assumed equivalence with stationarity of an integrated action.
-/
namespace JanusFormal
namespace P0EFTJanusT08CompositePiolaCoefficient4D
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

private abbrev E := ThroatCoverCoordinates

/-- Cofactor vector associated with a constant auxiliary-space direction.
The reverse map is required to have the inverse derivative locally. -/
def cofactorFlux (forward reverse : E → E) (vector : E) : E → E :=
  programPT06ThroatSignedVectorPullback forward reverse (fun _ => vector)

theorem cofactorFlux_divergence_zero {forward reverse : E → E} {point : E}
    (vector : E)
    (hInverse : ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ContDiffAt Real 2 forward point) :
    programPT06ThroatCoordinateDivergence (cofactorFlux forward reverse vector) point = 0 := by
  rw [cofactorFlux, programPT06ThroatSignedVectorPullback_divergence_eq_det_mul
    hInverse hFlux (differentiableAt_const vector) hForward]
  simp [programPT06ThroatCoordinateDivergence]

/-- Product rule for the existing coordinate divergence. -/
theorem divergence_smul {coefficient : E → Real} {field : E → E} {point : E}
    (hCoefficient : DifferentiableAt Real coefficient point)
    (hField : DifferentiableAt Real field point) :
    programPT06ThroatCoordinateDivergence (fun x => coefficient x • field x) point =
      fderiv Real coefficient point (field point) +
        coefficient point * programPT06ThroatCoordinateDivergence field point := by
  unfold programPT06ThroatCoordinateDivergence
  rw [(hCoefficient.hasFDerivAt.fun_smul hField.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [add_comm]
  congr 1
  calc
    _ = fderiv Real coefficient point
        (∑ i : Fin 3, programPT06ThroatSpatialBasis.equivFun (field point) i •
          programPT06ThroatSpatialBasis i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [programPT06ThroatSpatialBasis.sum_equivFun]

/-- Pointwise integration-by-parts identity for a test scalar. Integrating
this identity still requires a domain and a boundary/compact-support law. -/
theorem weighted_flux_product_identity
    {coefficient test : E → Real} {field : E → E} {point : E}
    (hCoefficient : DifferentiableAt Real coefficient point)
    (hTest : DifferentiableAt Real test point)
    (hField : DifferentiableAt Real field point) :
    coefficient point * fderiv Real test point (field point) =
      programPT06ThroatCoordinateDivergence
        (fun x => test x • (coefficient x • field x)) point -
      test point * programPT06ThroatCoordinateDivergence
        (fun x => coefficient x • field x) point := by
  rw [divergence_smul hTest (hCoefficient.fun_smul hField)]
  simp only [map_smul, smul_eq_mul]
  ring

/-- The Piola cancellation removes all second derivatives of the auxiliary
map from the weighted divergence. -/
theorem weighted_cofactor_divergence {forward reverse : E → E}
    {coefficient : E → Real} {point : E} (vector : E)
    (hInverse : ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ContDiffAt Real 2 forward point)
    (hCoefficient : DifferentiableAt Real coefficient point) :
    programPT06ThroatCoordinateDivergence
        (fun x => coefficient x • cofactorFlux forward reverse vector x) point =
      LinearMap.det (fderiv Real forward point).toLinearMap *
        fderiv Real coefficient point (fderiv Real reverse (forward point) vector) := by
  rw [divergence_smul hCoefficient hFlux,
    cofactorFlux_divergence_zero vector hInverse hFlux hForward, mul_zero, add_zero]
  simp only [cofactorFlux, programPT06ThroatSignedVectorPullback, map_smul, smul_eq_mul]

/-- On a regular patch the cofactor equations detect d(coefficient), not
coefficient itself. Directions range over the full auxiliary tangent space. -/
theorem weighted_equations_iff_derivative_zero {forward reverse : E → E}
    {coefficient : E → Real} {point : E}
    (hInverse : ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : ∀ vector : E, DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ContDiffAt Real 2 forward point)
    (hCoefficient : DifferentiableAt Real coefficient point)
    (hDet : LinearMap.det (fderiv Real forward point).toLinearMap ≠ 0) :
    (∀ vector : E, programPT06ThroatCoordinateDivergence
      (fun x => coefficient x • cofactorFlux forward reverse vector x) point = 0) ↔
      fderiv Real coefficient point = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro vector
    have hTest := h (fderiv Real forward point vector)
    rw [weighted_cofactor_divergence _ hInverse (hFlux _) hForward hCoefficient] at hTest
    have hAt := Filter.Eventually.self_of_nhds hInverse
    have hCancel := congrArg (fun map : E →L[Real] E => map vector) hAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hCancel
    rw [hCancel] at hTest
    exact (mul_eq_zero.mp hTest).resolve_left hDet
  · intro h vector
    rw [weighted_cofactor_divergence vector hInverse (hFlux vector) hForward hCoefficient, h]
    simp

/-- Testing the three auxiliary basis directions suffices. -/
theorem three_weighted_equations_iff_derivative_zero {forward reverse : E → E}
    {coefficient : E → Real} {point : E}
    (hInverse : ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : ∀ vector : E, DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ContDiffAt Real 2 forward point)
    (hCoefficient : DifferentiableAt Real coefficient point)
    (hDet : LinearMap.det (fderiv Real forward point).toLinearMap ≠ 0) :
    (∀ i : Fin 3, programPT06ThroatCoordinateDivergence
      (fun x => coefficient x • cofactorFlux forward reverse
        (programPT06ThroatSpatialBasis i) x) point = 0) ↔
      fderiv Real coefficient point = 0 := by
  constructor
  · intro h
    apply (weighted_equations_iff_derivative_zero hInverse hFlux hForward hCoefficient hDet).mp
    have hMap : (fderiv Real coefficient point).toLinearMap.comp
        (fderiv Real reverse (forward point)).toLinearMap = 0 := by
      apply programPT06ThroatSpatialBasis.ext
      intro i
      have hTest := h i
      rw [weighted_cofactor_divergence _ hInverse (hFlux _) hForward hCoefficient] at hTest
      exact (mul_eq_zero.mp hTest).resolve_left hDet
    intro vector
    rw [weighted_cofactor_divergence vector hInverse (hFlux vector) hForward hCoefficient]
    have hAt := congrArg (fun map : E →ₗ[Real] Real => map vector) hMap
    change fderiv Real coefficient point (fderiv Real reverse (forward point) vector) = 0 at hAt
    rw [hAt, mul_zero]
  · intro h i
    exact (weighted_equations_iff_derivative_zero hInverse hFlux hForward hCoefficient hDet).mpr h
      (programPT06ThroatSpatialBasis i)

/-- A connected regular patch has one integration constant. Its value is
not selected by the cofactor equations. -/
theorem coefficient_constant_on_connected_patch
    {forward reverse : E → E} {coefficient : E → Real} {patch : Set E}
    (hOpen : IsOpen patch) (hConnected : IsPreconnected patch)
    (hCoefficient : DifferentiableOn Real coefficient patch)
    (hInverse : ∀ point ∈ patch, ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : ∀ point ∈ patch, ∀ vector : E,
      DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ∀ point ∈ patch, ContDiffAt Real 2 forward point)
    (hDet : ∀ point ∈ patch, LinearMap.det (fderiv Real forward point).toLinearMap ≠ 0)
    (hEquations : ∀ point ∈ patch, ∀ vector : E,
      programPT06ThroatCoordinateDivergence
        (fun x => coefficient x • cofactorFlux forward reverse vector x) point = 0)
    {base : E} (hBase : base ∈ patch) :
    ∀ point ∈ patch, coefficient point = coefficient base := by
  apply hOpen.eqOn_of_fderiv_eq hConnected hCoefficient
    (differentiableOn_const (coefficient base)) _ hBase rfl
  intro point hPoint
  rw [fderiv_const_apply]
  exact (weighted_equations_iff_derivative_zero (hInverse point hPoint)
    (hFlux point hPoint) (hForward point hPoint)
    ((hCoefficient point hPoint).differentiableAt (hOpen.mem_nhds hPoint))
    (hDet point hPoint)).mp (hEquations point hPoint)

/-- Every constant, including a nonzero one, solves the weighted equations. -/
theorem constant_coefficient_solves (value : Real) {forward reverse : E → E} {point : E}
    (hInverse : ∀ᶠ nearby in nhds point,
      (fderiv Real reverse (forward nearby)).comp (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real E)
    (hFlux : ∀ vector : E, DifferentiableAt Real (cofactorFlux forward reverse vector) point)
    (hForward : ContDiffAt Real 2 forward point) :
    ∀ vector : E, programPT06ThroatCoordinateDivergence
      (fun x => value • cofactorFlux forward reverse vector x) point = 0 := by
  intro vector
  rw [weighted_cofactor_divergence vector hInverse (hFlux vector) hForward
    (differentiableAt_const value)]
  simp

/-! A populated regular local example: no inverse or regularity hypothesis
is left to supply for the identity auxiliary map. -/
theorem identity_patch_constant_solves (value : Real) (point vector : E) :
    programPT06ThroatCoordinateDivergence
      (fun x => value • cofactorFlux id id vector x) point = 0 := by
  simp [cofactorFlux, programPT06ThroatSignedVectorPullback,
    programPT06ThroatCoordinateDivergence]

theorem nonzero_coefficient_local_solution (point : E) :
    (1 : Real) ≠ 0 ∧ ∀ vector : E,
      programPT06ThroatCoordinateDivergence
        (fun x => (1 : Real) • cofactorFlux id id vector x) point = 0 :=
  ⟨one_ne_zero, identity_patch_constant_solves 1 point⟩

end
end P0EFTJanusT08CompositePiolaCoefficient4D
end JanusFormal
