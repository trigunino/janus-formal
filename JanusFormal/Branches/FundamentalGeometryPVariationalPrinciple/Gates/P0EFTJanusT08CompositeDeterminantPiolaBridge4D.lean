import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08CompositePiolaCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08CompositeMeasureScalarBridge

/-!
# T08: determinant variation and the actual local Piola pairing

The coordinate index of the existing composite jet is the first index,
so its matrix is the transpose of the derivative matrix. We identify its
previously proved determinant variation with the actual cofactor-vector
pairing of T06, and derive the local divergence/Euler split. Integration
and the global variational fundamental lemma are separate remaining steps.
-/
namespace JanusFormal
namespace P0EFTJanusT08CompositeDeterminantPiolaBridge4D
set_option autoImplicit false
noncomputable section
open scoped Topology
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D
open P0EFTJanusT08CompositePiolaCoefficient4D
open P0EFTJanusLLBraneCompositeMeasureVariation
open P0EFTJanusT08CompositeMeasureScalarBridge
attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
private abbrev E := ThroatCoverCoordinates
private abbrev Mat := P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3

/-- Polynomial determinant differential in a right-multiplicative direction;
valid even at singular matrices. -/
theorem determinant_variation_mul (jet direction : Mat) :
    compositeMeasureVariation jet (jet * direction) =
      compositeMeasure jet * Matrix.trace direction := by
  simp only [compositeMeasureVariation, compositeMeasure, Matrix.det_fin_three,
    Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  ring

/-- Actual derivative in the coordinate-first convention of the LL jet. -/
def derivativeJet (linear : E →L[Real] E) : Mat :=
  (LinearMap.toMatrix programPT06ThroatSpatialBasis programPT06ThroatSpatialBasis
    linear.toLinearMap).transpose

theorem derivativeJet_apply (linear : E →L[Real] E) (row column : Fin 3) :
    derivativeJet linear row column =
      programPT06ThroatSpatialBasis.equivFun (linear (programPT06ThroatSpatialBasis row)) column := by
  simp [derivativeJet, LinearMap.toMatrix_apply]

theorem derivativeJet_comp (first second : E →L[Real] E) :
    derivativeJet (first.comp second) = derivativeJet second * derivativeJet first := by
  unfold derivativeJet
  change (LinearMap.toMatrix programPT06ThroatSpatialBasis programPT06ThroatSpatialBasis
    (first.toLinearMap.comp second.toLinearMap)).transpose = _
  rw [LinearMap.toMatrix_comp programPT06ThroatSpatialBasis programPT06ThroatSpatialBasis
    programPT06ThroatSpatialBasis, Matrix.transpose_mul]

theorem derivativeJet_id : derivativeJet (ContinuousLinearMap.id Real E) = 1 := by
  simp [derivativeJet]

theorem derivativeJet_det (linear : E →L[Real] E) :
    compositeMeasure (derivativeJet linear) = LinearMap.det linear.toLinearMap := by
  simp [compositeMeasure, derivativeJet, LinearMap.det_toMatrix]

/-- The left-inverse derivative law suffices; no inverse is selected by the
potential or by the equations of the candidate action. -/
theorem determinant_variation_inverse_pairing (forward reverse variation : E →L[Real] E)
    (hInverse : reverse.comp forward = ContinuousLinearMap.id Real E) :
    compositeMeasureVariation (derivativeJet forward) (derivativeJet variation) =
      ∑ i : Fin 3, programPT06ThroatSpatialBasis.equivFun
        (variation (LinearMap.det forward.toLinearMap • reverse (programPT06ThroatSpatialBasis i))) i := by
  have hMatrices : derivativeJet forward * derivativeJet reverse = 1 := by
    rw [← derivativeJet_comp, hInverse, derivativeJet_id]
  have hFactor : derivativeJet variation = derivativeJet forward *
      (derivativeJet reverse * derivativeJet variation) := by
    rw [← Matrix.mul_assoc, hMatrices, Matrix.one_mul]
  calc
    _ = compositeMeasureVariation (derivativeJet forward)
        (derivativeJet forward * (derivativeJet reverse * derivativeJet variation)) := by
      rw [← hFactor]
    _ = compositeMeasure (derivativeJet forward) *
        Matrix.trace (derivativeJet reverse * derivativeJet variation) := determinant_variation_mul _ _
    _ = _ := by
      rw [← derivativeJet_comp, derivativeJet_det]
      simp only [Matrix.trace, Matrix.diag, derivativeJet_apply, ContinuousLinearMap.comp_apply,
        map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Genuine component of an auxiliary variation in the fixed throat basis. -/
def auxiliaryComponent (variation : E → E) (index : Fin 3) : E → Real :=
  fun x => programPT06ThroatSpatialBasis.equivFun (variation x) index

theorem component_hasFDerivAt {variation : E → E} {point : E}
    (hVariation : DifferentiableAt Real variation point) (index : Fin 3) :
    HasFDerivAt (auxiliaryComponent variation index)
      (((programPT06ThroatSpatialBasis.coord index).toContinuousLinearMap).comp
        (fderiv Real variation point)) point := by
  exact (programPT06ThroatSpatialBasis.coord index).toContinuousLinearMap.hasFDerivAt.comp point
    hVariation.hasFDerivAt

/-- This equality joins the actual determinant differential to the vector
fields used by the weighted Piola equations. -/
theorem determinant_variation_eq_cofactor_pairing
    {forward reverse variation : E → E} {point : E}
    (hInverse : (fderiv Real reverse (forward point)).comp (fderiv Real forward point) =
      ContinuousLinearMap.id Real E)
    (hVariation : DifferentiableAt Real variation point) :
    compositeMeasureVariation (derivativeJet (fderiv Real forward point))
        (derivativeJet (fderiv Real variation point)) =
      ∑ i : Fin 3, fderiv Real (auxiliaryComponent variation i) point
        (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) point) := by
  rw [determinant_variation_inverse_pairing _ _ _ hInverse]
  apply Finset.sum_congr rfl
  intro i _
  rw [(component_hasFDerivAt hVariation i).fderiv]
  rfl

/-- The actual local auxiliary curve induces the affine first-jet curve. -/
theorem derivativeJet_auxiliary_curve {forward variation : E → E} {point : E}
    (hForward : DifferentiableAt Real forward point)
    (hVariation : DifferentiableAt Real variation point) (t : Real) :
    derivativeJet (fderiv Real (fun x => forward x + t • variation x) point) =
      auxiliaryJetCurve (derivativeJet (fderiv Real forward point))
        (derivativeJet (fderiv Real variation point)) t := by
  rw [(hForward.hasFDerivAt.fun_add (hVariation.hasFDerivAt.fun_const_smul t)).fderiv]
  funext row column
  simp [auxiliaryJetCurve, derivativeJet,
    LinearMap.toMatrix_apply, map_add, map_smul]

/-- Actual derivative of the composite density along auxiliary fields, with
the energy and reference volume fixed. -/
theorem composite_density_auxiliary_hasDerivAt
    {forward reverse variation : E → E} {point : E}
    (hForward : DifferentiableAt Real forward point)
    (hVariation : DifferentiableAt Real variation point)
    (hInverse : (fderiv Real reverse (forward point)).comp (fderiv Real forward point) =
      ContinuousLinearMap.id Real E)
    (rho fluxEnergy : Real) (hRho : rho ≠ 0) (potential : Real → Real) (slope : Real)
    (hPotential : HasDerivAt potential slope
      (scalarCoefficient (derivativeJet (fderiv Real forward point)) rho)) :
    HasDerivAt (fun t : Real => chartDensity
      (derivativeJet (fderiv Real (fun x => forward x + t • variation x) point))
      rho fluxEnergy potential)
      ((fluxEnergy + slope) * ∑ i : Fin 3,
        fderiv Real (auxiliaryComponent variation i) point
          (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) point)) 0 := by
  have h := chartDensity_curve_hasDerivAt
    (derivativeJet (fderiv Real forward point)) (derivativeJet (fderiv Real variation point))
    rho 0 fluxEnergy hRho potential slope hPotential
  simpa only [derivativeJet_auxiliary_curve hForward hVariation,
    determinant_variation_eq_cofactor_pairing hInverse hVariation, mul_zero, add_zero] using h

/-- Exact pointwise divergence/Euler split of the determinant variation.
No boundary term is discarded. -/
theorem determinant_variation_divergence_split
    {forward reverse variation : E → E} {coefficient : E → Real} {point : E}
    (hInverse : (fderiv Real reverse (forward point)).comp (fderiv Real forward point) =
      ContinuousLinearMap.id Real E)
    (hVariation : DifferentiableAt Real variation point)
    (hCoefficient : DifferentiableAt Real coefficient point)
    (hFlux : ∀ i : Fin 3, DifferentiableAt Real
      (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i)) point) :
    coefficient point * compositeMeasureVariation (derivativeJet (fderiv Real forward point))
        (derivativeJet (fderiv Real variation point)) =
      (∑ i : Fin 3, programPT06ThroatCoordinateDivergence
        (fun x => auxiliaryComponent variation i x •
          (coefficient x • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) x)) point) -
      ∑ i : Fin 3, auxiliaryComponent variation i point *
        programPT06ThroatCoordinateDivergence
          (fun x => coefficient x • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) x) point := by
  rw [determinant_variation_eq_cofactor_pairing hInverse hVariation,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact weighted_flux_product_identity hCoefficient
    (component_hasFDerivAt hVariation i).differentiableAt (hFlux i)

end
end P0EFTJanusT08CompositeDeterminantPiolaBridge4D
end JanusFormal
