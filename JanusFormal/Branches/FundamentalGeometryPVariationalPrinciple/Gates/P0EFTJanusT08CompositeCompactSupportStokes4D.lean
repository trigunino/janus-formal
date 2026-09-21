import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08CompositeDeterminantPiolaBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# T08: compact-support Stokes and test separation in throat coordinates

The integration measure is actual additive Haar measure on the T06 throat
coordinate space. Compact support of the test removes the boundary term;
no decay is required of the smooth coefficient field. This is a Euclidean
coordinate statement, not a global Stokes theorem on the compact throat.
-/
namespace JanusFormal
namespace P0EFTJanusT08CompositeCompactSupportStokes4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D
open P0EFTJanusLLBraneCompositeMeasureVariation
open P0EFTJanusT08CompositePiolaCoefficient4D
open P0EFTJanusT08CompositeDeterminantPiolaBridge4D
open P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D
attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
private abbrev E := ThroatCoverCoordinates

/-- A component in the actual T06 basis preserves smoothness. -/
theorem auxiliaryComponent_contDiff {field : E → E}
    (hField : ContDiff Real ∞ field) (i : Fin 3) :
    ContDiff Real ∞ (auxiliaryComponent field i) :=
  (programPT06ThroatSpatialBasis.coord i).toContinuousLinearMap.contDiff.comp hField

theorem coordinate_divergence_eq_components {field : E → E} {point : E}
    (hField : DifferentiableAt Real field point) :
    programPT06ThroatCoordinateDivergence field point =
      ∑ i : Fin 3, fderiv Real (auxiliaryComponent field i) point (programPT06ThroatSpatialBasis i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [(component_hasFDerivAt hField i).fderiv]
  rfl

theorem coordinate_divergence_continuous {field : E → E}
    (hField : ContDiff Real ∞ field) :
    Continuous (programPT06ThroatCoordinateDivergence field) := by
  have hPoint : programPT06ThroatCoordinateDivergence field =
      fun point => ∑ i : Fin 3,
        fderiv Real (auxiliaryComponent field i) point (programPT06ThroatSpatialBasis i) := by
    funext point
    exact coordinate_divergence_eq_components (hField.differentiable (by simp) point)
  rw [hPoint]
  apply continuous_finsetSum
  intro i _
  exact ((auxiliaryComponent_contDiff hField i).continuous_fderiv (by simp)).clm_apply continuous_const

theorem scalar_derivative_basis_expansion (test : E → Real) (field : E → E) (point : E) :
    fderiv Real test point (field point) = ∑ i : Fin 3,
      fderiv Real test point (programPT06ThroatSpatialBasis i) * auxiliaryComponent field i point := by
  conv_lhs => rw [← programPT06ThroatSpatialBasis.sum_equivFun (field point)]
  simp only [map_sum, map_smul, smul_eq_mul, auxiliaryComponent]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact integration by parts with a compactly supported smooth scalar
variation. The boundary cancellation is proved from analytic hypotheses. -/
theorem integral_test_divergence_eq_neg_derivative
    {field : E → E} {test : E → Real}
    (hField : ContDiff Real ∞ field) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test) :
    (∫ x, test x * programPT06ThroatCoordinateDivergence field x ∂Measure.addHaar) =
      -∫ x, fderiv Real test x (field x) ∂Measure.addHaar := by
  have hComp (i : Fin 3) := auxiliaryComponent_contDiff hField i
  have hDComp (i : Fin 3) : Continuous (fun x =>
      fderiv Real (auxiliaryComponent field i) x (programPT06ThroatSpatialBasis i)) :=
    ((hComp i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDTest (i : Fin 3) : Continuous (fun x =>
      fderiv Real test x (programPT06ThroatSpatialBasis i)) :=
    (hTest.continuous_fderiv (by simp)).clm_apply continuous_const
  have hLeft (i : Fin 3) : Integrable (fun x => test x *
      fderiv Real (auxiliaryComponent field i) x (programPT06ThroatSpatialBasis i)) Measure.addHaar :=
    (hTest.continuous.mul (hDComp i)).integrable_of_hasCompactSupport hCompact.mul_right
  have hRight (i : Fin 3) : Integrable (fun x =>
      fderiv Real test x (programPT06ThroatSpatialBasis i) * auxiliaryComponent field i x) Measure.addHaar :=
    ((hDTest i).mul (hComp i).continuous).integrable_of_hasCompactSupport
      (hCompact.fderiv_apply Real (programPT06ThroatSpatialBasis i)).mul_right
  have hParts (i : Fin 3) :
      (∫ x, test x * fderiv Real (auxiliaryComponent field i) x
        (programPT06ThroatSpatialBasis i) ∂Measure.addHaar) =
      -∫ x, fderiv Real test x (programPT06ThroatSpatialBasis i) *
        auxiliaryComponent field i x ∂Measure.addHaar := by
    simpa only [one_mul] using integral_weighted_fderiv_eq_formalAdjoint
      (programPT06ThroatSpatialBasis i) (auxiliaryComponent field i) test (fun _ => 1) (fun _ => 1)
      (hComp i) hTest contDiff_const contDiff_const hCompact
  calc
    _ = ∫ x, ∑ i : Fin 3, test x * fderiv Real (auxiliaryComponent field i) x
          (programPT06ThroatSpatialBasis i) ∂Measure.addHaar := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinate_divergence_eq_components (hField.differentiable (by simp) x), Finset.mul_sum]
    _ = ∑ i : Fin 3, ∫ x, test x * fderiv Real (auxiliaryComponent field i) x
          (programPT06ThroatSpatialBasis i) ∂Measure.addHaar :=
      integral_finsetSum _ (fun i _ => hLeft i)
    _ = ∑ i : Fin 3, -(∫ x, fderiv Real test x (programPT06ThroatSpatialBasis i) *
          auxiliaryComponent field i x ∂Measure.addHaar) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hParts i
    _ = -∫ x, ∑ i : Fin 3, fderiv Real test x (programPT06ThroatSpatialBasis i) *
          auxiliaryComponent field i x ∂Measure.addHaar := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hRight i)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      exact (scalar_derivative_basis_expansion test field x).symm

/-- Fundamental lemma with actual Haar measure and all smooth compact tests. -/
theorem divergence_zero_of_test_pairing {field : E → E}
    (hField : ContDiff Real ∞ field)
    (hWeak : ∀ test : E → Real, ContDiff Real ∞ test → HasCompactSupport test →
      (∫ x, test x * programPT06ThroatCoordinateDivergence field x ∂Measure.addHaar) = 0) :
    ∀ point, programPT06ThroatCoordinateDivergence field point = 0 := by
  have hContinuous := coordinate_divergence_continuous hField
  have hAE : ∀ᵐ x ∂Measure.addHaar, programPT06ThroatCoordinateDivergence field x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hContinuous.locallyIntegrable
    intro test hTest hCompact
    simpa only [smul_eq_mul] using hWeak test hTest hCompact
  have hEverywhere : programPT06ThroatCoordinateDivergence field = 0 :=
    (Continuous.ae_eq_iff_eq Measure.addHaar hContinuous continuous_const).mp hAE
  exact fun point => congrFun hEverywhere point

/-- Vanishing of the derivative pairing is equivalent to the pointwise
weak-Euler residual, not merely to an almost-everywhere statement. -/
theorem derivative_pairing_zero_iff_divergence_zero {field : E → E}
    (hField : ContDiff Real ∞ field) :
    (∀ test : E → Real, ContDiff Real ∞ test → HasCompactSupport test →
      (∫ x, fderiv Real test x (field x) ∂Measure.addHaar) = 0) ↔
      ∀ point, programPT06ThroatCoordinateDivergence field point = 0 := by
  constructor
  · intro h
    apply divergence_zero_of_test_pairing hField
    intro test hTest hCompact
    rw [integral_test_divergence_eq_neg_derivative hField hTest hCompact, h test hTest hCompact, neg_zero]
  · intro h test hTest hCompact
    have hParts := integral_test_divergence_eq_neg_derivative hField hTest hCompact
    simp only [h, mul_zero, integral_zero] at hParts
    exact neg_eq_zero.mp hParts.symm

theorem derivative_pairing_integrable {field : E → E} {test : E → Real}
    (hField : Continuous field) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test) :
    Integrable (fun x => fderiv Real test x (field x)) Measure.addHaar := by
  apply ((hTest.continuous_fderiv (by simp)).clm_apply hField).integrable_of_hasCompactSupport
  apply (hCompact.fderiv Real).mono
  intro x hx
  change fderiv Real test x ≠ 0
  intro hZero
  apply hx
  simp [hZero]

/-- Exact integral identity for the existing determinant first variation.
Only the compactly supported auxiliary variation is required to decay. -/
theorem integral_composite_variation_eq_euler_pairing
    {forward reverse variation : E → E} {coefficient : E → Real}
    (hInverse : ∀ x, (fderiv Real reverse (forward x)).comp (fderiv Real forward x) =
      ContinuousLinearMap.id Real E)
    (hVariation : ContDiff Real ∞ variation) (hCompact : HasCompactSupport variation)
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hFlux : ∀ i : Fin 3, ContDiff Real ∞
      (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i))) :
    (∫ x, coefficient x * P0EFTJanusLLBraneCompositeMeasureVariation.compositeMeasureVariation
      (derivativeJet (fderiv Real forward x)) (derivativeJet (fderiv Real variation x))
      ∂Measure.addHaar) =
      -∑ i : Fin 3, ∫ x, auxiliaryComponent variation i x *
        programPT06ThroatCoordinateDivergence
          (fun y => coefficient y • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) y) x
        ∂Measure.addHaar := by
  let field (i : Fin 3) : E → E := fun x =>
    coefficient x • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) x
  have hField (i : Fin 3) : ContDiff Real ∞ (field i) := hCoefficient.fun_smul (hFlux i)
  have hTest (i : Fin 3) := auxiliaryComponent_contDiff hVariation i
  have hTestCompact (i : Fin 3) : HasCompactSupport (auxiliaryComponent variation i) :=
    hCompact.comp_left (g := fun v : E => programPT06ThroatSpatialBasis.equivFun v i) (by simp)
  have hInt (i : Fin 3) := derivative_pairing_integrable (hField i).continuous (hTest i) (hTestCompact i)
  calc
    _ = ∫ x, ∑ i : Fin 3, fderiv Real (auxiliaryComponent variation i) x (field i x)
        ∂Measure.addHaar := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [determinant_variation_eq_cofactor_pairing (hInverse x)
        (hVariation.differentiable (by simp) x), Finset.mul_sum]
      simp only [field, map_smul, smul_eq_mul]
    _ = ∑ i : Fin 3, ∫ x, fderiv Real (auxiliaryComponent variation i) x (field i x)
        ∂Measure.addHaar := integral_finsetSum _ (fun i _ => hInt i)
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hParts := integral_test_divergence_eq_neg_derivative (hField i) (hTest i) (hTestCompact i)
      exact neg_eq_iff_eq_neg.mp hParts.symm

/-- Independent compact scalar tests in the three auxiliary directions
detect exactly the three weighted Piola residuals. -/
theorem compact_cofactor_tests_iff_euler_zero
    {forward reverse : E → E} {coefficient : E → Real}
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hFlux : ∀ i : Fin 3, ContDiff Real ∞
      (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i))) :
    (∀ i : Fin 3, ∀ test : E → Real, ContDiff Real ∞ test → HasCompactSupport test →
      (∫ x, coefficient x * fderiv Real test x
        (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) x) ∂Measure.addHaar) = 0) ↔
    ∀ i : Fin 3, ∀ x, programPT06ThroatCoordinateDivergence
      (fun y => coefficient y • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) y) x = 0 := by
  have hEach (i : Fin 3) := derivative_pairing_zero_iff_divergence_zero
    (hCoefficient.fun_smul (hFlux i))
  simp only [map_smul, smul_eq_mul] at hEach
  exact forall_congr' hEach

/-- A scalar test in one auxiliary direction is a genuine vector variation. -/
theorem determinant_single_auxiliary_test
    {forward reverse : E → E} {test : E → Real} {point : E}
    (hInverse : (fderiv Real reverse (forward point)).comp (fderiv Real forward point) =
      ContinuousLinearMap.id Real E)
    (hTest : DifferentiableAt Real test point) (i : Fin 3) :
    compositeMeasureVariation (derivativeJet (fderiv Real forward point))
      (derivativeJet (fderiv Real (fun x => test x • programPT06ThroatSpatialBasis i) point)) =
      fderiv Real test point (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) point) := by
  rw [(hTest.hasFDerivAt.smul_const (programPT06ThroatSpatialBasis i)).fderiv,
    determinant_variation_inverse_pairing _ _ _ hInverse]
  simp [ContinuousLinearMap.smulRight_apply, map_smul, Module.Basis.equivFun_apply,
    cofactorFlux, programPT06ThroatSignedVectorPullback, Finsupp.single_apply]

/-- Vanishing of the integrated determinant first variation for all genuine
compact auxiliary variations is equivalent to the three pointwise residuals.
This is not yet a differentiation-under-the-action-integral theorem. -/
theorem integrated_determinant_variation_zero_iff_euler_zero
    {forward reverse : E → E} {coefficient : E → Real}
    (hInverse : ∀ x, (fderiv Real reverse (forward x)).comp (fderiv Real forward x) =
      ContinuousLinearMap.id Real E)
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hFlux : ∀ i : Fin 3, ContDiff Real ∞
      (cofactorFlux forward reverse (programPT06ThroatSpatialBasis i))) :
    (∀ variation : E → E, ContDiff Real ∞ variation → HasCompactSupport variation →
      (∫ x, coefficient x * compositeMeasureVariation
        (derivativeJet (fderiv Real forward x)) (derivativeJet (fderiv Real variation x))
        ∂Measure.addHaar) = 0) ↔
    ∀ i : Fin 3, ∀ x, programPT06ThroatCoordinateDivergence
      (fun y => coefficient y • cofactorFlux forward reverse (programPT06ThroatSpatialBasis i) y) x = 0 := by
  constructor
  · intro hWeak
    apply (compact_cofactor_tests_iff_euler_zero hCoefficient hFlux).mp
    intro i test hTest hCompact
    have hVectorCompact : HasCompactSupport (fun x => test x • programPT06ThroatSpatialBasis i) :=
      hCompact.comp_left (g := fun t : Real => t • programPT06ThroatSpatialBasis i) (by simp)
    have h := hWeak (fun x => test x • programPT06ThroatSpatialBasis i)
      (hTest.smul_const _) hVectorCompact
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [determinant_single_auxiliary_test (hInverse x) (hTest.differentiable (by simp) x)]
  · intro hEuler variation hVariation hCompact
    rw [integral_composite_variation_eq_euler_pairing hInverse hVariation hCompact hCoefficient hFlux]
    simp only [hEuler, mul_zero, integral_zero, Finset.sum_const_zero, neg_zero]

/-- Under regularity, the integrated first-variation equation fixes only the
derivative of the coefficient. Its constant value remains a separate datum. -/
theorem integrated_variation_zero_iff_coefficient_derivative_zero
    {forward reverse : E → E} {coefficient : E → Real}
    (hInverse : ∀ x, (fderiv Real reverse (forward x)).comp (fderiv Real forward x) =
      ContinuousLinearMap.id Real E)
    (hForward : ContDiff Real 2 forward)
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hFlux : ∀ vector : E, ContDiff Real ∞ (cofactorFlux forward reverse vector))
    (hDet : ∀ x, LinearMap.det (fderiv Real forward x).toLinearMap ≠ 0) :
    (∀ variation : E → E, ContDiff Real ∞ variation → HasCompactSupport variation →
      (∫ x, coefficient x * compositeMeasureVariation
        (derivativeJet (fderiv Real forward x)) (derivativeJet (fderiv Real variation x))
        ∂Measure.addHaar) = 0) ↔
    ∀ x, fderiv Real coefficient x = 0 := by
  rw [integrated_determinant_variation_zero_iff_euler_zero hInverse hCoefficient
    (fun i => hFlux (programPT06ThroatSpatialBasis i))]
  have hAt (x : E) := three_weighted_equations_iff_derivative_zero
    (point := x) (Filter.Eventually.of_forall hInverse)
    (fun vector => (hFlux vector).differentiable (by simp) x)
    hForward.contDiffAt (hCoefficient.differentiable (by simp) x) (hDet x)
  constructor
  · intro h x
    exact (hAt x).mp (fun i => h i x)
  · intro h i x
    exact (hAt x).mpr (h x) i

end
end P0EFTJanusT08CompositeCompactSupportStokes4D
end JanusFormal
