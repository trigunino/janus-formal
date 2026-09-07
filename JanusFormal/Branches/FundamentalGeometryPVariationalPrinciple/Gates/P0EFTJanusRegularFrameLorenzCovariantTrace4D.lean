import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D

/-!
# Lorenz covariant trace in an independent fixed regular frame

The supplied Lorentz metric and the reference frame are independent. Metric
compatibility converts the actual divergence of the raised potential into
the inverse-Gram contraction of the covariant derivative of its coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameLorenzCovariantTrace4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The supplied metric's Gram matrix in the independent reference frame. -/
def regularFrameLorenzMetricMatrix
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix (Fin 4) (Fin 4) Real :=
  fun first second => metric.tensor.tensor point
    (reference.frame first point) (reference.frame second point)

private theorem trace_eq_inverse_gram_contraction
    (basis : Module.Basis (Fin 4) Real Vector4)
    (form : LinearMap.BilinForm Real Vector4)
    (hNondegenerate : form.Nondegenerate)
    (hSymmetric : ∀ first second, form first second = form second first)
    (operator : Vector4 →ₗ[Real] Vector4) :
    LinearMap.trace Real Vector4 operator =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (LinearMap.BilinForm.toMatrix basis form)⁻¹ first second *
          form (operator (basis first)) (basis second) := by
  let gram := LinearMap.BilinForm.toMatrix basis form
  have hInverse : gram⁻¹ * gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero basis).mp hNondegenerate))
  have hPairing (vector : Vector4) :
      (fun index => form vector (basis index)) =
        gram *ᵥ (fun index => basis.repr vector index) := by
    funext index
    rw [hSymmetric vector (basis index)]
    simp only [Matrix.mulVec, dotProduct, gram, LinearMap.BilinForm.toMatrix_apply]
    calc
      _ = form (basis index)
          (∑ other : Fin 4, basis.repr vector other • basis other) :=
        congrArg (form (basis index)) (basis.sum_repr vector).symm
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro other _
        exact mul_comm _ _
  have hCoordinates (vector : Vector4) :
      (fun index => basis.repr vector index) =
        gram⁻¹ *ᵥ (fun index => form vector (basis index)) := by
    rw [hPairing, Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro first _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact congrFun (hCoordinates (operator (basis first))) first

private theorem localMetricCoordinateForm_raised
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate) vector =
      potential.toFun component (patch.coordinateMap coordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate vector) := by
  rw [localMetricCoordinateForm_apply,
    coordinateMap_mfderiv_localRaisedAbelianGaugePotential]
  rw [← metric.musical_eq_tensor]
  exact congrArg
    (fun covector : TangentSpace coverModelWithCorners
        (patch.coordinateMap coordinate) →L[Real] Real =>
      covector (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate vector))
    (metric_flat_inverseMetricSharp period hPeriod metric
      (patch.coordinateMap coordinate)
      (potential.toFun component (patch.coordinateMap coordinate)))

private theorem localMetricCoordinateForm_raised_frame
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin 4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate)
        (pulledRegularFrameVector period hPeriod reference patch index coordinate) =
      regularFramePotentialCoefficient period hPeriod reference potential
        component index (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_raised, coordinateMap_mfderiv_pulledRegularFrameVector]
  rfl

private theorem covariant_pairing_eq_coefficient_derivative
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin 4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component patch coordinate
          (pulledRegularFrameVector period hPeriod reference patch first coordinate))
        (pulledRegularFrameVector period hPeriod reference patch second coordinate) =
      frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          (regularFramePotentialCoefficient period hPeriod reference potential component second)
          (patch.coordinateMap coordinate) first -
        ∑ index : Fin 4,
          (pulledRegularFrameBasis period hPeriod reference patch coordinate).repr
              (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
                period hPeriod reference metric patch first second coordinate) index *
            regularFramePotentialCoefficient period hPeriod reference potential
              component index (patch.coordinateMap coordinate) := by
  let raised := localRaisedAbelianGaugePotential period hPeriod metric potential component patch
  let vector := pulledRegularFrameVector period hPeriod reference patch second
  let direction := pulledRegularFrameVector period hPeriod reference patch first coordinate
  let form := localMetricCoordinateForm period hPeriod metric patch coordinate
  let connection := candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
    period hPeriod reference metric patch first second coordinate
  have hProduct :
      fderiv Real (fun current =>
        localMetricCoordinateForm period hPeriod metric patch current
          (raised current) (vector current)) coordinate direction =
        form (fderiv Real raised coordinate direction) (vector coordinate) +
          localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate
            direction (raised coordinate) (vector coordinate) +
          form (raised coordinate) (fderiv Real vector coordinate direction) := by
    simpa only [form, localMetricCoordinateForm, localMetricDerivativeTrilinearForm_apply]
      using fderiv_matrix_toBilin_dynamic_apply
        (localMetricMatrix period hPeriod metric patch) raised vector coordinate direction
        ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable
          (by simp) coordinate)
        ((localRaisedAbelianGaugePotential_contDiff period hPeriod metric potential
          component patch).differentiable (by simp) coordinate)
        (pulledRegularFrameVector_differentiableAt period hPeriod reference patch
          coordinate second)
  have hFunction :
      (fun current => localMetricCoordinateForm period hPeriod metric patch current
        (raised current) (vector current)) =
        (regularFramePotentialCoefficient period hPeriod reference potential
          component second).toFun ∘ patch.coordinateMap := by
    funext current
    exact localMetricCoordinateForm_raised_frame period hPeriod reference metric potential
      component patch current second
  rw [hFunction, fderiv_comp_coordinateMap_pulledRegularFrameVector] at hProduct
  rw [localMetricDerivativeTrilinearForm_eq_leviCivita] at hProduct
  simp only [localLeviCivitaMetricCompatibilityForm_apply] at hProduct
  have hConnection : form (raised coordinate) connection =
      ∑ index : Fin 4,
        (pulledRegularFrameBasis period hPeriod reference patch coordinate).repr
            connection index *
          regularFramePotentialCoefficient period hPeriod reference potential
            component index (patch.coordinateMap coordinate) := by
    let basis := pulledRegularFrameBasis period hPeriod reference patch coordinate
    calc
      form (raised coordinate) connection =
          form (raised coordinate)
            (∑ index : Fin 4, basis.repr connection index • basis index) :=
        congrArg (form (raised coordinate)) (basis.sum_repr connection).symm
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro index _
        congr 1
        exact (congrArg (form (raised coordinate))
          (pulledRegularFrameBasis_apply period hPeriod reference patch coordinate index)).trans
            (localMetricCoordinateForm_raised_frame period hPeriod reference metric potential
              component patch coordinate index)
  rw [← hConnection]
  change form
      (fderiv Real raised coordinate direction +
        localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
          direction (raised coordinate)) (vector coordinate) = _
  have hConnectionExpand :
      form (raised coordinate) connection =
        form (raised coordinate) (fderiv Real vector coordinate direction) +
          form (raised coordinate)
            (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
              direction (vector coordinate)) := by
    exact map_add (form (raised coordinate)) _ _
  rw [hConnectionExpand]
  rw [map_add, LinearMap.add_apply]
  dsimp only [form, raised, vector, direction] at hProduct ⊢
  linarith [hProduct]

/-- The genuine Lorenz operator is the inverse-Gram contraction of the
covariant derivative of the potential coefficients in any fixed reference frame. -/
theorem globalGeneralMetricAbelianLorenzCodifferential_eq_regularFrameCovariantTrace
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential
        (patch.coordinateMap coordinate) component =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (regularFrameLorenzMetricMatrix period hPeriod reference metric
          (patch.coordinateMap coordinate))⁻¹ first second *
          (frameDerivative period hPeriod Real
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
              (regularFramePotentialCoefficient period hPeriod reference potential
                component second) (patch.coordinateMap coordinate) first -
            ∑ index : Fin 4,
              (pulledRegularFrameBasis period hPeriod reference patch coordinate).repr
                  (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
                    period hPeriod reference metric patch first second coordinate) index *
                regularFramePotentialCoefficient period hPeriod reference potential
                  component index (patch.coordinateMap coordinate)) := by
  let basis := pulledRegularFrameBasis period hPeriod reference patch coordinate
  let form := localMetricCoordinateForm period hPeriod metric patch coordinate
  have hNondegenerate : form.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate)
  have hSymmetric : ∀ first second, form first second = form second first := by
    intro first second
    dsimp only [form]
    rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
    exact metric.tensor.symmetric _ _ _
  have hGram : LinearMap.BilinForm.toMatrix basis form =
      regularFrameLorenzMetricMatrix period hPeriod reference metric
        (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    dsimp only [basis, form]
    rw [pulledRegularFrameBasis_apply, pulledRegularFrameBasis_apply,
      localMetricCoordinateForm_apply, coordinateMap_mfderiv_pulledRegularFrameVector,
      coordinateMap_mfderiv_pulledRegularFrameVector]
    rfl
  rw [globalGeneralMetricAbelianLorenzCodifferential_apply,
    globalGeneralMetricAbelianLorenzValue_eq_local, localAbelianLorenzDivergence_eq_trace,
    trace_eq_inverse_gram_contraction basis form hNondegenerate hSymmetric, hGram]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  congr 1
  dsimp only [basis, form]
  rw [pulledRegularFrameBasis_apply, pulledRegularFrameBasis_apply]
  exact covariant_pairing_eq_coefficient_derivative period hPeriod reference metric
    potential component patch coordinate first second

end
end P0EFTJanusRegularFrameLorenzCovariantTrace4D
end JanusFormal
