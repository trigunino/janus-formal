import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameLorenzCovariantTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

/-! # The intrinsic tensor trace in an independent regular frame

The inverse Gram contraction is proved equal to the actual fiberwise trace.
Its differential is transported through each genuine holonomic chart.
The reference frame need not belong to the metric being traced.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameMetricTensorTrace4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D

/-- Basis-independent trace evaluated by an inverse Gram contraction. -/
theorem trace_eq_inverse_gram_contraction
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 4) Real V)
    (form : LinearMap.BilinForm Real V)
    (hNondegenerate : form.Nondegenerate)
    (hSymmetric : ∀ first second, form first second = form second first)
    (operator : V →ₗ[Real] V) :
    LinearMap.trace Real V operator =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (LinearMap.BilinForm.toMatrix basis form)⁻¹ first second *
          form (operator (basis first)) (basis second) := by
  let gram := LinearMap.BilinForm.toMatrix basis form
  have hInverse : gram⁻¹ * gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero basis).mp hNondegenerate))
  have hPairing (vector : V) :
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
  have hCoordinates (vector : V) :
      (fun index => basis.repr vector index) =
        gram⁻¹ *ᵥ (fun index => form vector (basis index)) := by
    rw [hPairing, Matrix.mulVec_mulVec, hInverse, Matrix.one_mulVec]
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro first _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact congrFun (hCoordinates (operator (basis first))) first

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- The trace uses the supplied metric, while all tensor coefficients use the fixed frame. -/
theorem generalMetricTensorTraceAt_eq_regularFrameContraction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (regularFrameLorenzMetricMatrix period hPeriod reference metric point)⁻¹ first second *
          tensor.tensor point (reference.frame first point) (reference.frame second point) := by
  let form := (metric.tensor.tensor point).toBilinForm
  have hNondegenerate : form.Nondegenerate := by
    constructor
    · intro vector hVector
      apply metric_nondegenerate_at period hPeriod metric
      apply ContinuousLinearMap.ext
      intro second
      simpa [form] using hVector second
    · intro vector hVector
      apply metric_nondegenerate_at period hPeriod metric
      apply ContinuousLinearMap.ext
      intro second
      rw [metric.tensor.symmetric]
      simpa [form] using hVector second
  have hFrame (index : Fin 4) :
      regularMetricBasisAt period hPeriod reference point index = reference.frame index point := by
    simp [regularMetricBasisAt, RegularGeneralLorentzMetric.frame_eq_basisFun]
  have hGram : LinearMap.BilinForm.toMatrix
      (regularMetricBasisAt period hPeriod reference point) form =
        regularFrameLorenzMetricMatrix period hPeriod reference metric point := by
    ext first second
    simp only [LinearMap.BilinForm.toMatrix_apply, hFrame]
    rfl
  have hRaised (first second : TangentSpace coverModelWithCorners point) :
      form ((raisedGeneralMetricTensorAt period hPeriod metric tensor point).toLinearMap first)
        second = tensor.tensor point first second := by
    change metric.tensor.tensor point
      ((metric.musical point).symm (tensor.tensor point first)) second = _
    rw [← metric.musical_eq_tensor]
    exact congrArg (fun covector => covector second)
      ((metric.musical point).apply_symm_apply (tensor.tensor point first))
  have hTrace := trace_eq_inverse_gram_contraction
    (regularMetricBasisAt period hPeriod reference point) form hNondegenerate
    (fun first second => metric.tensor.symmetric point first second)
    (raisedGeneralMetricTensorAt period hPeriod metric tensor point).toLinearMap
  rw [hGram] at hTrace
  simp only [hRaised, hFrame] at hTrace
  exact hTrace

/-- The genuine trace differential is the local derivative of that same inverse-Gram formula. -/
theorem generalMetricTensorTraceDifferential_eq_regularFrameLocalDerivative
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction : Fin 4) :
    generalMetricTensorTraceDifferential period hPeriod metric tensor
        (patch.coordinateMap coordinate)
        (reference.frame direction (patch.coordinateMap coordinate)) =
      fderiv Real (fun current =>
        ∑ first : Fin 4, ∑ second : Fin 4,
          (regularFrameLorenzMetricMatrix period hPeriod reference metric
            (patch.coordinateMap current))⁻¹ first second *
          tensor.tensor (patch.coordinateMap current)
            (reference.frame first (patch.coordinateMap current))
            (reference.frame second (patch.coordinateMap current))) coordinate
        (pulledRegularFrameVector period hPeriod reference patch direction coordinate) := by
  have hLocal := fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod reference
    (generalMetricTensorTrace period hPeriod metric tensor) patch coordinate direction
  calc
    _ = frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        (generalMetricTensorTrace period hPeriod metric tensor)
        (patch.coordinateMap coordinate) direction := rfl
    _ = _ := hLocal.symm.trans (by
      apply congrArg (fun field : Vector4 → Real =>
        fderiv Real field coordinate
          (pulledRegularFrameVector period hPeriod reference patch direction coordinate))
      funext current
      exact generalMetricTensorTraceAt_eq_regularFrameContraction period hPeriod
        reference metric tensor (patch.coordinateMap current))

end
end P0EFTJanusRegularFrameMetricTensorTrace4D
end JanusFormal
