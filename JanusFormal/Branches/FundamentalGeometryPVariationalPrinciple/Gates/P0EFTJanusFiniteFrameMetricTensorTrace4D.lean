import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricContraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

/-! # Intrinsic tensor trace in a redundant finite family

The actual trace and its differential are evaluated through the reconstructed
dual family. No global basis or inverse of a redundant Gram matrix is used.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameMetricTensorTrace4D

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D

private theorem trace_of_reconstruction
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    {ι : Type*} [Fintype ι]
    (vectors : ι → V) (coefficients : ι → V →ₗ[Real] Real)
    (reconstructs : ∀ vector, vector = ∑ i, coefficients i vector • vectors i)
    (operator : V →ₗ[Real] V) :
    LinearMap.trace Real V operator = ∑ i, coefficients i (operator (vectors i)) := by
  have hOperator : operator = ∑ i, (coefficients i).smulRight (operator (vectors i)) := by
    apply LinearMap.ext
    intro vector
    have h := congrArg operator (reconstructs vector)
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul] using h
  have hTrace := congrArg (LinearMap.trace Real V) hOperator
  simpa only [map_sum, LinearMap.trace_smulRight] using hTrace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

/-- Redundant reconstruction gives the trace of every actual endomorphism. -/
theorem finiteFrame_endomorphism_trace
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (operator : TangentFiber period hPeriod point →ₗ[Real] TangentFiber period hPeriod point) :
    LinearMap.trace Real (TangentFiber period hPeriod point) operator =
      ∑ i : Fin frame.count,
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
          (operator (frame.vectorAt point i)) := by
  exact trace_of_reconstruction (V := TangentFiber period hPeriod point) (frame.vectorAt point)
    (fun i => (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i).toLinearMap)
    (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame reference point) operator

/-- The inverse-metric contraction computes the genuine tensor trace. -/
theorem generalMetricTensorTraceAt_eq_finiteFrameContraction
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric tensor point =
      ∑ i : Fin frame.count, ∑ j : Fin frame.count,
        inverseMetricContraction period hPeriod metric point
          (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i)
          (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point j) *
            tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) := by
  have hTrace := finiteFrame_endomorphism_trace period hPeriod frame reference point
    (raisedGeneralMetricTensorAt period hPeriod metric tensor point).toLinearMap
  apply hTrace.trans
  apply Finset.sum_congr rfl
  intro i _
  have hCovector := congrArg
    (fun covector : TangentFiber period hPeriod point →L[Real] Real =>
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
        (inverseMetricSharp period hPeriod metric point covector))
    (finiteFrameCovector_reconstructs period hPeriod frame reference point
      (tensor.tensor point (frame.vectorAt point i)))
  simp only [map_sum, map_smul, smul_eq_mul] at hCovector
  change generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
      (inverseMetricSharp period hPeriod metric point
        (tensor.tensor point (frame.vectorAt point i))) = _
  rw [hCovector]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The same identity uses the genuinely smooth inverse-metric coefficients. -/
theorem generalMetricTensorTrace_eq_finiteFrameContraction
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTrace period hPeriod metric tensor point =
      ∑ i : Fin frame.count, ∑ j : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric i j point *
          tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) := by
  simpa only [generalMetricTensorTrace_apply, finiteFrameInverseMetricCoefficient_apply] using
    generalMetricTensorTraceAt_eq_finiteFrameContraction period hPeriod frame reference metric tensor point

/-- The trace part of De Donder differentiates that exact finite contraction. -/
theorem generalMetricTensorTraceDifferential_eq_finiteFrameDerivative
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    generalMetricTensorTraceDifferential period hPeriod metric tensor point vector =
      mfderiv coverModelWithCorners 𝓘(Real, Real)
        (fun current : EffectiveQuotient period hPeriod =>
          ∑ i : Fin frame.count, ∑ j : Fin frame.count,
            finiteFrameInverseMetricCoefficient period hPeriod frame reference metric i j current *
              tensor.tensor current (frame.vectorAt current i) (frame.vectorAt current j)) point vector := by
  have hTrace : (fun current => generalMetricTensorTrace period hPeriod metric tensor current) =
      (fun current : EffectiveQuotient period hPeriod =>
        ∑ i : Fin frame.count, ∑ j : Fin frame.count,
          finiteFrameInverseMetricCoefficient period hPeriod frame reference metric i j current *
            tensor.tensor current (frame.vectorAt current i) (frame.vectorAt current j)) := by
    funext current
    exact generalMetricTensorTrace_eq_finiteFrameContraction period hPeriod frame reference metric tensor current
  have hDerivative := congrArg
    (fun scalar : EffectiveQuotient period hPeriod → Real =>
      mfderiv coverModelWithCorners 𝓘(Real, Real) scalar point vector) hTrace
  exact hDerivative

end
end P0EFTJanusFiniteFrameMetricTensorTrace4D
end JanusFormal
