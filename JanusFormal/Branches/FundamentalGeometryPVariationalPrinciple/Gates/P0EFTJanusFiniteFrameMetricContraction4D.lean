import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameBRSTPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothInverseMusical4D

/-! # Inverse-metric contraction in a finite generating family

The smooth redundant dual reconstructs covectors exactly. Its inverse-metric
coefficients use the actual musical inverse, with an independent reference metric.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameMetricContraction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev effectiveBackground : EffectiveD8Background := ⟨period, hPeriod⟩

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point
private abbrev SmoothCovectorSection :=
  ContMDiffSection coverModelWithCorners (CoverCoordinates →L[Real] Real) ∞
    (fun point : EffectiveQuotient period hPeriod => TangentFiber period hPeriod point →L[Real] Real)

/-- Dual reconstruction remains exact when the generating family is redundant. -/
theorem finiteFrameCovector_reconstructs
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    covector = ∑ i : Fin frame.count, covector (frame.vectorAt point i) •
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i := by
  apply ContinuousLinearMap.ext
  intro vector
  simpa only [sum_apply, smul_apply, smul_eq_mul] using
    finiteFrameCovector_pairing period hPeriod frame reference point covector vector

/-- Exact intrinsic inverse-metric contraction in the reconstructed dual family. -/
theorem finiteFrameInverseMetric_pairing
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point first second =
      ∑ i : Fin frame.count, ∑ j : Fin frame.count,
        first (frame.vectorAt point i) * second (frame.vectorAt point j) *
          inverseMetricContraction period hPeriod metric point
            (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i)
            (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point j) := by
  calc
    _ = ∑ i : Fin frame.count, first (frame.vectorAt point i) *
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
          (inverseMetricSharp period hPeriod metric point second) :=
      finiteFrameCovector_pairing period hPeriod frame reference point first _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hSecond := congrArg
        (fun covector : TangentFiber period hPeriod point →L[Real] Real =>
          generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
            (inverseMetricSharp period hPeriod metric point covector))
        (finiteFrameCovector_reconstructs period hPeriod frame reference point second)
      simp only [map_sum, map_smul, smul_eq_mul] at hSecond
      rw [hSecond, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (mul_assoc _ _ _).symm

private theorem finiteFrameOperator_metric_symmetric
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    metric.tensor.tensor point
        (generalMetricFiniteFrameOperator period hPeriod frame metric point first) second =
      metric.tensor.tensor point first
        (generalMetricFiniteFrameOperator period hPeriod frame metric point second) := by
  rw [metric.tensor.symmetric point _ second]
  simp only [generalMetricFiniteFrameOperator_apply, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [metric.tensor.symmetric point second (frame.vectorAt point i),
    metric.tensor.symmetric point first (frame.vectorAt point i)]
  exact mul_comm _ _

private theorem finiteFrameCoefficientAt_eq_metric_solve
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (i : Fin frame.count)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i vector =
      reference.tensor.tensor point
        ((generalMetricFiniteFrameOperator period hPeriod frame reference point).inverse
          (frame.vectorAt point i)) vector := by
  have h := finiteFrameOperator_metric_symmetric period hPeriod frame reference point
    ((generalMetricFiniteFrameOperator period hPeriod frame reference point).inverse
      (frame.vectorAt point i))
    ((generalMetricFiniteFrameOperator period hPeriod frame reference point).inverse vector)
  rw [(generalMetricFiniteFrameOperator_isInvertible period hPeriod frame reference point
    ).self_apply_inverse, (generalMetricFiniteFrameOperator_isInvertible
      period hPeriod frame reference point).self_apply_inverse] at h
  exact h

/-- The canonical redundant dual is a genuine smooth covector section. -/
def finiteFrameDualCovector
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (i : Fin frame.count) : SmoothCovectorSection period hPeriod where
  toFun := fun point => reference.tensor.tensor point
    (generalMetricFiniteFrameSolve period hPeriod frame reference
      (smoothFrameVectorSection period hPeriod frame i) point)
  contMDiff_toFun := reference.tensor.tensor.contMDiff.clm_bundle_apply
    (generalMetricFiniteFrameSolve period hPeriod frame reference
      (smoothFrameVectorSection period hPeriod frame i)).contMDiff

@[simp] theorem finiteFrameDualCovector_apply
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (i : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameDualCovector period hPeriod frame reference i point =
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i := by
  apply ContinuousLinearMap.ext
  intro vector
  exact (finiteFrameCoefficientAt_eq_metric_solve period hPeriod frame reference point i vector).symm

/-- Smooth coefficients of the true inverse metric on the redundant dual. -/
def finiteFrameInverseMetricCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (i j : Fin frame.count) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod frame reference
    (effectiveD8SmoothInverseMusical (effectiveBackground period hPeriod) metric
      (finiteFrameDualCovector period hPeriod frame reference j)) i

@[simp] theorem finiteFrameInverseMetricCoefficient_apply
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (i j : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameInverseMetricCoefficient period hPeriod frame reference metric i j point =
      inverseMetricContraction period hPeriod metric point
        (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i)
        (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point j) := by
  change generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
    (inverseMetricSharp period hPeriod metric point
      (finiteFrameDualCovector period hPeriod frame reference j point)) = _
  rw [finiteFrameDualCovector_apply]
  rfl

end
end P0EFTJanusFiniteFrameMetricContraction4D
end JanusFormal
