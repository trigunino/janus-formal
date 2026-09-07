import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

/-! # Intrinsic BRST pairings in a finite generating family

The coefficients come from the actual redundant reconstruction. No global
basis or inverse Gram matrix is required. These are exact smooth-field
pairings; no completed C² action is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameBRSTPairing4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point
private abbrev SmoothTangentSection :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞ (TangentFiber period hPeriod)

/-- Covector contraction through the true finite-frame reconstruction. -/
theorem finiteFrameCovector_pairing
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (covector : TangentFiber period hPeriod point →L[Real] Real)
    (vector : TangentFiber period hPeriod point) :
    covector vector = ∑ i : Fin frame.count,
      covector (frame.vectorAt point i) *
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i vector := by
  calc
    covector vector = covector (∑ i : Fin frame.count,
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i vector •
          frame.vectorAt point i) :=
      congrArg covector (generalMetricFiniteFrameCoefficientAt_reconstructs
        period hPeriod frame reference point vector)
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- Bilinear metric contraction; the coefficient reference may be independent
of the metric being paired. -/
theorem finiteFrameMetric_pairing
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    metric.tensor.tensor point first second = ∑ i : Fin frame.count, ∑ j : Fin frame.count,
      metric.tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) *
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i first *
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point j second := by
  calc
    metric.tensor.tensor point first second = ∑ i : Fin frame.count,
        metric.tensor.tensor point (frame.vectorAt point i) second *
          generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i first := by
      rw [metric.tensor.symmetric point first second]
      have h := finiteFrameCovector_pairing period hPeriod frame reference point
        (metric.tensor.tensor point second) first
      apply h.trans
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun value : Real => value *
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i first)
        (metric.tensor.symmetric point second (frame.vectorAt point i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finiteFrameCovector_pairing period hPeriod frame reference point
        (metric.tensor.tensor point (frame.vectorAt point i)) second, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Smooth-field version, with the constructed smooth dual coefficients. -/
theorem finiteFrameSmoothCovector_pairing
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    covector (vector point) = ∑ i : Fin frame.count,
      covector (frame.vectorAt point i) *
        generalMetricFiniteFrameCoefficient period hPeriod frame reference vector i point :=
  finiteFrameCovector_pairing period hPeriod frame reference point covector (vector point)

/-- The actual Nakanishi--Lautrup quadratic pairing in redundant coefficients. -/
theorem finiteFrameSmoothMetric_self_pairing
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    metric.tensor.tensor point (vector point) (vector point) =
      ∑ i : Fin frame.count, ∑ j : Fin frame.count,
        metric.tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference vector i point *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference vector j point :=
  finiteFrameMetric_pairing period hPeriod frame reference metric point (vector point) (vector point)

/-- Both BRST contractions on the unconditionally constructed finite smooth
generating family of the actual quotient. -/
theorem finite_frame_BRST_pairing_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    let frame := finiteSmoothTangentFrame period hPeriod
    (covector (vector point) = ∑ i : Fin frame.count,
      covector (frame.vectorAt point i) *
        generalMetricFiniteFrameCoefficient period hPeriod frame metric vector i point) ∧
    (metric.tensor.tensor point (vector point) (vector point) =
      ∑ i : Fin frame.count, ∑ j : Fin frame.count,
        metric.tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) *
          generalMetricFiniteFrameCoefficient period hPeriod frame metric vector i point *
          generalMetricFiniteFrameCoefficient period hPeriod frame metric vector j point) := by
  exact ⟨finiteFrameSmoothCovector_pairing period hPeriod
    (finiteSmoothTangentFrame period hPeriod) metric vector point covector,
    finiteFrameSmoothMetric_self_pairing period hPeriod
      (finiteSmoothTangentFrame period hPeriod) metric metric vector point⟩

end
end P0EFTJanusFiniteFrameBRSTPairing4D
end JanusFormal
