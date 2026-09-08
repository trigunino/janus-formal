import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D

/-! # Explicit derivative of the completed finite-frame relative target -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedRelativeC2TargetDerivativeAtCenter4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (C2FiniteFrameCorner period hPeriod frame metric) := inferInstance
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)

private abbrev MetricCore :=
  GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
private abbrev Model :=
  PairedFiniteFrameMetricC2Core period hPeriod geometry frame
private abbrev Corner :=
  C2FiniteFrameCorner period hPeriod frame geometry.plusMetric

private theorem generalMetricRelativeC2InverseMatrix_zero :
    generalMetricRelativeC2InverseMatrix period hPeriod frame geometry.plusMetric 0 =
      c2FiniteMatrixIdentity period hPeriod frame.count := by
  have hInverse := c2FiniteMatrixProduct_inverse_right period hPeriod frame.count
    (c2FiniteMatrixIdentity period hPeriod frame.count)
    (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count)
  change c2FiniteMatrixInverse period hPeriod frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count + 0) = _
  rw [c2FiniteMatrixProduct_identity_left] at hInverse
  simpa using hInverse

/-- Linearization `δ(P (I + A₊)⁻¹ (R₀² + A₋) P)` at the affine origin. -/
def pairedFiniteFrameRelativeC2TargetLinearizationAtZero :
    Model period hPeriod geometry frame →L[Real] Corner period hPeriod geometry frame :=
  (finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric).comp
    (((generalMetricRelativeC2CoreToMatrix period hPeriod frame geometry.plusMetric).comp
        (ContinuousLinearMap.snd Real
          (MetricCore period hPeriod geometry frame)
          (MetricCore period hPeriod geometry frame))) +
      (((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count).flip
          (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
            (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1).comp
        ((generalMetricRelativeC2InverseMatrixDerivativeAtZero period hPeriod frame
          geometry.plusMetric).comp
          (ContinuousLinearMap.fst Real
            (MetricCore period hPeriod geometry frame)
            (MetricCore period hPeriod geometry frame)))))

theorem pairedFiniteFrameRelativeC2Target_hasFDerivAt_zero_explicit :
    HasFDerivAt (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame)
      (pairedFiniteFrameRelativeC2TargetLinearizationAtZero period hPeriod geometry frame) 0 := by
  have hInverse :=
    (generalMetricRelativeC2InverseMatrix_hasFDerivAt_zero period hPeriod frame
      geometry.plusMetric).comp 0
      (ContinuousLinearMap.fst Real
        (MetricCore period hPeriod geometry frame)
        (MetricCore period hPeriod geometry frame)).hasFDerivAt
  have hMinus :=
    (generalMetricRelativeC2CoreToMatrix period hPeriod frame geometry.plusMetric).hasFDerivAt.comp 0
      (ContinuousLinearMap.snd Real
        (MetricCore period hPeriod geometry frame)
        (MetricCore period hPeriod geometry frame)).hasFDerivAt
  have hNumerator := hMinus.const_add
    (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
      (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1
  have hProduct :=
    ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count).hasFDerivAt.comp
      0 hInverse).clm_apply hNumerator
  have hProjected :=
    (finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric).hasFDerivAt.comp
      0 hProduct
  refine (hProjected.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · apply ContinuousLinearMap.ext
    intro direction
    simp only [pairedFiniteFrameRelativeC2TargetLinearizationAtZero,
      ContinuousLinearMap.comp_apply, add_apply,
      Function.comp_apply, map_zero, add_zero]
    rw [generalMetricRelativeC2InverseMatrix_zero,
      c2FiniteMatrixProduct_identity_left]
    rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

theorem pairedFiniteFrameRelativeC2TargetDerivativeAtZero_eq_linearization :
    pairedFiniteFrameRelativeC2TargetDerivativeAtZero period hPeriod geometry frame =
      pairedFiniteFrameRelativeC2TargetLinearizationAtZero period hPeriod geometry frame :=
  (pairedFiniteFrameRelativeC2Target_hasFDerivAt_zero period hPeriod geometry frame).unique
    (pairedFiniteFrameRelativeC2Target_hasFDerivAt_zero_explicit period hPeriod geometry frame)

@[simp]
theorem pairedFiniteFrameRelativeC2TargetDerivativeAtZero_apply
    (direction : Model period hPeriod geometry frame) :
    pairedFiniteFrameRelativeC2TargetDerivativeAtZero period hPeriod geometry frame direction =
      finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric
        (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
            direction.1.1
            (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
              (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1 +
          direction.2.1) := by
  rw [pairedFiniteFrameRelativeC2TargetDerivativeAtZero_eq_linearization]
  change finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric
      (direction.2.1 + c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
        frame.count
        (generalMetricRelativeC2InverseMatrixDerivativeAtZero period hPeriod frame
          geometry.plusMetric direction.1)
        (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
          (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1) = _
  rw [generalMetricRelativeC2InverseMatrixDerivativeAtZero_apply]
  have hNeg :
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
          (-direction.1.1)
          (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
            (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1 =
        -c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
          direction.1.1
          (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
            (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1 :=
    ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count).flip
      (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
        (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1).map_neg
        direction.1.1
  rw [hNeg]
  congr 1
  abel

variable (hRegular : ∀ point, Function.Bijective
  (intrinsicCandidateASylvesterAt period hPeriod geometry point))

/-- Exact Sylvester equation with the affine target velocity expanded. -/
theorem pairedFiniteFrameMetricC2RootDerivativeAtZero_sylvester_explicit
    (direction : Model period hPeriod geometry frame) :
    c2FiniteFrameCornerSylvester period hPeriod frame geometry.plusMetric
        (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)
        (pairedFiniteFrameMetricC2RootDerivativeAtZero period hPeriod geometry frame hRegular
          direction) =
      finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric
        (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
            direction.1.1
            (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
              (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1 +
          direction.2.1) := by
  rw [pairedFiniteFrameMetricC2RootDerivativeAtZero_sylvester,
    pairedFiniteFrameRelativeC2TargetDerivativeAtZero_apply]

end
end P0EFTJanusFiniteFramePairedRelativeC2TargetDerivativeAtCenter4D
end JanusFormal
