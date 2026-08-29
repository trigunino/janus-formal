import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D

/-!
# Uniform C² algebra of the Candidate-A finite-frame corner

The closed projector corner is stable under the bounded C² matrix product.
Squaring is smooth there, with the exact internal Sylvester derivative, and
the intrinsic Candidate-A root is an element of this complete algebra.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

theorem c2FiniteFrameCorner_product_mem
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : C2FiniteFrameCorner period hPeriod frame metric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1 second.1 ∈
      c2FiniteFrameCornerSubmodule period hPeriod frame metric := by
  rw [c2FiniteFrameCorner_mem_iff]
  exact c2FiniteMatrixSandwich_product period hPeriod frame.count
    (c2FiniteFrameProjector period hPeriod frame metric) first.1 second.1
    (c2FiniteFrameProjector_idempotent period hPeriod frame metric)
    ((c2FiniteFrameCorner_mem_iff period hPeriod frame metric first.1).mp
      first.2)
    ((c2FiniteFrameCorner_mem_iff period hPeriod frame metric second.1).mp
      second.2)

private def c2FiniteFrameCornerProductLinear
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FiniteFrameCorner period hPeriod frame metric →ₗ[Real]
      C2FiniteFrameCorner period hPeriod frame metric →ₗ[Real]
        C2FiniteFrameCorner period hPeriod frame metric :=
  LinearMap.mk₂ Real
    (fun first second =>
      ⟨c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count first.1 second.1,
        c2FiniteFrameCorner_product_mem
          period hPeriod frame metric first second⟩)
    (by
      intro first second third
      apply Subtype.ext
      exact congrArg (fun operator => operator third.1)
        ((c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count).map_add
            first.1 second.1))
    (by
      intro scalar first second
      apply Subtype.ext
      exact congrArg (fun operator => operator second.1)
        ((c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count).map_smul
            scalar first.1))
    (by
      intro first second third
      apply Subtype.ext
      exact (c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1).map_add
          second.1 third.1)
    (by
      intro scalar first second
      apply Subtype.ext
      exact (c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1).map_smul
          scalar second.1)

/-- Continuous bilinear product internal to the C² projector corner. -/
def c2FiniteFrameCornerProduct
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FiniteFrameCorner period hPeriod frame metric →L[Real]
      C2FiniteFrameCorner period hPeriod frame metric →L[Real]
        C2FiniteFrameCorner period hPeriod frame metric :=
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  LinearMap.mkContinuous₂
    (c2FiniteFrameCornerProductLinear period hPeriod frame metric)
    ‖product‖
    (by
      intro first second
      change ‖product first.1 second.1‖ ≤
        ‖product‖ * ‖first‖ * ‖second‖
      calc
        ‖product first.1 second.1‖ ≤
            ‖product first.1‖ * ‖second.1‖ :=
          (product first.1).le_opNorm second.1
        _ ≤ (‖product‖ * ‖first.1‖) * ‖second.1‖ := by
          gcongr
          exact product.le_opNorm first.1
        _ = ‖product‖ * ‖first‖ * ‖second‖ := rfl)

@[simp]
theorem c2FiniteFrameCornerProduct_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : C2FiniteFrameCorner period hPeriod frame metric) :
    (c2FiniteFrameCornerProduct period hPeriod frame metric first second).1 =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1 second.1 :=
  rfl

def c2FiniteFrameCornerSquare
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : C2FiniteFrameCorner period hPeriod frame metric) :
    C2FiniteFrameCorner period hPeriod frame metric :=
  c2FiniteFrameCornerProduct period hPeriod frame metric matrix matrix

def c2FiniteFrameCornerSylvester
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : C2FiniteFrameCorner period hPeriod frame metric) :
    C2FiniteFrameCorner period hPeriod frame metric →L[Real]
      C2FiniteFrameCorner period hPeriod frame metric :=
  c2FiniteFrameCornerProduct period hPeriod frame metric root +
    ((c2FiniteFrameCornerProduct period hPeriod frame metric).flip root :
      C2FiniteFrameCorner period hPeriod frame metric →L[Real]
        C2FiniteFrameCorner period hPeriod frame metric)

theorem c2FiniteFrameCornerSquare_hasFDerivAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : C2FiniteFrameCorner period hPeriod frame metric) :
    HasFDerivAt (c2FiniteFrameCornerSquare period hPeriod frame metric)
      (c2FiniteFrameCornerSylvester period hPeriod frame metric root) root := by
  have hDerivative :=
    (c2FiniteFrameCornerProduct period hPeriod frame metric).hasFDerivAt
      (x := root) |>.clm_apply (hasFDerivAt_id root)
  exact hDerivative.congr_fderiv rfl

theorem c2FiniteFrameCornerSquare_contDiff
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (c2FiniteFrameCornerSquare period hPeriod frame metric) :=
  (c2FiniteFrameCornerProduct period hPeriod frame metric).contDiff.clm_apply
    contDiff_id

/-- Intrinsic root as an element of the complete C² projector corner. -/
def c2GlobalCandidateAFiniteFrameRootCorner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    C2FiniteFrameCorner period hPeriod frame geometry.plusMetric :=
  ⟨c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame,
    c2GlobalCandidateAFiniteFrameRoot_mem_corner
      period hPeriod geometry frame⟩

theorem global_candidate_a_c2_finite_frame_corner_algebra_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    ContDiff Real ⊤
      (c2FiniteFrameCornerSquare
        period hPeriod frame geometry.plusMetric) ∧
      HasFDerivAt
        (c2FiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (c2FiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (c2GlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame))
        (c2GlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) := by
  exact ⟨c2FiniteFrameCornerSquare_contDiff
      period hPeriod frame geometry.plusMetric,
    c2FiniteFrameCornerSquare_hasFDerivAt
      period hPeriod frame geometry.plusMetric
      (c2GlobalCandidateAFiniteFrameRootCorner
        period hPeriod geometry frame)⟩

end

end P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
end JanusFormal
