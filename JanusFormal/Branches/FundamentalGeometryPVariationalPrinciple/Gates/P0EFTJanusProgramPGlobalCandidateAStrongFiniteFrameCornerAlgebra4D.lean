import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D

/-!
# Strong algebra of the Candidate-A finite-frame projector corner

The closed complete projector corner already constructed from the redundant
finite tangent generators is stable under the established strong matrix
product.  This file internalizes that bounded bilinear product, proves that
squaring is smooth with the exact Sylvester derivative, and places the
intrinsic Candidate-A root in the resulting Banach algebra.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

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

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

theorem strongFiniteFrameCorner_product_mem
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : StrongFiniteFrameCorner period hPeriod frame metric) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1 second.1 ∈
      strongFiniteFrameCornerSubmodule period hPeriod frame metric := by
  rw [strongFiniteFrameCorner_mem_iff]
  exact strongFiniteMatrixSandwich_product period hPeriod frame.count
    (strongFiniteFrameProjector period hPeriod frame metric) first.1 second.1
    (strongFiniteFrameProjector_idempotent period hPeriod frame metric)
    ((strongFiniteFrameCorner_mem_iff period hPeriod frame metric first.1).mp
      first.2)
    ((strongFiniteFrameCorner_mem_iff period hPeriod frame metric second.1).mp
      second.2)

private def strongFiniteFrameCornerProductLinear
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    StrongFiniteFrameCorner period hPeriod frame metric →ₗ[Real]
      StrongFiniteFrameCorner period hPeriod frame metric →ₗ[Real]
        StrongFiniteFrameCorner period hPeriod frame metric :=
  LinearMap.mk₂ Real
    (fun first second =>
      ⟨strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count first.1 second.1,
        strongFiniteFrameCorner_product_mem
          period hPeriod frame metric first second⟩)
    (by
      intro first second third
      apply Subtype.ext
      exact congrArg (fun operator => operator third.1)
        ((strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count).map_add
            first.1 second.1))
    (by
      intro scalar first second
      apply Subtype.ext
      exact congrArg (fun operator => operator second.1)
        ((strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count).map_smul
            scalar first.1))
    (by
      intro first second third
      apply Subtype.ext
      exact (strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1).map_add
          second.1 third.1)
    (by
      intro scalar first second
      apply Subtype.ext
      exact (strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1).map_smul
          scalar second.1)

/-- Continuous bilinear multiplication internal to the closed projector
corner. -/
def strongFiniteFrameCornerProduct
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
      StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric :=
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  LinearMap.mkContinuous₂
    (strongFiniteFrameCornerProductLinear period hPeriod frame metric)
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
theorem strongFiniteFrameCornerProduct_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : StrongFiniteFrameCorner period hPeriod frame metric) :
    (strongFiniteFrameCornerProduct period hPeriod frame metric first second).1 =
      strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count first.1 second.1 :=
  rfl

def strongFiniteFrameCornerSquare
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : StrongFiniteFrameCorner period hPeriod frame metric) :
    StrongFiniteFrameCorner period hPeriod frame metric :=
  strongFiniteFrameCornerProduct period hPeriod frame metric matrix matrix

def strongFiniteFrameCornerSylvester
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric) :
    StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
      StrongFiniteFrameCorner period hPeriod frame metric :=
  strongFiniteFrameCornerProduct period hPeriod frame metric root +
    ((strongFiniteFrameCornerProduct period hPeriod frame metric).flip root :
      StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric)

theorem strongFiniteFrameCornerSquare_hasFDerivAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric) :
    HasFDerivAt (strongFiniteFrameCornerSquare period hPeriod frame metric)
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root) root := by
  have hDerivative :=
    (strongFiniteFrameCornerProduct period hPeriod frame metric).hasFDerivAt
      (x := root) |>.clm_apply (hasFDerivAt_id root)
  exact hDerivative.congr_fderiv rfl

theorem strongFiniteFrameCornerSquare_contDiff
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (strongFiniteFrameCornerSquare period hPeriod frame metric) :=
  (strongFiniteFrameCornerProduct period hPeriod frame metric).contDiff.clm_apply
    contDiff_id

/-- The intrinsic root, now as an element of the complete strong projector
corner. -/
def strongGlobalCandidateAFiniteFrameRootCorner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric :=
  ⟨strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame,
    strongGlobalCandidateAFiniteFrameRoot_mem_corner
      period hPeriod geometry frame⟩




/-- Summary gate for the complete strong projector-corner algebra. -/
theorem global_candidate_a_strong_finite_frame_corner_algebra_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    ContDiff Real ⊤
      (strongFiniteFrameCornerSquare
        period hPeriod frame geometry.plusMetric) ∧
      HasFDerivAt
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame))
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) := by
  exact ⟨strongFiniteFrameCornerSquare_contDiff
      period hPeriod frame geometry.plusMetric,
    strongFiniteFrameCornerSquare_hasFDerivAt
      period hPeriod frame geometry.plusMetric
      (strongGlobalCandidateAFiniteFrameRootCorner
        period hPeriod geometry frame)⟩

end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D
end JanusFormal
