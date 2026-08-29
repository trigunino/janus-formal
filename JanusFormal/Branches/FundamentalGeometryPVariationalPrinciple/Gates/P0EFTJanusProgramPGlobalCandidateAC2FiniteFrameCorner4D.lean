import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D

/-!
# Uniform C² projector corner for the intrinsic Candidate-A root

The existing redundant finite tangent frame has a smooth idempotent projector
`P`.  Its exact C² lift defines the bounded projection `X ↦ PXP`; the closed
fixed-point space is complete and contains the intrinsic Candidate-A root.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2FrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  C2FiniteMatrix period hPeriod frame.count

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

def c2FiniteFrameProjector
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FrameMatrix period hPeriod frame :=
  smoothFiniteMatrixToC2 period hPeriod frame.count
    (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric)

def c2GlobalCandidateAFiniteFrameRoot
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    C2FrameMatrix period hPeriod frame :=
  smoothFiniteMatrixToC2 period hPeriod frame.count
    (smoothGlobalCandidateAFiniteFrameRootCoefficients
      period hPeriod geometry frame)

theorem c2FiniteFrameProjector_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame metric)
        (c2FiniteFrameProjector period hPeriod frame metric) =
      c2FiniteFrameProjector period hPeriod frame metric := by
  rw [c2FiniteFrameProjector, c2FiniteMatrixProduct_smooth]
  exact congrArg
    (smoothFiniteMatrixToC2 period hPeriod frame.count)
    (smoothFiniteFrameProjectorCoefficients_idempotent
      period hPeriod frame metric)

theorem c2GlobalCandidateAFiniteFrameRoot_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame geometry.plusMetric)
        (c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame) =
      c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∧
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame)
        (c2FiniteFrameProjector period hPeriod frame geometry.plusMetric) =
      c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame := by
  constructor
  · rw [c2FiniteFrameProjector, c2GlobalCandidateAFiniteFrameRoot,
      c2FiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToC2 period hPeriod frame.count)
      (smoothGlobalCandidateAFiniteFrameRootCoefficients_corner
        period hPeriod geometry frame).1
  · rw [c2FiniteFrameProjector, c2GlobalCandidateAFiniteFrameRoot,
      c2FiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToC2 period hPeriod frame.count)
      (smoothGlobalCandidateAFiniteFrameRootCoefficients_corner
        period hPeriod geometry frame).2

def c2FiniteFrameCornerProjection
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FrameMatrix period hPeriod frame →L[Real]
      C2FrameMatrix period hPeriod frame :=
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let projector := c2FiniteFrameProjector period hPeriod frame metric
  (product projector).comp (product.flip projector)

@[simp]
theorem c2FiniteFrameCornerProjection_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    c2FiniteFrameCornerProjection period hPeriod frame metric matrix =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame metric)
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count matrix
          (c2FiniteFrameProjector period hPeriod frame metric)) :=
  rfl

theorem c2FiniteMatrixSandwich_idempotent
    (dimension : Nat)
    (projector matrix : C2FiniteMatrix period hPeriod dimension)
    (hProjector : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension projector
            (c2FiniteMatrixProduct
              (period := period) (hPeriod := hPeriod) dimension
              matrix projector)) projector) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := c2FiniteMatrixProduct_assoc period hPeriod dimension
  change product projector
      (product (product projector (product matrix projector)) projector) =
    product projector (product matrix projector)
  calc
    product projector
        (product (product projector (product matrix projector)) projector) =
      product (product projector
        (product projector (product matrix projector))) projector :=
      (hAssoc projector
        (product projector (product matrix projector)) projector).symm
    _ = product
        (product (product projector projector) (product matrix projector))
        projector := congrArg (fun current => product current projector)
      (hAssoc projector projector (product matrix projector)).symm
    _ = product (product projector (product matrix projector)) projector :=
      congrArg (fun current => product (product current
        (product matrix projector)) projector) hProjector
    _ = product projector (product (product matrix projector) projector) :=
      hAssoc projector (product matrix projector) projector
    _ = product projector
        (product matrix (product projector projector)) :=
      congrArg (product projector) (hAssoc matrix projector projector)
    _ = product projector (product matrix projector) :=
      congrArg (fun current => product projector (product matrix current))
        hProjector

theorem c2FiniteMatrixSandwich_left
    (dimension : Nat)
    (projector matrix : C2FiniteMatrix period hPeriod dimension)
    (hProjector : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hMatrix : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) =
      matrix) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector matrix =
      matrix := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := c2FiniteMatrixProduct_assoc period hPeriod dimension
  change product projector matrix = matrix
  calc
    product projector matrix =
        product projector (product projector (product matrix projector)) :=
      congrArg (product projector) hMatrix.symm
    _ = product (product projector projector) (product matrix projector) :=
      (hAssoc projector projector (product matrix projector)).symm
    _ = product projector (product matrix projector) :=
      congrArg (fun current => product current (product matrix projector))
        hProjector
    _ = matrix := hMatrix

theorem c2FiniteMatrixSandwich_right
    (dimension : Nat)
    (projector matrix : C2FiniteMatrix period hPeriod dimension)
    (hProjector : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hMatrix : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) =
      matrix) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension matrix projector =
      matrix := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := c2FiniteMatrixProduct_assoc period hPeriod dimension
  change product matrix projector = matrix
  calc
    product matrix projector =
        product (product projector (product matrix projector)) projector :=
      congrArg (fun current => product current projector) hMatrix.symm
    _ = product projector (product (product matrix projector) projector) :=
      hAssoc projector (product matrix projector) projector
    _ = product projector (product matrix (product projector projector)) :=
      congrArg (product projector) (hAssoc matrix projector projector)
    _ = product projector (product matrix projector) :=
      congrArg (fun current => product projector (product matrix current))
        hProjector
    _ = matrix := hMatrix

theorem c2FiniteMatrixSandwich_product
    (dimension : Nat)
    (projector first second : C2FiniteMatrix period hPeriod dimension)
    (hProjector : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hFirst : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first projector) =
      first)
    (hSecond : c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension second projector) =
      second) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension first second)
          projector) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first second := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := c2FiniteMatrixProduct_assoc period hPeriod dimension
  have hLeft := c2FiniteMatrixSandwich_left
    period hPeriod dimension projector first hProjector hFirst
  have hRight := c2FiniteMatrixSandwich_right
    period hPeriod dimension projector second hProjector hSecond
  change product projector (product (product first second) projector) =
    product first second
  calc
    product projector (product (product first second) projector) =
      product (product projector (product first second)) projector :=
      (hAssoc projector (product first second) projector).symm
    _ = product (product (product projector first) second) projector :=
      congrArg (fun current => product current projector)
        (hAssoc projector first second).symm
    _ = product (product first second) projector :=
      congrArg (fun current => product (product current second) projector) hLeft
    _ = product first (product second projector) :=
      hAssoc first second projector
    _ = product first second := congrArg (product first) hRight

theorem c2FiniteFrameCornerProjection_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    c2FiniteFrameCornerProjection period hPeriod frame metric
        (c2FiniteFrameCornerProjection period hPeriod frame metric matrix) =
      c2FiniteFrameCornerProjection period hPeriod frame metric matrix := by
  exact c2FiniteMatrixSandwich_idempotent period hPeriod frame.count
    (c2FiniteFrameProjector period hPeriod frame metric) matrix
    (c2FiniteFrameProjector_idempotent period hPeriod frame metric)

def c2FiniteFrameCornerSubmodule
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (C2FrameMatrix period hPeriod frame) :=
  (c2FiniteFrameCornerProjection period hPeriod frame metric -
    ContinuousLinearMap.id Real
      (C2FrameMatrix period hPeriod frame)).ker

abbrev C2FiniteFrameCorner
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  c2FiniteFrameCornerSubmodule period hPeriod frame metric

theorem c2FiniteFrameCorner_mem_iff
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    matrix ∈ c2FiniteFrameCornerSubmodule period hPeriod frame metric ↔
      c2FiniteFrameCornerProjection period hPeriod frame metric matrix =
        matrix := by
  change c2FiniteFrameCornerProjection period hPeriod frame metric matrix -
      matrix = 0 ↔ _
  exact sub_eq_zero

theorem c2FiniteFrameCornerProjection_mem
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    c2FiniteFrameCornerProjection period hPeriod frame metric matrix ∈
      c2FiniteFrameCornerSubmodule period hPeriod frame metric := by
  rw [c2FiniteFrameCorner_mem_iff]
  exact c2FiniteFrameCornerProjection_idempotent
    period hPeriod frame metric matrix

theorem c2GlobalCandidateAFiniteFrameRoot_mem_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∈
      c2FiniteFrameCornerSubmodule
        period hPeriod frame geometry.plusMetric := by
  rw [c2FiniteFrameCorner_mem_iff]
  change c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) frame.count
      (c2FiniteFrameProjector period hPeriod frame geometry.plusMetric)
      (c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame)
        (c2FiniteFrameProjector
          period hPeriod frame geometry.plusMetric)) =
    c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame
  rw [(c2GlobalCandidateAFiniteFrameRoot_corner
    period hPeriod geometry frame).2]
  exact (c2GlobalCandidateAFiniteFrameRoot_corner
    period hPeriod geometry frame).1

theorem c2FiniteFrameCornerSubmodule_isClosed
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IsClosed (c2FiniteFrameCornerSubmodule
      period hPeriod frame metric : Set (C2FrameMatrix period hPeriod frame)) :=
  (c2FiniteFrameCornerProjection period hPeriod frame metric -
    ContinuousLinearMap.id Real
      (C2FrameMatrix period hPeriod frame)).isClosed_ker

@[implicit_reducible]
def c2FiniteFrameCornerCompleteSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (C2FiniteFrameCorner period hPeriod frame metric) := by
  letI : IsClosed
      (c2FiniteFrameCornerSubmodule period hPeriod frame metric :
        Set (C2FrameMatrix period hPeriod frame)) :=
    c2FiniteFrameCornerSubmodule_isClosed period hPeriod frame metric
  exact IsClosed.completeSpace_coe

/-- Summary gate for the actual intrinsic finite-frame root in the C² core. -/
theorem global_candidate_a_c2_finite_frame_corner_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    IsClosed (c2FiniteFrameCornerSubmodule
      period hPeriod frame geometry.plusMetric :
        Set (C2FrameMatrix period hPeriod frame)) ∧
      c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∈
        c2FiniteFrameCornerSubmodule
          period hPeriod frame geometry.plusMetric := by
  exact ⟨c2FiniteFrameCornerSubmodule_isClosed
      period hPeriod frame geometry.plusMetric,
    c2GlobalCandidateAFiniteFrameRoot_mem_corner
      period hPeriod geometry frame⟩

end

end P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
end JanusFormal
