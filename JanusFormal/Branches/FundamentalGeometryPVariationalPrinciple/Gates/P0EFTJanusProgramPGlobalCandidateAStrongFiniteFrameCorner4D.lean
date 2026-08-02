import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

/-!
# Strong projector corner for the intrinsic Candidate-A root

The existing finite smooth tangent generators encode intrinsic endomorphisms
in a redundant matrix algebra.  Their identity matrix is therefore a smooth
idempotent projector `P`, not an ambient identity.  Using the arbitrary finite
strong matrix product, this file constructs the bounded idempotent map
`X ↦ P X P`, its closed complete fixed-point subspace, and proves that the
general intrinsic Candidate-A root belongs to it.  No global tangent frame or
new geometric assumption is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D

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
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev StrongFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  StrongFiniteMatrix period hPeriod frame.count

private abbrev SmoothFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  SmoothFiniteMatrix period hPeriod frame.count

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

def smoothFiniteFrameProjectorCoefficients
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothFrameMatrix period hPeriod frame :=
  fun row column =>
    finiteFrameProjectorCoefficient period hPeriod frame metric row column

def strongFiniteFrameProjector
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    StrongFrameMatrix period hPeriod frame :=
  smoothFiniteMatrixToStrong period hPeriod frame.count
    (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric)

def smoothGlobalCandidateAFiniteFrameRootCoefficients
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    SmoothFrameMatrix period hPeriod frame :=
  fun row column => globalCandidateAFiniteFrameRootCoefficient
    period hPeriod geometry frame row column

def strongGlobalCandidateAFiniteFrameRoot
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StrongFrameMatrix period hPeriod frame :=
  smoothFiniteMatrixToStrong period hPeriod frame.count
    (smoothGlobalCandidateAFiniteFrameRootCoefficients
      period hPeriod geometry frame)

theorem smoothFiniteFrameProjectorCoefficients_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric)
        (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric) =
      smoothFiniteFrameProjectorCoefficients period hPeriod frame metric := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hIdempotent := finiteFrameProjectorMatrixAt_idempotent
    period hPeriod frame metric point
  have hEntry := congrFun (congrFun hIdempotent row) column
  simp only [smoothFiniteMatrixProduct,
    smoothFiniteFrameProjectorCoefficients,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
  simp_rw [finiteFrameProjectorCoefficient_apply]
  exact hEntry

theorem strongFiniteFrameProjector_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (strongFiniteFrameProjector period hPeriod frame metric)
        (strongFiniteFrameProjector period hPeriod frame metric) =
      strongFiniteFrameProjector period hPeriod frame metric := by
  rw [strongFiniteFrameProjector]
  rw [strongFiniteMatrixProduct_smooth]
  exact congrArg
    (smoothFiniteMatrixToStrong period hPeriod frame.count)
    (smoothFiniteFrameProjectorCoefficients_idempotent
      period hPeriod frame metric)

theorem smoothGlobalCandidateAFiniteFrameRootCoefficients_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothFiniteFrameProjectorCoefficients
          period hPeriod frame geometry.plusMetric)
        (smoothGlobalCandidateAFiniteFrameRootCoefficients
          period hPeriod geometry frame) =
      smoothGlobalCandidateAFiniteFrameRootCoefficients
        period hPeriod geometry frame ∧
    smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients
          period hPeriod geometry frame)
        (smoothFiniteFrameProjectorCoefficients
          period hPeriod frame geometry.plusMetric) =
      smoothGlobalCandidateAFiniteFrameRootCoefficients
        period hPeriod geometry frame := by
  constructor
  · funext row column
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    have hCorner := globalCandidateAFiniteFrameRootMatrix_corner
      period hPeriod geometry frame point
    have hEntry := congrFun (congrFun hCorner.1 row) column
    simp only [smoothFiniteMatrixProduct,
      smoothFiniteFrameProjectorCoefficients,
      smoothGlobalCandidateAFiniteFrameRootCoefficients,
      smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
    simpa [Matrix.mul_apply, finiteFrameProjectorMatrixAt,
      finiteFrameEndomorphismMatrixAt,
      finiteFrameProjectorCoefficient_apply,
      globalCandidateAFiniteFrameRootCoefficient_apply] using hEntry
  · funext row column
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    have hCorner := globalCandidateAFiniteFrameRootMatrix_corner
      period hPeriod geometry frame point
    have hEntry := congrFun (congrFun hCorner.2 row) column
    simp only [smoothFiniteMatrixProduct,
      smoothFiniteFrameProjectorCoefficients,
      smoothGlobalCandidateAFiniteFrameRootCoefficients,
      smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
    simpa [Matrix.mul_apply, finiteFrameProjectorMatrixAt,
      finiteFrameEndomorphismMatrixAt,
      finiteFrameProjectorCoefficient_apply,
      globalCandidateAFiniteFrameRootCoefficient_apply] using hEntry

theorem strongGlobalCandidateAFiniteFrameRoot_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (strongFiniteFrameProjector
          period hPeriod frame geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRoot
          period hPeriod geometry frame) =
      strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∧
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (strongGlobalCandidateAFiniteFrameRoot
          period hPeriod geometry frame)
        (strongFiniteFrameProjector
          period hPeriod frame geometry.plusMetric) =
      strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame := by
  constructor
  · change strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (smoothFiniteMatrixToStrong period hPeriod frame.count
          (smoothFiniteFrameProjectorCoefficients
            period hPeriod frame geometry.plusMetric))
        (smoothFiniteMatrixToStrong period hPeriod frame.count
          (smoothGlobalCandidateAFiniteFrameRootCoefficients
            period hPeriod geometry frame)) =
      smoothFiniteMatrixToStrong period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients
          period hPeriod geometry frame)
    rw [strongFiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToStrong period hPeriod frame.count)
      (smoothGlobalCandidateAFiniteFrameRootCoefficients_corner
        period hPeriod geometry frame).1
  · change strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (smoothFiniteMatrixToStrong period hPeriod frame.count
          (smoothGlobalCandidateAFiniteFrameRootCoefficients
            period hPeriod geometry frame))
        (smoothFiniteMatrixToStrong period hPeriod frame.count
          (smoothFiniteFrameProjectorCoefficients
            period hPeriod frame geometry.plusMetric)) =
      smoothFiniteMatrixToStrong period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients
          period hPeriod geometry frame)
    rw [strongFiniteMatrixProduct_smooth]
    exact congrArg
      (smoothFiniteMatrixToStrong period hPeriod frame.count)
      (smoothGlobalCandidateAFiniteFrameRootCoefficients_corner
        period hPeriod geometry frame).2

def strongFiniteFrameCornerProjection
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    StrongFrameMatrix period hPeriod frame →L[Real]
      StrongFrameMatrix period hPeriod frame :=
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let projector := strongFiniteFrameProjector period hPeriod frame metric
  (product projector).comp (product.flip projector)

@[simp]
theorem strongFiniteFrameCornerProjection_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    strongFiniteFrameCornerProjection period hPeriod frame metric matrix =
      strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (strongFiniteFrameProjector period hPeriod frame metric)
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count matrix
          (strongFiniteFrameProjector period hPeriod frame metric)) :=
  rfl

theorem strongFiniteMatrixSandwich_idempotent
    (dimension : Nat)
    (projector matrix : StrongFiniteMatrix period hPeriod dimension)
    (hProjector : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension
          (strongFiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension projector
            (strongFiniteMatrixProduct
              (period := period) (hPeriod := hPeriod) dimension
              matrix projector)) projector) =
      strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := strongFiniteMatrixProduct_assoc period hPeriod dimension
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

theorem strongFiniteMatrixSandwich_left
    (dimension : Nat)
    (projector matrix : StrongFiniteMatrix period hPeriod dimension)
    (hProjector : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hMatrix : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) =
      matrix) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector matrix =
      matrix := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := strongFiniteMatrixProduct_assoc period hPeriod dimension
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

theorem strongFiniteMatrixSandwich_right
    (dimension : Nat)
    (projector matrix : StrongFiniteMatrix period hPeriod dimension)
    (hProjector : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hMatrix : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension matrix projector) =
      matrix) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension matrix projector =
      matrix := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := strongFiniteMatrixProduct_assoc period hPeriod dimension
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

theorem strongFiniteMatrixSandwich_product
    (dimension : Nat)
    (projector first second : StrongFiniteMatrix period hPeriod dimension)
    (hProjector : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        projector projector = projector)
    (hFirst : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first projector) =
      first)
    (hSecond : strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension second projector) =
      second) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension projector
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension
          (strongFiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension first second)
          projector) =
      strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first second := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  have hAssoc := strongFiniteMatrixProduct_assoc period hPeriod dimension
  have hLeft := strongFiniteMatrixSandwich_left
    period hPeriod dimension projector first hProjector hFirst
  have hRight := strongFiniteMatrixSandwich_right
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

theorem strongFiniteFrameCornerProjection_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    strongFiniteFrameCornerProjection period hPeriod frame metric
        (strongFiniteFrameCornerProjection period hPeriod frame metric matrix) =
      strongFiniteFrameCornerProjection period hPeriod frame metric matrix := by
  exact strongFiniteMatrixSandwich_idempotent period hPeriod frame.count
    (strongFiniteFrameProjector period hPeriod frame metric) matrix
    (strongFiniteFrameProjector_idempotent period hPeriod frame metric)

def strongFiniteFrameCornerSubmodule
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (StrongFrameMatrix period hPeriod frame) :=
  (strongFiniteFrameCornerProjection period hPeriod frame metric -
    ContinuousLinearMap.id Real
      (StrongFrameMatrix period hPeriod frame)).ker

abbrev StrongFiniteFrameCorner
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  strongFiniteFrameCornerSubmodule period hPeriod frame metric

theorem strongFiniteFrameCorner_mem_iff
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    matrix ∈ strongFiniteFrameCornerSubmodule period hPeriod frame metric ↔
      strongFiniteFrameCornerProjection period hPeriod frame metric matrix =
        matrix := by
  change strongFiniteFrameCornerProjection period hPeriod frame metric matrix -
      matrix = 0 ↔ _
  exact sub_eq_zero

theorem strongFiniteFrameCornerProjection_mem
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    strongFiniteFrameCornerProjection period hPeriod frame metric matrix ∈
      strongFiniteFrameCornerSubmodule period hPeriod frame metric := by
  rw [strongFiniteFrameCorner_mem_iff]
  exact strongFiniteFrameCornerProjection_idempotent
    period hPeriod frame metric matrix

theorem strongGlobalCandidateAFiniteFrameRoot_mem_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∈
      strongFiniteFrameCornerSubmodule
        period hPeriod frame geometry.plusMetric := by
  rw [strongFiniteFrameCorner_mem_iff]
  change strongFiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) frame.count
      (strongFiniteFrameProjector period hPeriod frame geometry.plusMetric)
      (strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame)
        (strongFiniteFrameProjector
          period hPeriod frame geometry.plusMetric)) =
    strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame
  rw [(strongGlobalCandidateAFiniteFrameRoot_corner
    period hPeriod geometry frame).2]
  exact (strongGlobalCandidateAFiniteFrameRoot_corner
    period hPeriod geometry frame).1

theorem strongFiniteFrameCornerSubmodule_isClosed
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IsClosed (strongFiniteFrameCornerSubmodule
      period hPeriod frame metric : Set (StrongFrameMatrix period hPeriod frame)) :=
  (strongFiniteFrameCornerProjection period hPeriod frame metric -
    ContinuousLinearMap.id Real
      (StrongFrameMatrix period hPeriod frame)).isClosed_ker

@[implicit_reducible]
def strongFiniteFrameCornerCompleteSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (StrongFiniteFrameCorner period hPeriod frame metric) := by
  letI : IsClosed
      (strongFiniteFrameCornerSubmodule period hPeriod frame metric :
        Set (StrongFrameMatrix period hPeriod frame)) :=
    strongFiniteFrameCornerSubmodule_isClosed period hPeriod frame metric
  exact IsClosed.completeSpace_coe


/-- Summary gate: the redundant strong coefficient algebra has an exact
closed projector corner containing the intrinsic Candidate-A root. -/
theorem global_candidate_a_strong_finite_frame_corner_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    IsClosed (strongFiniteFrameCornerSubmodule
      period hPeriod frame geometry.plusMetric :
        Set (StrongFrameMatrix period hPeriod frame)) ∧
      (∀ matrix : StrongFrameMatrix period hPeriod frame,
        strongFiniteFrameCornerProjection
            period hPeriod frame geometry.plusMetric
            (strongFiniteFrameCornerProjection
              period hPeriod frame geometry.plusMetric matrix) =
          strongFiniteFrameCornerProjection
            period hPeriod frame geometry.plusMetric matrix) ∧
      strongGlobalCandidateAFiniteFrameRoot period hPeriod geometry frame ∈
        strongFiniteFrameCornerSubmodule
          period hPeriod frame geometry.plusMetric := by
  exact ⟨strongFiniteFrameCornerSubmodule_isClosed
      period hPeriod frame geometry.plusMetric,
    strongFiniteFrameCornerProjection_idempotent
      period hPeriod frame geometry.plusMetric,
    strongGlobalCandidateAFiniteFrameRoot_mem_corner
      period hPeriod geometry frame⟩

end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
end JanusFormal


