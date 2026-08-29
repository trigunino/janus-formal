import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D

/-!
# Intrinsic Sylvester regularity on the strong finite-frame corner

The redundant finite-frame matrix corner is identified pointwise with
intrinsic tangent endomorphisms.  Intrinsic Sylvester regularity therefore
transports to the matrix corner and then, through the established smooth
finite-matrix lift, to the complete strong corner.  This is a regular-stratum
statement; no global frame and no extra physical axiom are introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
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
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev FrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  FiniteFrameMatrix period hPeriod frame

private abbrev StrongFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  StrongFiniteMatrix period hPeriod frame.count

private abbrev EndAt (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    TangentFiber period hPeriod point

@[reducible] local instance frameMatrixNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) :
    NormedAddCommGroup (FrameMatrix period hPeriod frame) :=
  Matrix.normedAddCommGroup

local instance frameMatrixAddCommGroup
    (frame : SmoothD8Frame period hPeriod) :
    AddCommGroup (FrameMatrix period hPeriod frame) :=
  (frameMatrixNormedAddCommGroup period hPeriod frame).toAddCommGroup

local instance frameMatrixPseudoMetricSpace
    (frame : SmoothD8Frame period hPeriod) :
    PseudoMetricSpace (FrameMatrix period hPeriod frame) :=
  (frameMatrixNormedAddCommGroup
    period hPeriod frame).toPseudoMetricSpace

local instance frameMatrixUniformSpace
    (frame : SmoothD8Frame period hPeriod) :
    UniformSpace (FrameMatrix period hPeriod frame) :=
  (frameMatrixPseudoMetricSpace
    period hPeriod frame).toUniformSpace

local instance frameMatrixTopologicalSpace
    (frame : SmoothD8Frame period hPeriod) :
    TopologicalSpace (FrameMatrix period hPeriod frame) :=
  (frameMatrixUniformSpace
    period hPeriod frame).toTopologicalSpace

@[reducible] local instance frameMatrixNormedSpace
    (frame : SmoothD8Frame period hPeriod) :
    NormedSpace Real (FrameMatrix period hPeriod frame) :=
  Matrix.normedSpace

local instance frameMatrixModule
    (frame : SmoothD8Frame period hPeriod) :
    Module Real (FrameMatrix period hPeriod frame) :=
  (frameMatrixNormedSpace period hPeriod frame).toModule

local instance frameMatrixOperatorNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) :
    NormedAddCommGroup
      (FrameMatrix period hPeriod frame →L[Real]
        FrameMatrix period hPeriod frame) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance frameMatrixOperatorNormedSpace
    (frame : SmoothD8Frame period hPeriod) :
    NormedSpace Real
      (FrameMatrix period hPeriod frame →L[Real]
        FrameMatrix period hPeriod frame) :=
  ContinuousLinearMap.toNormedSpace

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

/-! ## Intrinsic and pointwise corner algebra -/

/-- Intrinsic Sylvester operator at one quotient point. -/
def intrinsicCandidateASylvesterAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    EndAt period hPeriod point →ₗ[Real] EndAt period hPeriod point where
  toFun variation :=
    (geometry.rootAt point).comp variation +
      variation.comp (geometry.rootAt point)
  map_add' first second := by
    ext vector
    simp
    abel
  map_smul' scalar variation := by
    ext vector
    simp

@[simp]
theorem intrinsicCandidateASylvesterAt_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (variation : EndAt period hPeriod point) :
    intrinsicCandidateASylvesterAt period hPeriod geometry point variation =
      (geometry.rootAt point).comp variation +
        variation.comp (geometry.rootAt point) :=
  rfl

/-- Intrinsic rank-one endomorphism associated with two redundant-frame
indices. -/
def finiteFrameRankOneAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (row column : Fin frame.count) :
    EndAt period hPeriod point :=
  (generalMetricFiniteFrameCoefficientAt
    period hPeriod frame metric point column).smulRight
      (frame.vectorAt point row)

/-- The pointwise decoder as a genuine linear map in the redundant matrix. -/
def finiteFrameMatrixDecodeLinearAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FrameMatrix period hPeriod frame →ₗ[Real] EndAt period hPeriod point :=
  ∑ row : Fin frame.count,
    ∑ column : Fin frame.count,
      LinearMap.smulRight
        (finiteMatrixEntryLinearMap frame.count row column)
        (finiteFrameRankOneAt period hPeriod frame metric point row column)

/-- Decode an arbitrary redundant matrix into an intrinsic endomorphism. -/
def finiteFrameMatrixDecodeAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    EndAt period hPeriod point :=
  finiteFrameMatrixDecodeLinearAt period hPeriod frame metric point matrix

@[simp]
theorem finiteFrameMatrixDecodeLinearAt_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameMatrixDecodeLinearAt period hPeriod frame metric point matrix =
      finiteFrameMatrixDecodeAt period hPeriod frame metric point matrix :=
  rfl

@[simp]
theorem finiteFrameMatrixDecodeAt_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame)
    (vector : TangentFiber period hPeriod point) :
    finiteFrameMatrixDecodeAt period hPeriod frame metric point matrix vector =
      ∑ row : Fin frame.count,
        (∑ column : Fin frame.count,
          matrix row column *
            generalMetricFiniteFrameCoefficientAt
              period hPeriod frame metric point column vector) •
          frame.vectorAt point row := by
  simp [finiteFrameMatrixDecodeAt, finiteFrameMatrixDecodeLinearAt,
    finiteFrameRankOneAt, finiteMatrixEntryLinearMap,
    ContinuousLinearMap.smulRight_apply, Finset.sum_smul, smul_smul]

/-- Encoding after decoding is exactly the projector sandwich. -/
theorem finiteFrameEndomorphismMatrixAt_decode
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
        (finiteFrameMatrixDecodeAt
          period hPeriod frame metric point matrix) =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point *
        matrix *
          finiteFrameProjectorMatrixAt
            period hPeriod frame metric point := by
  ext outputRow outputColumn
  simp only [finiteFrameEndomorphismMatrixAt_apply,
    finiteFrameMatrixDecodeAt_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_mul]
  simp only [finiteFrameProjectorMatrixAt,
    finiteFrameEndomorphismMatrixAt_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inputColumn _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro inputRow _
  ring

/-- Decoding is a left inverse of the faithful endomorphism encoding. -/
theorem finiteFrameMatrixDecodeAt_encode
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : EndAt period hPeriod point) :
    finiteFrameMatrixDecodeAt period hPeriod frame metric point
        (finiteFrameEndomorphismMatrixAt
          period hPeriod frame metric point endomorphism) = endomorphism := by
  apply finiteFrameEndomorphismMatrixAt_injective
    period hPeriod frame metric point
  rw [finiteFrameEndomorphismMatrixAt_decode]
  rw [mul_assoc]
  rw [finiteFrameEndomorphismMatrixAt_right_projector]
  exact finiteFrameEndomorphismMatrixAt_left_projector
    period hPeriod frame metric point endomorphism

/-- Every projector-corner matrix is exactly the encoding of its intrinsic
decode. -/
theorem finiteFrameEndomorphismMatrixAt_decode_of_corner
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame)
    (hCorner :
      finiteFrameProjectorMatrixAt period hPeriod frame metric point * matrix *
          finiteFrameProjectorMatrixAt period hPeriod frame metric point =
        matrix) :
    finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
        (finiteFrameMatrixDecodeAt
          period hPeriod frame metric point matrix) = matrix := by
  rw [finiteFrameEndomorphismMatrixAt_decode, hCorner]

/-- Intrinsic composition is transported exactly by the redundant encoding. -/
theorem finiteFrameIntrinsicSylvester_encode
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (variation : EndAt period hPeriod point) :
    finiteFrameEndomorphismMatrixAt period hPeriod frame
        geometry.plusMetric point
        (intrinsicCandidateASylvesterAt
          period hPeriod geometry point variation) =
      globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point *
        finiteFrameEndomorphismMatrixAt period hPeriod frame
          geometry.plusMetric point variation +
      finiteFrameEndomorphismMatrixAt period hPeriod frame
          geometry.plusMetric point variation *
        globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point := by
  rw [intrinsicCandidateASylvesterAt_apply]
  rw [show finiteFrameEndomorphismMatrixAt period hPeriod frame
        geometry.plusMetric point
        ((geometry.rootAt point).comp variation +
          variation.comp (geometry.rootAt point)) =
      finiteFrameEndomorphismMatrixAt period hPeriod frame
          geometry.plusMetric point
          ((geometry.rootAt point).comp variation) +
        finiteFrameEndomorphismMatrixAt period hPeriod frame
          geometry.plusMetric point
          (variation.comp (geometry.rootAt point)) by
    ext row column
    simp [finiteFrameEndomorphismMatrixAt]]
  rw [finiteFrameEndomorphismMatrixAt_comp,
    finiteFrameEndomorphismMatrixAt_comp]
  rw [globalCandidateAFiniteFrameRootMatrix_apply]

/-- Pointwise projector sandwich on the redundant matrix algebra. -/
def finiteFrameCornerProjectionLinearAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FrameMatrix period hPeriod frame →ₗ[Real]
      FrameMatrix period hPeriod frame where
  toFun matrix :=
    finiteFrameProjectorMatrixAt period hPeriod frame metric point * matrix *
      finiteFrameProjectorMatrixAt period hPeriod frame metric point
  map_add' first second := by
    simp [mul_add, add_mul]
  map_smul' scalar matrix := by
    calc
      finiteFrameProjectorMatrixAt period hPeriod frame metric point *
            (scalar • matrix) *
          finiteFrameProjectorMatrixAt period hPeriod frame metric point =
        (scalar •
          (finiteFrameProjectorMatrixAt period hPeriod frame metric point *
            matrix)) *
          finiteFrameProjectorMatrixAt period hPeriod frame metric point := by
        rw [Matrix.mul_smul]
      _ = scalar •
          (finiteFrameProjectorMatrixAt period hPeriod frame metric point *
            matrix * finiteFrameProjectorMatrixAt
              period hPeriod frame metric point) := by
        rw [Matrix.smul_mul]

def finiteFrameCornerProjectionAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FrameMatrix period hPeriod frame →L[Real]
      FrameMatrix period hPeriod frame :=
  LinearMap.toContinuousLinearMap
    (finiteFrameCornerProjectionLinearAt period hPeriod frame metric point)

@[simp]
theorem finiteFrameCornerProjectionAt_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameCornerProjectionAt period hPeriod frame metric point matrix =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point * matrix *
        finiteFrameProjectorMatrixAt period hPeriod frame metric point :=
  rfl

theorem finiteFrameCornerProjectionAt_idempotent
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameCornerProjectionAt period hPeriod frame metric point
        (finiteFrameCornerProjectionAt
          period hPeriod frame metric point matrix) =
      finiteFrameCornerProjectionAt period hPeriod frame metric point matrix := by
  let projector := finiteFrameProjectorMatrixAt
    period hPeriod frame metric point
  have hProjector : projector * projector = projector :=
    finiteFrameProjectorMatrixAt_idempotent
      period hPeriod frame metric point
  change projector * (projector * matrix * projector) * projector =
    projector * matrix * projector
  calc
    projector * (projector * matrix * projector) * projector =
        (projector * projector) * matrix * (projector * projector) := by
      simp only [mul_assoc]
    _ = projector * matrix * projector := by rw [hProjector]

theorem finiteFrameCornerProjectionAt_encode
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (endomorphism : EndAt period hPeriod point) :
    finiteFrameCornerProjectionAt period hPeriod frame metric point
        (finiteFrameEndomorphismMatrixAt
          period hPeriod frame metric point endomorphism) =
      finiteFrameEndomorphismMatrixAt
        period hPeriod frame metric point endomorphism := by
  rw [finiteFrameCornerProjectionAt_apply, mul_assoc]
  rw [finiteFrameEndomorphismMatrixAt_right_projector]
  exact finiteFrameEndomorphismMatrixAt_left_projector
    period hPeriod frame metric point endomorphism

theorem finiteFrameMatrixDecodeAt_cornerProjection
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameMatrixDecodeAt period hPeriod frame metric point
        (finiteFrameCornerProjectionAt
          period hPeriod frame metric point matrix) =
      finiteFrameMatrixDecodeAt period hPeriod frame metric point matrix := by
  apply finiteFrameEndomorphismMatrixAt_injective
    period hPeriod frame metric point
  rw [finiteFrameEndomorphismMatrixAt_decode,
    finiteFrameEndomorphismMatrixAt_decode]
  exact finiteFrameCornerProjectionAt_idempotent
    period hPeriod frame metric point matrix

/-- Sylvester on the matrix corner and the identity on its complementary
projector summand. -/
def finiteFrameExtendedSylvesterLinearAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FrameMatrix period hPeriod frame →ₗ[Real]
      FrameMatrix period hPeriod frame where
  toFun matrix :=
    let corner := finiteFrameCornerProjectionAt
      period hPeriod frame geometry.plusMetric point matrix
    globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point * corner +
      corner * globalCandidateAFiniteFrameRootMatrix
          period hPeriod geometry frame point +
      (matrix - corner)
  map_add' first second := by
    simp [mul_add, add_mul]
    abel
  map_smul' scalar matrix := by
    rw [(finiteFrameCornerProjectionAt period hPeriod frame
      geometry.plusMetric point).map_smul]
    change
      globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point *
          (scalar • finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point matrix) +
        (scalar • finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point matrix) *
          globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point +
        (scalar • matrix - scalar •
          finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point matrix) =
      scalar •
        (globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point *
            finiteFrameCornerProjectionAt period hPeriod frame
              geometry.plusMetric point matrix +
          finiteFrameCornerProjectionAt period hPeriod frame
                geometry.plusMetric point matrix *
            globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point +
          (matrix - finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point matrix))
    rw [Matrix.mul_smul, Matrix.smul_mul]
    module

def finiteFrameExtendedSylvesterAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    FrameMatrix period hPeriod frame →L[Real]
      FrameMatrix period hPeriod frame :=
  LinearMap.toContinuousLinearMap
    (finiteFrameExtendedSylvesterLinearAt
      period hPeriod geometry frame point)

@[simp]
theorem finiteFrameExtendedSylvesterAt_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameExtendedSylvesterAt
        period hPeriod geometry frame point matrix =
      let corner := finiteFrameCornerProjectionAt
        period hPeriod frame geometry.plusMetric point matrix
      globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point * corner +
        corner * globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point +
        (matrix - corner) :=
  rfl

theorem finiteFrameExtendedSylvesterAt_decode
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        (finiteFrameExtendedSylvesterAt
          period hPeriod geometry frame point matrix) =
      intrinsicCandidateASylvesterAt period hPeriod geometry point
        (finiteFrameMatrixDecodeAt
          period hPeriod frame geometry.plusMetric point matrix) := by
  let decode := finiteFrameMatrixDecodeLinearAt
    period hPeriod frame geometry.plusMetric point
  let corner := finiteFrameCornerProjectionAt
    period hPeriod frame geometry.plusMetric point matrix
  have hCornerEncode :
      finiteFrameEndomorphismMatrixAt period hPeriod frame
          geometry.plusMetric point
          (finiteFrameMatrixDecodeAt
            period hPeriod frame geometry.plusMetric point matrix) = corner := by
    exact finiteFrameEndomorphismMatrixAt_decode
      period hPeriod frame geometry.plusMetric point matrix
  have hSylvesterEncode := finiteFrameIntrinsicSylvester_encode
    period hPeriod geometry frame point
      (finiteFrameMatrixDecodeAt
        period hPeriod frame geometry.plusMetric point matrix)
  rw [hCornerEncode] at hSylvesterEncode
  change decode
      (globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point * corner +
        corner * globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point +
        (matrix - corner)) = _
  rw [← hSylvesterEncode]
  rw [decode.map_add, decode.map_sub]
  dsimp [decode]
  rw [finiteFrameMatrixDecodeAt_encode]
  change _ +
      (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        matrix -
      finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        corner) = _
  rw [finiteFrameMatrixDecodeAt_cornerProjection]
  abel

theorem finiteFrameExtendedSylvesterAt_bijective
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (point : EffectiveQuotient period hPeriod) :
    Function.Bijective
      (finiteFrameExtendedSylvesterAt
        period hPeriod geometry frame point) := by
  constructor
  · intro first second hEqual
    have hDecoded :
        intrinsicCandidateASylvesterAt period hPeriod geometry point
            (finiteFrameMatrixDecodeAt period hPeriod frame
              geometry.plusMetric point first) =
          intrinsicCandidateASylvesterAt period hPeriod geometry point
            (finiteFrameMatrixDecodeAt period hPeriod frame
              geometry.plusMetric point second) := by
      rw [← finiteFrameExtendedSylvesterAt_decode,
        ← finiteFrameExtendedSylvesterAt_decode, hEqual]
    have hDecode := (hRegular point).1 hDecoded
    have hCorner :
        finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point first =
          finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point second := by
      change
        finiteFrameProjectorMatrixAt period hPeriod frame
              geometry.plusMetric point * first *
            finiteFrameProjectorMatrixAt period hPeriod frame
              geometry.plusMetric point =
          finiteFrameProjectorMatrixAt period hPeriod frame
              geometry.plusMetric point * second *
            finiteFrameProjectorMatrixAt period hPeriod frame
              geometry.plusMetric point
      rw [← finiteFrameEndomorphismMatrixAt_decode
          period hPeriod frame geometry.plusMetric point first,
        ← finiteFrameEndomorphismMatrixAt_decode
          period hPeriod frame geometry.plusMetric point second,
        hDecode]
    let firstCorner := finiteFrameCornerProjectionAt period hPeriod frame
      geometry.plusMetric point first
    let secondCorner := finiteFrameCornerProjectionAt period hPeriod frame
      geometry.plusMetric point second
    have hCorner' : firstCorner = secondCorner := hCorner
    have hComplement : first - firstCorner = second - secondCorner := by
      have hEqual' := hEqual
      change
        globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point * firstCorner +
            firstCorner * globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point +
            (first - firstCorner) =
          globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point * secondCorner +
            secondCorner * globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point +
            (second - secondCorner) at hEqual'
      rw [hCorner'] at hEqual'
      rw [hCorner']
      exact add_left_cancel hEqual'
    calc
      first = firstCorner + (first - firstCorner) := by abel
      _ = secondCorner + (second - secondCorner) := by
        calc
          firstCorner + (first - firstCorner) =
              secondCorner + (first - firstCorner) := by rw [hCorner']
          _ = secondCorner + (second - secondCorner) := by rw [hComplement]
      _ = second := by abel
  · intro target
    obtain ⟨variation, hVariation⟩ := (hRegular point).2
      (finiteFrameMatrixDecodeAt period hPeriod frame
        geometry.plusMetric point target)
    let encoded := finiteFrameEndomorphismMatrixAt period hPeriod frame
      geometry.plusMetric point variation
    let targetCorner := finiteFrameCornerProjectionAt period hPeriod frame
      geometry.plusMetric point target
    let source := encoded + (target - targetCorner)
    refine ⟨source, ?_⟩
    have hEncodedCorner :
        finiteFrameCornerProjectionAt period hPeriod frame
          geometry.plusMetric point encoded = encoded :=
      finiteFrameCornerProjectionAt_encode
        period hPeriod frame geometry.plusMetric point variation
    have hComplementCorner :
        finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point (target - targetCorner) = 0 := by
      rw [(finiteFrameCornerProjectionAt
        period hPeriod frame geometry.plusMetric point).map_sub]
      rw [finiteFrameCornerProjectionAt_idempotent]
      exact sub_self targetCorner
    have hSourceCorner :
        finiteFrameCornerProjectionAt period hPeriod frame
          geometry.plusMetric point source = encoded := by
      change finiteFrameCornerProjectionAt period hPeriod frame
        geometry.plusMetric point (encoded + (target - targetCorner)) = encoded
      rw [(finiteFrameCornerProjectionAt
        period hPeriod frame geometry.plusMetric point).map_add]
      rw [hEncodedCorner, hComplementCorner, add_zero]
    have hSylvester :
        globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point * encoded +
            encoded * globalCandidateAFiniteFrameRootMatrix
              period hPeriod geometry frame point = targetCorner := by
      rw [← finiteFrameIntrinsicSylvester_encode
        period hPeriod geometry frame point variation]
      rw [hVariation]
      exact finiteFrameEndomorphismMatrixAt_decode
        period hPeriod frame geometry.plusMetric point target
    change
      globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point *
          finiteFrameCornerProjectionAt period hPeriod frame
            geometry.plusMetric point source +
        finiteFrameCornerProjectionAt period hPeriod frame
              geometry.plusMetric point source *
          globalCandidateAFiniteFrameRootMatrix
            period hPeriod geometry frame point +
        (source - finiteFrameCornerProjectionAt period hPeriod frame
          geometry.plusMetric point source) = target
    rw [hSourceCorner, hSylvester]
    change targetCorner +
      (encoded + (target - targetCorner) - encoded) = target
    abel

/-! ## Smooth family and strong lift -/

def smoothRealConstant
    (value : Real) : SmoothQuotientField period hPeriod Real where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

def smoothScalarFieldTripleMul
    (first second third : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real :=
  smoothScalarFieldMul period hPeriod first
    (smoothScalarFieldMul period hPeriod second third)

@[simp]
theorem smoothScalarFieldTripleMul_apply
    (first second third : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    smoothScalarFieldTripleMul period hPeriod first second third point =
      first point * second point * third point := by
  simp [smoothScalarFieldTripleMul, smoothScalarFieldMul_apply, mul_assoc]

theorem finiteFrameCornerProjectionAt_unit_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (inputRow inputColumn outputRow outputColumn : Fin frame.count) :
    finiteFrameCornerProjectionAt period hPeriod frame geometry.plusMetric point
        (finiteMatrixUnit frame.count inputRow inputColumn)
        outputRow outputColumn =
      finiteFrameProjectorMatrixAt period hPeriod frame geometry.plusMetric point
          outputRow inputRow *
      finiteFrameProjectorMatrixAt period hPeriod frame geometry.plusMetric point
          inputColumn outputColumn := by
  classical
  simp only [finiteFrameCornerProjectionAt_apply, finiteMatrixUnit,
    Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single inputColumn]
  · simp
  · intro column _ hColumn
    simp [Ne.symm hColumn]
  · simp

/-- Smooth coordinates of the extended pointwise Sylvester family. -/
def finiteFrameExtendedSylvesterCoefficient
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (outputRow outputColumn inputRow inputColumn : Fin frame.count) :
    SmoothQuotientField period hPeriod Real :=
  (∑ middle : Fin frame.count,
      smoothScalarFieldTripleMul period hPeriod
        (globalCandidateAFiniteFrameRootCoefficient
          period hPeriod geometry frame outputRow middle)
        (finiteFrameProjectorCoefficient
          period hPeriod frame geometry.plusMetric middle inputRow)
        (finiteFrameProjectorCoefficient
          period hPeriod frame geometry.plusMetric inputColumn outputColumn)) +
    (∑ middle : Fin frame.count,
      smoothScalarFieldTripleMul period hPeriod
        (finiteFrameProjectorCoefficient
          period hPeriod frame geometry.plusMetric outputRow inputRow)
        (finiteFrameProjectorCoefficient
          period hPeriod frame geometry.plusMetric inputColumn middle)
        (globalCandidateAFiniteFrameRootCoefficient
          period hPeriod geometry frame middle outputColumn)) +
    smoothRealConstant period hPeriod
      (finiteMatrixUnit frame.count inputRow inputColumn
        outputRow outputColumn) -
    smoothScalarFieldMul period hPeriod
      (finiteFrameProjectorCoefficient
        period hPeriod frame geometry.plusMetric outputRow inputRow)
      (finiteFrameProjectorCoefficient
        period hPeriod frame geometry.plusMetric inputColumn outputColumn)

theorem finiteFrameExtendedSylvesterCoefficient_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (outputRow outputColumn inputRow inputColumn : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameExtendedSylvesterCoefficient period hPeriod geometry frame
        outputRow outputColumn inputRow inputColumn point =
      finiteFrameExtendedSylvesterAt period hPeriod geometry frame point
          (finiteMatrixUnit frame.count inputRow inputColumn)
        outputRow outputColumn := by
  rw [finiteFrameExtendedSylvesterAt_apply]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  simp_rw [finiteFrameCornerProjectionAt_unit_apply]
  simp [finiteFrameExtendedSylvesterCoefficient,
    smoothScalarFieldTripleMul, smoothScalarFieldMul, smoothRealConstant,
    globalCandidateAFiniteFrameRootMatrix,
    finiteFrameProjectorMatrixAt, finiteFrameEndomorphismMatrixAt,
    finiteFrameProjectorCoefficient_apply,
    globalCandidateAFiniteFrameRootCoefficient_apply]
  simp only [mul_assoc]
  ring

/-- Smooth matrix image of one standard input matrix unit. -/
def finiteFrameExtendedSylvesterUnitImage
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (inputRow inputColumn : Fin frame.count) :
    SmoothQuotientField period hPeriod
      (FrameMatrix period hPeriod frame) where
  toFun := fun point outputRow outputColumn =>
    finiteFrameExtendedSylvesterCoefficient period hPeriod geometry frame
      outputRow outputColumn inputRow inputColumn point
  contMDiff_toFun := by
    have hExpansion :
        ContMDiff coverModelWithCorners
          (modelWithCornersSelf Real
            (FrameMatrix period hPeriod frame)) ∞
          (fun point =>
            ∑ outputRow : Fin frame.count,
              ∑ outputColumn : Fin frame.count,
                finiteFrameExtendedSylvesterCoefficient
                    period hPeriod geometry frame outputRow outputColumn
                      inputRow inputColumn point •
                  Matrix.single outputRow outputColumn (1 : Real)) := by
      apply ContMDiff.sum
      intro outputRow _
      apply ContMDiff.sum
      intro outputColumn _
      exact (finiteFrameExtendedSylvesterCoefficient
        period hPeriod geometry frame outputRow outputColumn
          inputRow inputColumn).contMDiff_toFun.smul contMDiff_const
    exact hExpansion.congr fun point => by
      simpa using
        (Matrix.matrix_eq_sum_single
          (fun outputRow outputColumn =>
            finiteFrameExtendedSylvesterCoefficient
              period hPeriod geometry frame outputRow outputColumn
                inputRow inputColumn point))

theorem finiteFrameExtendedSylvesterUnitImage_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (inputRow inputColumn : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameExtendedSylvesterUnitImage period hPeriod geometry frame
        inputRow inputColumn point =
      finiteFrameExtendedSylvesterAt period hPeriod geometry frame point
        (finiteMatrixUnit frame.count inputRow inputColumn) := by
  ext outputRow outputColumn
  exact finiteFrameExtendedSylvesterCoefficient_apply
    period hPeriod geometry frame outputRow outputColumn
      inputRow inputColumn point

/-- Globally smooth family whose value is the extended Sylvester operator. -/
def globalCandidateAFiniteFrameExtendedSylvesterField
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    SmoothQuotientField period hPeriod
      (FrameMatrix period hPeriod frame →L[Real]
        FrameMatrix period hPeriod frame) where
  toFun := fun point =>
    ∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
      (finiteMatrixEntryCLM frame.count inputRow inputColumn).smulRight
        (finiteFrameExtendedSylvesterUnitImage
          period hPeriod geometry frame inputRow inputColumn point)
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro inputRow _
    apply ContMDiff.sum
    intro inputColumn _
    intro anchor
    exact (contDiff_const.smulRight contDiff_id).comp_contMDiffAt
      ((finiteFrameExtendedSylvesterUnitImage
        period hPeriod geometry frame inputRow inputColumn).contMDiff_toFun
          anchor)

@[simp]
theorem globalCandidateAFiniteFrameExtendedSylvesterField_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalCandidateAFiniteFrameExtendedSylvesterField
        period hPeriod geometry frame point =
      finiteFrameExtendedSylvesterAt
        period hPeriod geometry frame point := by
  apply ContinuousLinearMap.ext
  intro matrix
  let evaluation :
      (FrameMatrix period hPeriod frame →L[Real]
        FrameMatrix period hPeriod frame) →+
          FrameMatrix period hPeriod frame :=
    { toFun := fun operator => operator matrix
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change evaluation
      (∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
        (finiteMatrixEntryCLM frame.count inputRow inputColumn).smulRight
          (finiteFrameExtendedSylvesterUnitImage
            period hPeriod geometry frame inputRow inputColumn point)) = _
  have hEvaluation :
      evaluation
          (∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
            (finiteMatrixEntryCLM frame.count inputRow inputColumn).smulRight
              (finiteFrameExtendedSylvesterUnitImage
                period hPeriod geometry frame inputRow inputColumn point)) =
        ∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
          matrix inputRow inputColumn •
            finiteFrameExtendedSylvesterUnitImage
              period hPeriod geometry frame inputRow inputColumn point := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro inputRow _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro inputColumn _
    rfl
  rw [hEvaluation]
  simp_rw [finiteFrameExtendedSylvesterUnitImage_apply]
  calc
    (∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
        matrix inputRow inputColumn •
          finiteFrameExtendedSylvesterAt period hPeriod geometry frame point
            (finiteMatrixUnit frame.count inputRow inputColumn)) =
      finiteFrameExtendedSylvesterAt period hPeriod geometry frame point
        (∑ inputRow : Fin frame.count, ∑ inputColumn : Fin frame.count,
          matrix inputRow inputColumn •
            finiteMatrixUnit frame.count inputRow inputColumn) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro inputRow _
      rw [map_sum]
      simp
    _ = finiteFrameExtendedSylvesterAt
        period hPeriod geometry frame point matrix := by
      rw [finiteMatrix_eq_sum_units]

theorem globalCandidateAFiniteFrameExtendedSylvesterField_bijective
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (point : EffectiveQuotient period hPeriod) :
    Function.Bijective
      (globalCandidateAFiniteFrameExtendedSylvesterField
        period hPeriod geometry frame point) := by
  rw [globalCandidateAFiniteFrameExtendedSylvesterField_apply]
  exact finiteFrameExtendedSylvesterAt_bijective
    period hPeriod geometry frame hRegular point

/-- Bounded ambient strong equivalence obtained from intrinsic pointwise
Sylvester regularity. -/
def strongFiniteFrameExtendedSylvesterEquiv
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    StrongFrameMatrix period hPeriod frame ≃L[Real]
      StrongFrameMatrix period hPeriod frame :=
  strongFiniteMatrixOperatorEquiv period hPeriod frame.count
    (globalCandidateAFiniteFrameExtendedSylvesterField
      period hPeriod geometry frame)
    (globalCandidateAFiniteFrameExtendedSylvesterField_bijective
      period hPeriod geometry frame hRegular)

theorem smoothFiniteMatrixValue_add
    (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod dimension (first + second) point =
      smoothFiniteMatrixValue period hPeriod dimension first point +
        smoothFiniteMatrixValue period hPeriod dimension second point :=
  rfl

theorem smoothFiniteMatrixValue_sub
    (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod dimension (first - second) point =
      smoothFiniteMatrixValue period hPeriod dimension first point -
        smoothFiniteMatrixValue period hPeriod dimension second point :=
  rfl

theorem smoothFiniteMatrixProduct_value
    (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod dimension
        (smoothFiniteMatrixProduct period hPeriod dimension first second) point =
      smoothFiniteMatrixValue period hPeriod dimension first point *
        smoothFiniteMatrixValue period hPeriod dimension second point := by
  ext row column
  simp [smoothFiniteMatrixValue, smoothFiniteMatrixProduct,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    Matrix.mul_apply]

theorem smoothFiniteFrameProjectorCoefficients_value
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod frame.count
        (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric) point =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point := by
  ext row column
  exact finiteFrameProjectorCoefficient_apply
    period hPeriod frame metric row column point

theorem smoothGlobalCandidateAFiniteFrameRootCoefficients_value
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients
          period hPeriod geometry frame) point =
      globalCandidateAFiniteFrameRootMatrix
        period hPeriod geometry frame point := by
  ext row column
  rfl

def smoothFiniteFrameCornerProjectionApply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count) :
    SmoothFiniteMatrix period hPeriod frame.count :=
  smoothFiniteMatrixProduct period hPeriod frame.count
    (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric)
    (smoothFiniteMatrixProduct period hPeriod frame.count variation
      (smoothFiniteFrameProjectorCoefficients period hPeriod frame metric))

theorem smoothFiniteFrameCornerProjectionApply_value
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod frame.count
        (smoothFiniteFrameCornerProjectionApply
          period hPeriod frame metric variation) point =
      finiteFrameCornerProjectionAt period hPeriod frame metric point
        (smoothFiniteMatrixValue
          period hPeriod frame.count variation point) := by
  rw [smoothFiniteFrameCornerProjectionApply]
  rw [smoothFiniteMatrixProduct_value, smoothFiniteMatrixProduct_value]
  rw [smoothFiniteFrameProjectorCoefficients_value]
  rw [finiteFrameCornerProjectionAt_apply, Matrix.mul_assoc]

def smoothFiniteFrameExtendedSylvesterApply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count) :
    SmoothFiniteMatrix period hPeriod frame.count :=
  let corner := smoothFiniteFrameCornerProjectionApply
    period hPeriod frame geometry.plusMetric variation
  smoothFiniteMatrixProduct period hPeriod frame.count
      (smoothGlobalCandidateAFiniteFrameRootCoefficients
        period hPeriod geometry frame) corner +
    smoothFiniteMatrixProduct period hPeriod frame.count corner
      (smoothGlobalCandidateAFiniteFrameRootCoefficients
        period hPeriod geometry frame) +
    (variation - corner)

theorem smoothFiniteFrameExtendedSylvesterApply_value
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count)
    (point : EffectiveQuotient period hPeriod) :
    smoothFiniteMatrixValue period hPeriod frame.count
        (smoothFiniteFrameExtendedSylvesterApply
          period hPeriod geometry frame variation) point =
      finiteFrameExtendedSylvesterAt period hPeriod geometry frame point
        (smoothFiniteMatrixValue
          period hPeriod frame.count variation point) := by
  rw [smoothFiniteFrameExtendedSylvesterApply]
  rw [smoothFiniteMatrixValue_add, smoothFiniteMatrixValue_add,
    smoothFiniteMatrixValue_sub]
  rw [smoothFiniteMatrixProduct_value, smoothFiniteMatrixProduct_value]
  rw [smoothGlobalCandidateAFiniteFrameRootCoefficients_value]
  rw [smoothFiniteFrameCornerProjectionApply_value]
  rfl

theorem smoothFiniteMatrixOperatorApply_extended
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count) :
    smoothFiniteMatrixOperatorApply period hPeriod frame.count
        (globalCandidateAFiniteFrameExtendedSylvesterField
          period hPeriod geometry frame) variation =
      smoothFiniteFrameExtendedSylvesterApply
        period hPeriod geometry frame variation := by
  funext row column
  apply SmoothQuotientField.ext
  intro point
  have hGeneric := smoothFiniteMatrixOperatorApply_value
    period hPeriod frame.count
      (globalCandidateAFiniteFrameExtendedSylvesterField
        period hPeriod geometry frame) variation point
  rw [globalCandidateAFiniteFrameExtendedSylvesterField_apply] at hGeneric
  have hExplicit := smoothFiniteFrameExtendedSylvesterApply_value
    period hPeriod geometry frame variation point
  exact congrArg (fun matrix : FrameMatrix period hPeriod frame =>
    matrix row column) (hGeneric.trans hExplicit.symm)

/-- Strong realization of the extended Sylvester family. -/
def strongFiniteFrameExtendedSylvester
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StrongFrameMatrix period hPeriod frame →L[Real]
      StrongFrameMatrix period hPeriod frame :=
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := strongFiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := strongGlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  (product root).comp corner +
    (product.flip root).comp corner +
    (ContinuousLinearMap.id Real
      (StrongFrameMatrix period hPeriod frame) - corner)

@[simp]
theorem strongFiniteFrameExtendedSylvester_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame matrix =
      let corner := strongFiniteFrameCornerProjection
        period hPeriod frame geometry.plusMetric matrix
      strongFiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count
            (strongGlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) corner +
        strongFiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count corner
            (strongGlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) +
        (matrix - corner) :=
  rfl

end


end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
end JanusFormal
