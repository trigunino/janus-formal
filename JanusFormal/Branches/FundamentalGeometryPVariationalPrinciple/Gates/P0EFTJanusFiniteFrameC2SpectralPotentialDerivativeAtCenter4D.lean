import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedRelativeC2TargetDerivativeAtCenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2SpectralInteraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

/-! # Derivative of the finite-frame spectral potential at the center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev FrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  FiniteFrameMatrix period hPeriod frame

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
@[reducible] local instance (frame : SmoothD8Frame period hPeriod) :
    NormedAddCommGroup (FrameMatrix period hPeriod frame) :=
  Matrix.normedAddCommGroup
@[reducible] local instance (frame : SmoothD8Frame period hPeriod) :
    NormedSpace Real (FrameMatrix period hPeriod frame) :=
  Matrix.normedSpace
@[reducible] local instance : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup
@[reducible] local instance : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace
local instance : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4
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
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

private abbrev Model :=
  PairedFiniteFrameMetricC2Core period hPeriod geometry frame

/-- Continuous point evaluation of an arbitrary finite C² matrix. -/
def finiteFrameC2MatrixValueAtCLM
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    C2FiniteMatrix period hPeriod frame.count →L[Real]
      FrameMatrix period hPeriod frame :=
  ContinuousLinearMap.pi fun row =>
    ContinuousLinearMap.pi fun column =>
      (c2ScalarValueAtCLM period hPeriod point).comp
        ((ContinuousLinearMap.proj column :
          (Fin frame.count → C2Scalar period hPeriod) →L[Real]
            C2Scalar period hPeriod).comp
          (ContinuousLinearMap.proj row :
            C2FiniteMatrix period hPeriod frame.count →L[Real]
              (Fin frame.count → C2Scalar period hPeriod)))

@[simp]
theorem finiteFrameC2MatrixValueAtCLM_apply
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (matrix : C2FiniteMatrix period hPeriod frame.count) :
    finiteFrameC2MatrixValueAtCLM period hPeriod frame point matrix =
      c2FiniteMatrixValueAt period hPeriod frame.count matrix point :=
  rfl

/-- Decode a redundant pointwise matrix and write the resulting tangent
endomorphism in an arbitrary tangent basis. -/
def finiteFrameDecodeMatrixAtCLM
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    FrameMatrix period hPeriod frame →L[Real] Matrix4 :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.toMatrix basis basis).toLinearMap.comp
      (ContinuousLinearMap.coeLM Real)).comp
      (finiteFrameMatrixDecodeLinearAt period hPeriod frame metric point))

@[simp]
theorem finiteFrameDecodeMatrixAtCLM_apply
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point))
    (matrix : FrameMatrix period hPeriod frame) :
    finiteFrameDecodeMatrixAtCLM period hPeriod frame metric point basis matrix =
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame metric point matrix).toLinearMap :=
  rfl

/-- Pointwise intrinsic matrix represented by an element of the completed C²
finite-frame corner. -/
def finiteFrameC2CornerMatrixAtCLM
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    C2FiniteFrameCorner period hPeriod frame geometry.plusMetric →L[Real] Matrix4 :=
  (finiteFrameDecodeMatrixAtCLM
      period hPeriod frame geometry.plusMetric point basis).comp
    ((finiteFrameC2MatrixValueAtCLM period hPeriod frame point).comp
      (c2FiniteFrameCornerSubmodule
        period hPeriod frame geometry.plusMetric).subtypeL)

@[simp]
theorem finiteFrameC2CornerMatrixAtCLM_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point))
    (root : C2FiniteFrameCorner period hPeriod frame geometry.plusMetric) :
    finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis root =
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count root.1 point)).toLinearMap :=
  rfl

private theorem c2FiniteFrameProjector_valueAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod frame.count
        (c2FiniteFrameProjector period hPeriod frame metric) point =
      finiteFrameProjectorMatrixAt period hPeriod frame metric point := by
  ext row column
  rfl

/-- Every completed corner element remains in the pointwise redundant matrix
corner after evaluation. -/
theorem c2FiniteFrameCorner_valueAt
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : C2FiniteFrameCorner period hPeriod frame metric)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectorMatrixAt period hPeriod frame metric point *
          c2FiniteMatrixValueAt period hPeriod frame.count root.1 point *
          finiteFrameProjectorMatrixAt period hPeriod frame metric point =
      c2FiniteMatrixValueAt period hPeriod frame.count root.1 point := by
  have h := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod frame.count matrix point)
    ((c2FiniteFrameCorner_mem_iff period hPeriod frame metric root.1).1 root.2)
  simpa only [c2FiniteFrameCornerProjection_apply,
    c2FiniteMatrixValueAt_product, c2FiniteFrameProjector_valueAt,
    Matrix.mul_assoc] using h

/-- Pointwise decoding carries multiplication of two corner matrices to
composition of their intrinsic endomorphisms. -/
theorem finiteFrameMatrixDecodeAt_mul_of_corner
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : FrameMatrix period hPeriod frame)
    (hFirst : finiteFrameProjectorMatrixAt period hPeriod frame metric point *
        first * finiteFrameProjectorMatrixAt period hPeriod frame metric point = first)
    (hSecond : finiteFrameProjectorMatrixAt period hPeriod frame metric point *
        second * finiteFrameProjectorMatrixAt period hPeriod frame metric point = second) :
    finiteFrameMatrixDecodeAt period hPeriod frame metric point (first * second) =
      (finiteFrameMatrixDecodeAt period hPeriod frame metric point first).comp
        (finiteFrameMatrixDecodeAt period hPeriod frame metric point second) := by
  have hEncodeFirst := finiteFrameEndomorphismMatrixAt_decode_of_corner
    period hPeriod frame metric point first hFirst
  have hEncodeSecond := finiteFrameEndomorphismMatrixAt_decode_of_corner
    period hPeriod frame metric point second hSecond
  calc
    finiteFrameMatrixDecodeAt period hPeriod frame metric point (first * second) =
        finiteFrameMatrixDecodeAt period hPeriod frame metric point
          (finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
              (finiteFrameMatrixDecodeAt period hPeriod frame metric point first) *
            finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
              (finiteFrameMatrixDecodeAt period hPeriod frame metric point second)) := by
      rw [hEncodeFirst, hEncodeSecond]
    _ = finiteFrameMatrixDecodeAt period hPeriod frame metric point
          (finiteFrameEndomorphismMatrixAt period hPeriod frame metric point
            ((finiteFrameMatrixDecodeAt period hPeriod frame metric point first).comp
              (finiteFrameMatrixDecodeAt period hPeriod frame metric point second))) := by
      rw [finiteFrameEndomorphismMatrixAt_comp]
    _ = _ := finiteFrameMatrixDecodeAt_encode period hPeriod frame metric point _

/-- The pointwise intrinsic matrix map intertwines the completed corner
Sylvester operator with the ordinary matrix Sylvester operator. -/
theorem finiteFrameC2CornerMatrixAtCLM_sylvester
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (root variation : C2FiniteFrameCorner period hPeriod frame geometry.plusMetric)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis
        (c2FiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric root variation) =
      finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis root *
          finiteFrameC2CornerMatrixAtCLM
            period hPeriod geometry frame point basis variation +
        finiteFrameC2CornerMatrixAtCLM
            period hPeriod geometry frame point basis variation *
          finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis root := by
  let rootValue := c2FiniteMatrixValueAt period hPeriod frame.count root.1 point
  let variationValue := c2FiniteMatrixValueAt period hPeriod frame.count variation.1 point
  have hRootCorner := c2FiniteFrameCorner_valueAt
    period hPeriod frame geometry.plusMetric root point
  have hVariationCorner := c2FiniteFrameCorner_valueAt
    period hPeriod frame geometry.plusMetric variation point
  have hDecode :
      finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (rootValue * variationValue + variationValue * rootValue) =
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point rootValue).comp
            (finiteFrameMatrixDecodeAt
              period hPeriod frame geometry.plusMetric point variationValue) +
          (finiteFrameMatrixDecodeAt
              period hPeriod frame geometry.plusMetric point variationValue).comp
            (finiteFrameMatrixDecodeAt
              period hPeriod frame geometry.plusMetric point rootValue) := by
    have hAdd := (finiteFrameMatrixDecodeLinearAt
      period hPeriod frame geometry.plusMetric point).map_add
        (rootValue * variationValue) (variationValue * rootValue)
    change finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        (rootValue * variationValue + variationValue * rootValue) =
      finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (rootValue * variationValue) +
        finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (variationValue * rootValue) at hAdd
    rw [hAdd,
      finiteFrameMatrixDecodeAt_mul_of_corner period hPeriod frame geometry.plusMetric point
        rootValue variationValue hRootCorner hVariationCorner,
      finiteFrameMatrixDecodeAt_mul_of_corner period hPeriod frame geometry.plusMetric point
        variationValue rootValue hVariationCorner hRootCorner]
  simp only [finiteFrameC2CornerMatrixAtCLM_apply]
  rw [c2FiniteFrameCornerSylvester_value, c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_product, c2FiniteMatrixValueAt_product, hDecode]
  change LinearMap.toMatrix basis basis
      ((finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point rootValue).toLinearMap.comp
          (finiteFrameMatrixDecodeAt
            period hPeriod frame geometry.plusMetric point variationValue).toLinearMap +
        (finiteFrameMatrixDecodeAt
            period hPeriod frame geometry.plusMetric point variationValue).toLinearMap.comp
          (finiteFrameMatrixDecodeAt
            period hPeriod frame geometry.plusMetric point rootValue).toLinearMap) =
    LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt
          period hPeriod frame geometry.plusMetric point rootValue).toLinearMap *
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt
          period hPeriod frame geometry.plusMetric point variationValue).toLinearMap +
    LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt
          period hPeriod frame geometry.plusMetric point variationValue).toLinearMap *
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt
          period hPeriod frame geometry.plusMetric point rootValue).toLinearMap
  rw [(LinearMap.toMatrix basis basis).map_add,
    LinearMap.toMatrix_comp basis basis basis
      (finiteFrameMatrixDecodeAt
        period hPeriod frame geometry.plusMetric point rootValue).toLinearMap
      (finiteFrameMatrixDecodeAt
        period hPeriod frame geometry.plusMetric point variationValue).toLinearMap,
    LinearMap.toMatrix_comp basis basis basis
      (finiteFrameMatrixDecodeAt
        period hPeriod frame geometry.plusMetric point variationValue).toLinearMap
      (finiteFrameMatrixDecodeAt
        period hPeriod frame geometry.plusMetric point rootValue).toLinearMap]

/-- Pointwise intrinsic decoding removes the redundant C² corner projection. -/
theorem finiteFrameC2CornerMatrixAtCLM_projection
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (matrix : C2FiniteMatrix period hPeriod frame.count)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis
        (finiteFrameC2CornerProjection
          period hPeriod frame geometry.plusMetric matrix) =
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count matrix point)).toLinearMap := by
  rw [finiteFrameC2CornerMatrixAtCLM_apply]
  have hValue :
      c2FiniteMatrixValueAt period hPeriod frame.count
          (finiteFrameC2CornerProjection
            period hPeriod frame geometry.plusMetric matrix).1 point =
        finiteFrameCornerProjectionAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count matrix point) := by
    change c2FiniteMatrixValueAt period hPeriod frame.count
        (c2FiniteFrameCornerProjection
          period hPeriod frame geometry.plusMetric matrix) point = _
    simp only [c2FiniteFrameCornerProjection_apply,
      c2FiniteMatrixValueAt_product, c2FiniteFrameProjector_valueAt,
      finiteFrameCornerProjectionAt_apply, Matrix.mul_assoc]
  rw [hValue, finiteFrameMatrixDecodeAt_cornerProjection]

/-- On the finite-frame corner, point evaluation of the completed polynomial
is the intrinsic four-dimensional spectral potential of the decoded root. -/
theorem finiteFrameC2SpectralPotential_valueAt_corner
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (root : C2FiniteFrameCorner period hPeriod frame reference)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (finiteFrameC2SpectralPotential period hPeriod frame reference coefficients root.1) point =
      matrixSpectralPotential coefficients
        (LinearMap.toMatrix basis basis
          (finiteFrameMatrixDecodeAt period hPeriod frame reference point
            (c2FiniteMatrixValueAt period hPeriod frame.count root.1 point)).toLinearMap) := by
  rw [finiteFrameC2SpectralPotential_valueAt]
  let matrix := c2FiniteMatrixValueAt period hPeriod frame.count root.1 point
  let decoded := finiteFrameMatrixDecodeAt period hPeriod frame reference point matrix
  calc
    finiteFrameSpectralPotential period hPeriod frame reference coefficients point matrix =
        finiteFrameSpectralPotential period hPeriod frame reference coefficients point
          (finiteFrameEndomorphismMatrixAt
            period hPeriod frame reference point decoded) := by
      apply congrArg
      exact (finiteFrameEndomorphismMatrixAt_decode_of_corner
        period hPeriod frame reference point matrix
          (c2FiniteFrameCorner_valueAt period hPeriod frame reference root point)).symm
    _ = matrixSpectralPotential coefficients
          (LinearMap.toMatrix basis basis decoded.toLinearMap) :=
      finiteFrameSpectralPotential_encode_eq_matrix
        period hPeriod frame reference coefficients point decoded basis

/-- The decoded completed Candidate-A root is its intrinsic tangent
endomorphism in every pointwise basis. -/
theorem finiteFrameC2CornerMatrixAtCLM_candidateRoot
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis
        (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame) =
      LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap := by
  rw [finiteFrameC2CornerMatrixAtCLM_apply]
  have hValue :
      c2FiniteMatrixValueAt period hPeriod frame.count
          (c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame) point =
        globalCandidateAFiniteFrameRootMatrix period hPeriod geometry frame point := by
    ext row column
    rfl
  change LinearMap.toMatrix basis basis
      (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        (c2FiniteMatrixValueAt period hPeriod frame.count
          (c2GlobalCandidateAFiniteFrameRoot period hPeriod geometry frame) point)).toLinearMap =
    LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap
  rw [hValue, globalCandidateAFiniteFrameRootMatrix_apply,
    finiteFrameMatrixDecodeAt_encode]

/-- Chain-rule derivative through the finite local root branch. -/
def pairedFiniteFrameC2SpectralPotentialDerivativeAtZero
    (coefficients : PotentialCoefficients) :
    Model period hPeriod geometry frame →L[Real] C2Scalar period hPeriod :=
  (fderiv Real
    (finiteFrameC2SpectralPotential period hPeriod frame geometry.plusMetric coefficients)
    (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular 0).1).comp
      ((c2FiniteFrameCornerSubmodule period hPeriod frame geometry.plusMetric).subtypeL.comp
        (pairedFiniteFrameMetricC2RootDerivativeAtZero period hPeriod geometry frame hRegular))

/-- Pointwise tangent-matrix velocity of the finite local root at the chart
center. -/
def pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    Model period hPeriod geometry frame →L[Real] Matrix4 :=
  (finiteFrameC2CornerMatrixAtCLM
      period hPeriod geometry frame point basis).comp
    (pairedFiniteFrameMetricC2RootDerivativeAtZero
      period hPeriod geometry frame hRegular)

@[simp]
theorem pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_apply
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point))
    (direction : Model period hPeriod geometry frame) :
    pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
        period hPeriod geometry frame hRegular point basis direction =
      finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis
        (pairedFiniteFrameMetricC2RootDerivativeAtZero
          period hPeriod geometry frame hRegular direction) :=
  rfl

theorem pairedFiniteFrameC2SpectralPotential_hasFDerivAt_zero
    (coefficients : PotentialCoefficients) :
    HasFDerivAt
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients)
      (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod geometry frame hRegular
        coefficients) 0 := by
  have hRoot :=
    pairedFiniteFrameMetricC2Root_hasFDerivAt_zero period hPeriod geometry frame hRegular
  have hRootValue :=
    (c2FiniteFrameCornerSubmodule period hPeriod frame geometry.plusMetric).subtypeL.hasFDerivAt.comp
      0 hRoot
  have hOuter : DifferentiableAt Real
      (finiteFrameC2SpectralPotential period hPeriod frame geometry.plusMetric coefficients)
      (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular 0).1 :=
    ((finiteFrameC2SpectralPotential_contDiff period hPeriod frame geometry.plusMetric
      coefficients).differentiable (by norm_num)) _
  have hComposed := hOuter.hasFDerivAt.comp 0 hRootValue
  exact hComposed.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

/-- Every spacetime value of the finite-frame spectral derivative is the
explicit four-dimensional spectral covector applied to the decoded root
velocity. -/
theorem pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_valueAt
    (coefficients : PotentialCoefficients)
    (direction : Model period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero
          period hPeriod geometry frame hRegular coefficients direction) point =
      matrixSpectralPotentialDerivative coefficients
        (LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap)
        (pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
          period hPeriod geometry frame hRegular point basis direction) := by
  let scalarEval := c2ScalarValueAtCLM period hPeriod point
  let rootMatrix := finiteFrameC2CornerMatrixAtCLM
    period hPeriod geometry frame point basis
  let derivative := pairedFiniteFrameC2SpectralPotentialDerivativeAtZero
    period hPeriod geometry frame hRegular coefficients
  have hPotential := pairedFiniteFrameC2SpectralPotential_hasFDerivAt_zero
    period hPeriod geometry frame hRegular coefficients
  have hLeft := HasFDerivAt.comp
    (f := pairedFiniteFrameC2SpectralPotential
      period hPeriod frame geometry hRegular coefficients)
    (g := fun field => scalarEval field) 0
    scalarEval.hasFDerivAt hPotential
  have hRoot := pairedFiniteFrameMetricC2Root_hasFDerivAt_zero
    period hPeriod geometry frame hRegular
  have hRootMatrix := rootMatrix.hasFDerivAt.comp 0 hRoot
  have hFinite : HasFDerivAt
      (matrixSpectralPotential coefficients)
      (matrixSpectralPotentialDerivative coefficients
        (rootMatrix (pairedFiniteFrameMetricC2Root
          period hPeriod geometry frame hRegular 0)))
      (rootMatrix (pairedFiniteFrameMetricC2Root
        period hPeriod geometry frame hRegular 0)) := by
    exact matrixSpectralPotential_hasFDerivAt coefficients
      (rootMatrix (pairedFiniteFrameMetricC2Root
        period hPeriod geometry frame hRegular 0))
  have hRight := hFinite.comp 0 hRootMatrix
  have hLeftOnRight : HasFDerivAt
      (matrixSpectralPotential coefficients ∘ fun current =>
        rootMatrix (pairedFiniteFrameMetricC2Root
          period hPeriod geometry frame hRegular current))
      (scalarEval.comp derivative) 0 := by
    apply hLeft.congr_of_eventuallyEq
    filter_upwards [] with current
    exact (finiteFrameC2SpectralPotential_valueAt_corner
      period hPeriod frame geometry.plusMetric coefficients
        (pairedFiniteFrameMetricC2Root
          period hPeriod geometry frame hRegular current) point basis).symm
  have hDerivative := hLeftOnRight.unique hRight
  have hApplied := congrArg
    (fun linear : Model period hPeriod geometry frame →L[Real] Real =>
      linear direction) hDerivative
  have hCenter :
      rootMatrix (pairedFiniteFrameMetricC2Root
        period hPeriod geometry frame hRegular 0) =
        LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap := by
    rw [pairedFiniteFrameMetricC2Root_zero]
    exact finiteFrameC2CornerMatrixAtCLM_candidateRoot
      period hPeriod geometry frame point basis
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero
        period hPeriod geometry frame hRegular coefficients direction) point =
    matrixSpectralPotentialDerivative coefficients
      (rootMatrix (pairedFiniteFrameMetricC2Root
        period hPeriod geometry frame hRegular 0))
      (pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
        period hPeriod geometry frame hRegular point basis direction) at hApplied
  rw [hCenter] at hApplied
  exact hApplied

end
end P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D
end JanusFormal
