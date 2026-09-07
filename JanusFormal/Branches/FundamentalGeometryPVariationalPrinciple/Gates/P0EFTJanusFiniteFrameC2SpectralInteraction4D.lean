import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedRelativeC2Root4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D

/-! # Spectral interaction on the redundant finite-frame C² root

The Newton polynomial is evaluated directly in the completed scalar algebra.
Only the determinant receives the identity on the redundant complement.
No smooth root operator is decoded from a C² root.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2SpectralInteraction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
open P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

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

variable (frame : SmoothD8Frame period hPeriod)
  (reference : SmoothGeneralLorentzMetric period hPeriod)
local notation "MatrixC2" => C2FiniteMatrix period hPeriod frame.count

def finiteFrameC2ExtendedRootMatrix (root : MatrixC2) : MatrixC2 :=
  c2FiniteMatrixIdentity period hPeriod frame.count -
    smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothFiniteFrameProjectorCoefficients period hPeriod frame reference) + root

/-- The first five intrinsic Newton invariants in the redundant C² encoding. -/
def finiteFrameC2SpectralPotential (coefficients : PotentialCoefficients) (root : MatrixC2) :
    C2Scalar period hPeriod :=
  let trace := c2FiniteMatrixTrace period hPeriod frame.count root
  let square := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count root root
  let cube := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count square root
  coefficients.beta0 • c2ScalarOne period hPeriod + coefficients.beta1 • trace +
    coefficients.beta2 • ((1 / 2 : Real) •
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace trace -
        c2FiniteMatrixTrace period hPeriod frame.count square)) +
    coefficients.beta3 • ((1 / 6 : Real) •
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace trace) trace -
        (3 : Real) • canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace
          (c2FiniteMatrixTrace period hPeriod frame.count square) +
        (2 : Real) • c2FiniteMatrixTrace period hPeriod frame.count cube)) +
    coefficients.beta4 • c2FiniteMatrixDeterminant period hPeriod frame.count
      (finiteFrameC2ExtendedRootMatrix period hPeriod frame reference root)

theorem finiteFrameC2SpectralPotential_contDiff (coefficients : PotentialCoefficients) :
    ContDiff Real ∞ (finiteFrameC2SpectralPotential period hPeriod frame reference coefficients) := by
  let trace := c2FiniteMatrixTrace period hPeriod frame.count
  have hTrace : ContDiff Real ∞ trace := trace.contDiff
  have hSquare := c2FiniteMatrixSquare_contDiff period hPeriod frame.count
  have hCube : ContDiff Real ∞ (fun root : MatrixC2 =>
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count root root) root) :=
    ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count).contDiff.comp
      hSquare).clm_apply contDiff_id
  have hTraceSquare := hTrace.comp hSquare
  have hTraceCube := hTrace.comp hCube
  have hTraceTwo := ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).contDiff.comp
    hTrace).clm_apply hTrace
  have hTraceThree := ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).contDiff.comp
    hTraceTwo).clm_apply hTrace
  have hTraceTraceSquare := ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).contDiff.comp
    hTrace).clm_apply hTraceSquare
  have hExtended : ContDiff Real ∞
      (finiteFrameC2ExtendedRootMatrix period hPeriod frame reference) := by
    unfold finiteFrameC2ExtendedRootMatrix
    fun_prop
  have hDet := (c2FiniteMatrixDeterminant_contDiff period hPeriod frame.count).comp hExtended
  unfold finiteFrameC2SpectralPotential
  have h0 := (contDiff_const : ContDiff Real ∞
    (fun _ : MatrixC2 => c2ScalarOne period hPeriod)).const_smul coefficients.beta0
  have h1 := hTrace.const_smul coefficients.beta1
  have h2 := ((hTraceTwo.sub hTraceSquare).const_smul (1 / 2 : Real)).const_smul
    coefficients.beta2
  have h3 := (((hTraceThree.sub (hTraceTraceSquare.const_smul (3 : Real))).add
    (hTraceCube.const_smul (2 : Real))).const_smul (1 / 6 : Real)).const_smul coefficients.beta3
  have h4 := hDet.const_smul coefficients.beta4
  simpa only [Function.comp_apply, c2FiniteMatrixSquare] using
    (((h0.add h1).add h2).add h3).add h4

private theorem finiteFrameC2Trace_valueAt (root : MatrixC2)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2FiniteMatrixTrace period hPeriod frame.count root) point =
    Matrix.trace (c2FiniteMatrixValueAt period hPeriod frame.count root point) := by
  rw [c2FiniteMatrixTrace_apply]
  let evaluate : C(EffectiveQuotient period hPeriod, Real) →ₗ[Real] Real :=
    { toFun := fun value => value point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change evaluate ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
      (∑ index : Fin frame.count, root index index)) =
    ∑ index : Fin frame.count,
      evaluate ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod) (root index index))
  rw [map_sum, map_sum]

private theorem finiteFrameC2ScalarOne_valueAt (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2ScalarOne period hPeriod) point = 1 := rfl

private theorem finiteFrameC2ScalarAdd_valueAt (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (first + second) point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point +
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second point := rfl

private theorem finiteFrameC2ScalarSub_valueAt (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (first - second) point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point -
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second point := rfl

private theorem finiteFrameC2ScalarSmul_valueAt (scalar : Real) (field : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (scalar • field) point =
      scalar * canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod field point := rfl

private theorem finiteFrameC2ScalarProduct_valueAt (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second) point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second point := rfl

private theorem finiteFrameC2Projector_valueAt (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod frame.count
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameProjectorCoefficients period hPeriod frame reference)) point =
    finiteFrameProjectorMatrixAt period hPeriod frame reference point := by
  ext row column
  rfl

private theorem finiteFrameC2MatrixSub_valueAt (first second : MatrixC2)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod frame.count (first - second) point =
      c2FiniteMatrixValueAt period hPeriod frame.count first point -
        c2FiniteMatrixValueAt period hPeriod frame.count second point := rfl

/-- Pointwise evaluation is exactly the intrinsic redundant-frame polynomial. -/
theorem finiteFrameC2SpectralPotential_valueAt (coefficients : PotentialCoefficients)
    (root : MatrixC2) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (finiteFrameC2SpectralPotential period hPeriod frame reference coefficients root) point =
    finiteFrameSpectralPotential period hPeriod frame reference coefficients point
      (c2FiniteMatrixValueAt period hPeriod frame.count root point) := by
  have hExtended : c2FiniteMatrixValueAt period hPeriod frame.count
      (finiteFrameC2ExtendedRootMatrix period hPeriod frame reference root) point =
      1 - finiteFrameProjectorMatrixAt period hPeriod frame reference point +
        c2FiniteMatrixValueAt period hPeriod frame.count root point := by
    unfold finiteFrameC2ExtendedRootMatrix
    rw [c2FiniteMatrixValueAt_add, finiteFrameC2MatrixSub_valueAt,
      c2FiniteMatrixValueAt_identity, finiteFrameC2Projector_valueAt]
  have hDet : canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2FiniteMatrixDeterminant period hPeriod frame.count
        (finiteFrameC2ExtendedRootMatrix period hPeriod frame reference root)) point =
      Matrix.det (1 - finiteFrameProjectorMatrixAt period hPeriod frame reference point +
        c2FiniteMatrixValueAt period hPeriod frame.count root point) := by
    rw [c2FiniteMatrixDeterminant_continuous_apply]
    change Matrix.det (c2FiniteMatrixValueAt period hPeriod frame.count
      (finiteFrameC2ExtendedRootMatrix period hPeriod frame reference root) point) = _
    rw [hExtended]
  unfold finiteFrameC2SpectralPotential finiteFrameSpectralPotential
  simp only [finiteFrameC2ScalarAdd_valueAt, finiteFrameC2ScalarSub_valueAt,
    finiteFrameC2ScalarSmul_valueAt, finiteFrameC2ScalarProduct_valueAt,
    finiteFrameC2ScalarOne_valueAt]
  simp_rw [finiteFrameC2Trace_valueAt]
  simp_rw [c2FiniteMatrixValueAt_product]
  rw [hDet]
  ring

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (hRegular : ∀ point, Function.Bijective (intrinsicCandidateASylvesterAt period hPeriod geometry point))
local notation "Model" => PairedFiniteFrameMetricC2Core period hPeriod geometry frame

def pairedFiniteFrameC2SpectralPotential (coefficients : PotentialCoefficients) (variation : Model) :
    C2Scalar period hPeriod :=
  finiteFrameC2SpectralPotential period hPeriod frame geometry.plusMetric coefficients
    (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular variation).1

theorem pairedFiniteFrameC2SpectralPotential_contDiffOn (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2 (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients)
      (pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular) := by
  have hRoot := pairedFiniteFrameMetricC2Root_contDiffOn period hPeriod geometry frame hRegular
  have hValue := (c2FiniteFrameCornerSubmodule period hPeriod frame geometry.plusMetric).subtypeL.contDiff
    |>.comp_contDiffOn hRoot
  exact (finiteFrameC2SpectralPotential_contDiff period hPeriod frame geometry.plusMetric coefficients).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.comp_contDiffOn hValue

/-- At the chart center, the completed potential is the genuine Candidate-A potential in every pointwise basis. -/
theorem pairedFiniteFrameC2SpectralPotential_zero_valueAt (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real (TangentSpace coverModelWithCorners point)) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients 0) point =
    matrixSpectralPotential coefficients
      (LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap) := by
  rw [pairedFiniteFrameC2SpectralPotential, pairedFiniteFrameMetricC2Root_zero,
    finiteFrameC2SpectralPotential_valueAt]
  change finiteFrameSpectralPotential period hPeriod frame geometry.plusMetric coefficients point
      (globalCandidateAFiniteFrameRootMatrix period hPeriod geometry frame point) = _
  rw [globalCandidateAFiniteFrameRootMatrix_apply]
  exact finiteFrameSpectralPotential_encode_eq_matrix period hPeriod frame geometry.plusMetric coefficients
    point (geometry.rootAt point) basis

end
end P0EFTJanusFiniteFrameC2SpectralInteraction4D
end JanusFormal
