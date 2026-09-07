import Mathlib.LinearAlgebra.Matrix.SchurComplement
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricContraction4D

/-! # Intrinsic spectral potential in the redundant finite-frame corner

Reconstruction makes the coefficient and synthesis maps a retraction. The
complement-identity determinant is therefore the determinant of the actual
tangent endomorphism, despite redundancy of the smooth generating family.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D

set_option autoImplicit false

noncomputable section
open scoped BigOperators Manifold ContDiff

section Algebra

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
variable {n : Nat}

private def reconstructionAnalysis (coefficient : Fin n → V →ₗ[Real] Real) :
    V →ₗ[Real] (Fin n → Real) := LinearMap.pi coefficient

private def reconstructionSynthesis (vector : Fin n → V) :
    (Fin n → Real) →ₗ[Real] V := (Pi.basisFun Real (Fin n)).constr Real vector

omit [FiniteDimensional Real V] in
private theorem reconstruction_encoding_factor
    (vector : Fin n → V) (coefficient : Fin n → V →ₗ[Real] Real)
    (operator : V →ₗ[Real] V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι Real V) :
    (fun i j => coefficient i (operator (vector j))) =
      LinearMap.toMatrix basis (Pi.basisFun Real (Fin n)) (reconstructionAnalysis coefficient) *
      LinearMap.toMatrix basis basis operator *
      LinearMap.toMatrix (Pi.basisFun Real (Fin n)) basis (reconstructionSynthesis vector) := by
  calc
    _ = LinearMap.toMatrix (Pi.basisFun Real (Fin n)) (Pi.basisFun Real (Fin n))
        (((reconstructionAnalysis coefficient).comp operator).comp
          (reconstructionSynthesis vector)) := by
      ext i j
      simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, LinearMap.comp_apply,
        reconstructionSynthesis, Module.Basis.constr_basis, reconstructionAnalysis,
        LinearMap.pi_apply]
    _ = _ := by
      rw [LinearMap.toMatrix_comp (Pi.basisFun Real (Fin n)) basis
        (Pi.basisFun Real (Fin n)), LinearMap.toMatrix_comp basis basis
          (Pi.basisFun Real (Fin n))]

private theorem matrix_retraction_extended_det
    {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (analysis : Matrix m k Real) (synthesis : Matrix k m Real)
    (operator : Matrix k k Real) (hRetraction : synthesis * analysis = 1) :
    Matrix.det (1 - analysis * synthesis + analysis * operator * synthesis) =
      Matrix.det operator := by
  calc
    _ = Matrix.det (1 + analysis * ((operator - 1) * synthesis)) := by
      congr 1
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
      abel
    _ = Matrix.det (1 + ((operator - 1) * synthesis) * analysis) :=
      Matrix.det_one_add_mul_comm _ _
    _ = _ := by
      rw [Matrix.mul_assoc, hRetraction, Matrix.mul_one]
      congr 1
      abel

private theorem reconstruction_matrix_invariants
    (vector : Fin n → V) (coefficient : Fin n → V →ₗ[Real] Real)
    (hReconstruct : ∀ value, value = ∑ i, coefficient i value • vector i)
    (operator : V →ₗ[Real] V) :
    (Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) - Matrix.of (fun i j => coefficient i (vector j)) +
        Matrix.of (fun i j => coefficient i (operator (vector j)))) = LinearMap.det operator) ∧
    (Matrix.trace (fun i j => coefficient i (operator (vector j))) =
      LinearMap.trace Real V operator) := by
  classical
  let basis := Module.finBasis Real V
  let analysis := LinearMap.toMatrix basis (Pi.basisFun Real (Fin n))
    (reconstructionAnalysis coefficient)
  let synthesis := LinearMap.toMatrix (Pi.basisFun Real (Fin n)) basis
    (reconstructionSynthesis vector)
  let matrix := LinearMap.toMatrix basis basis operator
  have hRetraction : (reconstructionSynthesis vector).comp (reconstructionAnalysis coefficient) =
      LinearMap.id := by
    ext value
    simp only [LinearMap.comp_apply, LinearMap.id_apply, reconstructionSynthesis,
      Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
      reconstructionAnalysis, LinearMap.pi_apply]
    exact (hReconstruct value).symm
  have hMatrixRetraction : synthesis * analysis = 1 := by
    change LinearMap.toMatrix (Pi.basisFun Real (Fin n)) basis (reconstructionSynthesis vector) *
      LinearMap.toMatrix basis (Pi.basisFun Real (Fin n)) (reconstructionAnalysis coefficient) = 1
    rw [← LinearMap.toMatrix_comp basis (Pi.basisFun Real (Fin n)) basis,
      hRetraction, LinearMap.toMatrix_id]
  have hProjector : (fun i j => coefficient i (vector j)) = analysis * synthesis := by
    have h := reconstruction_encoding_factor vector coefficient LinearMap.id basis
    simpa only [LinearMap.id_apply, LinearMap.toMatrix_id, Matrix.mul_one] using h
  have hEncoding : (fun i j => coefficient i (operator (vector j))) =
      analysis * matrix * synthesis :=
    reconstruction_encoding_factor vector coefficient operator basis
  constructor
  · rw [hProjector, hEncoding]
    exact (matrix_retraction_extended_det analysis synthesis matrix hMatrixRetraction).trans
      (LinearMap.det_toMatrix basis operator)
  · calc
      _ = Matrix.trace (analysis * matrix * synthesis) := congrArg Matrix.trace hEncoding
      _ = Matrix.trace (synthesis * (analysis * matrix)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace matrix := by
        rw [← Matrix.mul_assoc, hMatrixRetraction, Matrix.one_mul]
      _ = _ := (LinearMap.trace_eq_matrix_trace Real basis operator).symm

end Algebra

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixSquareRootInteractionDensity

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- Adding identity on the redundant complement recovers the genuine determinant. -/
theorem finiteFrameEndomorphismMatrixAt_extended_det
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (operator : TangentFiber period hPeriod point →L[Real] TangentFiber period hPeriod point) :
    Matrix.det (1 - finiteFrameProjectorMatrixAt period hPeriod frame reference point +
      finiteFrameEndomorphismMatrixAt period hPeriod frame reference point operator) =
        LinearMap.det operator.toLinearMap := by
  have h := reconstruction_matrix_invariants (frame.vectorAt point)
    (fun i => (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
      ).toLinearMap)
    (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame reference point)
    operator.toLinearMap
  exact h.1

/-- Redundant matrix encoding preserves the intrinsic trace. -/
theorem finiteFrameEndomorphismMatrixAt_trace
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (operator : TangentFiber period hPeriod point →L[Real] TangentFiber period hPeriod point) :
    Matrix.trace (finiteFrameEndomorphismMatrixAt period hPeriod frame reference point operator) =
      LinearMap.trace Real (TangentFiber period hPeriod point) operator.toLinearMap := by
  have h := reconstruction_matrix_invariants (frame.vectorAt point)
    (fun i => (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point i
      ).toLinearMap)
    (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame reference point)
    operator.toLinearMap
  exact h.2

/-- Candidate-A Newton coefficients in the actual finite-frame corner. -/
def finiteFrameSpectralPotential
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients) (point : EffectiveQuotient period hPeriod)
    (root : FiniteFrameMatrix period hPeriod frame) : Real :=
  coefficients.beta0 + coefficients.beta1 * Matrix.trace root +
    coefficients.beta2 * ((Matrix.trace root ^ 2 - Matrix.trace (root * root)) / 2) +
    coefficients.beta3 * ((Matrix.trace root ^ 3 -
      3 * Matrix.trace root * Matrix.trace (root * root) +
      2 * Matrix.trace (root * root * root)) / 6) +
    coefficients.beta4 * Matrix.det
      (1 - finiteFrameProjectorMatrixAt period hPeriod frame reference point + root)

/-- The redundant formula is the established spectral potential in every tangent basis. -/
theorem finiteFrameSpectralPotential_encode_eq_matrix
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients) (point : EffectiveQuotient period hPeriod)
    (operator : TangentFiber period hPeriod point →L[Real] TangentFiber period hPeriod point)
    (basis : Module.Basis (Fin 4) Real (TangentFiber period hPeriod point)) :
    finiteFrameSpectralPotential period hPeriod frame reference coefficients point
      (finiteFrameEndomorphismMatrixAt period hPeriod frame reference point operator) =
        matrixSpectralPotential coefficients (LinearMap.toMatrix basis basis operator.toLinearMap) := by
  have hTrace (value : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :=
    (finiteFrameEndomorphismMatrixAt_trace period hPeriod frame reference point value).trans
      (LinearMap.trace_eq_matrix_trace Real basis value.toLinearMap)
  have hFirst := hTrace operator
  have hSecond := hTrace (operator.comp operator)
  change Matrix.trace (finiteFrameEndomorphismMatrixAt period hPeriod frame reference point
    (operator.comp operator)) = Matrix.trace (LinearMap.toMatrix basis basis
      (operator.toLinearMap.comp operator.toLinearMap)) at hSecond
  rw [finiteFrameEndomorphismMatrixAt_comp,
    LinearMap.toMatrix_comp basis basis basis operator.toLinearMap operator.toLinearMap] at hSecond
  have hThird := hTrace ((operator.comp operator).comp operator)
  change Matrix.trace (finiteFrameEndomorphismMatrixAt period hPeriod frame reference point
    ((operator.comp operator).comp operator)) = Matrix.trace (LinearMap.toMatrix basis basis
      ((operator.toLinearMap.comp operator.toLinearMap).comp operator.toLinearMap)) at hThird
  simp only [finiteFrameEndomorphismMatrixAt_comp,
    LinearMap.toMatrix_comp basis basis basis
      (operator.toLinearMap.comp operator.toLinearMap) operator.toLinearMap,
    LinearMap.toMatrix_comp basis basis basis operator.toLinearMap operator.toLinearMap] at hThird
  have hDet := (finiteFrameEndomorphismMatrixAt_extended_det period hPeriod frame reference point
    operator).trans (LinearMap.det_toMatrix basis operator.toLinearMap).symm
  unfold finiteFrameSpectralPotential matrixSpectralPotential matrixElementary0 matrixElementary1
    matrixElementary2 matrixElementary3 matrixElementary4
  rw [hFirst, hSecond, hThird, hDet]
  simp only [mul_one]

end
end P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
end JanusFormal
