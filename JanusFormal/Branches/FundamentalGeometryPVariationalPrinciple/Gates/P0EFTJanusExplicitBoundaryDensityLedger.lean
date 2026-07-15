import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Pointwise density ledger for the boundary pieces that Candidate A must declare.
The non-null GHY, null-generator, null reparametrization counterterm, joint and
generic worldvolume-placeholder slots are explicit and convention signs are
constrained data.

This file fixes no throat geometry and proves no Einstein--Hilbert boundary
variation.  It prevents an unspecified "boundary term" from being counted as
a completed variational principle.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitBoundaryDensityLedger

set_option autoImplicit false

noncomputable section

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def IsOrientationSign (sign : ℝ) : Prop := sign = 1 ∨ sign = -1

structure Matrix3InverseWitness (metric inverse : Matrix3) : Prop where
  inverse_mul : inverse * metric = 1
  mul_inverse : metric * inverse = 1

structure Matrix2InverseWitness (metric inverse : Matrix2) : Prop where
  inverse_mul : inverse * metric = 1
  mul_inverse : metric * inverse = 1

/-- Data for a spacelike or timelike boundary face. -/
structure NonNullBoundaryPointData where
  inducedMetric : Matrix3
  inducedInverse : Matrix3
  extrinsicCurvature : Matrix3
  orientationSign : ℝ
  inverseWitness : Matrix3InverseWitness inducedMetric inducedInverse
  inducedMetricSymmetric : inducedMetric.transpose = inducedMetric
  extrinsicCurvatureSymmetric :
    extrinsicCurvature.transpose = extrinsicCurvature
  orientationSignAdmissible : IsOrientationSign orientationSign

def meanCurvatureTrace (data : NonNullBoundaryPointData) : ℝ :=
  Matrix.trace (data.inducedInverse * data.extrinsicCurvature)

/-- GHY coordinate density for a bulk coefficient `einsteinScale / 2`. -/
def nonNullGHYDensity
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.inducedMetric| * meanCurvatureTrace data

theorem nonNullGHYDensity_zero_of_extrinsicCurvature_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (hZero : data.extrinsicCurvature = 0) :
    nonNullGHYDensity einsteinScale data = 0 := by
  simp [nonNullGHYDensity, meanCurvatureTrace, hZero]

/-- Supplied null-face data.  The normalization convention is carried by the
orientation sign and the chosen generator parametrization. -/
structure NullBoundaryPointData where
  screenMetric : Matrix2
  screenInverse : Matrix2
  orientationSign : ℝ
  inaffinity : ℝ
  expansion : ℝ
  renormalizationLengthScale : ℝ
  inverseWitness : Matrix2InverseWitness screenMetric screenInverse
  screenMetricSymmetric : screenMetric.transpose = screenMetric
  screenMetricDeterminantPositive : 0 < Matrix.det screenMetric
  orientationSignAdmissible : IsOrientationSign orientationSign
  renormalizationLengthScalePositive : 0 < renormalizationLengthScale

/-- Fixed-parametrization null-generator density. -/
def nullGeneratorDensity
    (einsteinScale : ℝ) (data : NullBoundaryPointData) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.screenMetric| * data.inaffinity

/-- Continuous zero extension of `Θ log(ℓ |Θ|)` at a stationary cross-section. -/
def expansionLogFactor (data : NullBoundaryPointData) : ℝ :=
  if data.expansion = 0 then 0
  else data.expansion *
    Real.log (data.renormalizationLengthScale * |data.expansion|)

@[simp]
theorem expansionLogFactor_zero
    (data : NullBoundaryPointData) (hZero : data.expansion = 0) :
    expansionLogFactor data = 0 := by
  simp [expansionLogFactor, hZero]

/-- Standard expansion-times-log slot with its stationary `Θ = 0` extension. -/
def nullReparametrizationCountertermDensity
    (einsteinScale : ℝ) (data : NullBoundaryPointData) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.screenMetric| * expansionLogFactor data

structure JointPointData where
  cornerMetric : Matrix2
  cornerInverse : Matrix2
  orientationSign : ℝ
  jointAngle : ℝ
  inverseWitness : Matrix2InverseWitness cornerMetric cornerInverse
  cornerMetricSymmetric : cornerMetric.transpose = cornerMetric
  cornerMetricDeterminantPositive : 0 < Matrix.det cornerMetric
  orientationSignAdmissible : IsOrientationSign orientationSign

/-- Hayward/null-joint slot; `jointAngle` carries the boundary-type and normal
normalization convention. -/
def jointDensity (einsteinScale : ℝ) (data : JointPointData) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.cornerMetric| * data.jointAngle

structure WorldvolumePointData where
  inducedMetric : Matrix3
  measureDensity : ℝ
  tension : ℝ
  localLagrangian : ℝ
  inducedMetricSymmetric : inducedMetric.transpose = inducedMetric

/-- Declared local worldvolume slot.  The measure is independent data so a
lightlike/degenerate induced metric is not incorrectly assigned a determinant
measure.  Its auxiliary fields and actual LL measure law remain to be supplied. -/
def worldvolumeDensity (data : WorldvolumePointData) : ℝ :=
  data.measureDensity * (data.localLagrangian - data.tension)

structure GravitationalBoundaryPointData where
  nonNull : NonNullBoundaryPointData
  nullFace : NullBoundaryPointData
  joint : JointPointData

/-- Densities on three-dimensional faces, two-dimensional joints and the
worldvolume are kept in distinct typed slots; they must not be added before
integration over their respective strata. -/
structure PointwiseBoundaryDensityLedger where
  nonNullFace : ℝ
  nullGeneratorFace : ℝ
  nullCountertermFace : ℝ
  jointStratum : ℝ

def gravitationalBoundaryDensityLedger
    (einsteinScale : ℝ) (data : GravitationalBoundaryPointData) :
    PointwiseBoundaryDensityLedger where
  nonNullFace := nonNullGHYDensity einsteinScale data.nonNull
  nullGeneratorFace := nullGeneratorDensity einsteinScale data.nullFace
  nullCountertermFace :=
    nullReparametrizationCountertermDensity einsteinScale data.nullFace
  jointStratum := jointDensity einsteinScale data.joint

/-- Only already-integrated values from the distinct strata may be summed. -/
structure IntegratedGravitationalBoundaryActionValues where
  nonNullFaces : ℝ
  nullGeneratorFaces : ℝ
  nullCountertermFaces : ℝ
  joints : ℝ

def totalIntegratedGravitationalBoundaryAction
    (data : IntegratedGravitationalBoundaryActionValues) : ℝ :=
  data.nonNullFaces + data.nullGeneratorFaces +
    data.nullCountertermFaces + data.joints

structure IntegratedTwoSectorBoundaryActionValues where
  plusGravity : IntegratedGravitationalBoundaryActionValues
  minusGravity : IntegratedGravitationalBoundaryActionValues
  commonWorldvolume : ℝ

def totalIntegratedTwoSectorBoundaryAction
    (data : IntegratedTwoSectorBoundaryActionValues) : ℝ :=
  totalIntegratedGravitationalBoundaryAction data.plusGravity +
    totalIntegratedGravitationalBoundaryAction data.minusGravity +
    data.commonWorldvolume

def exchangeGravitationalSectors
    (data : IntegratedTwoSectorBoundaryActionValues) :
    IntegratedTwoSectorBoundaryActionValues :=
  { plusGravity := data.minusGravity
    minusGravity := data.plusGravity
    commonWorldvolume := data.commonWorldvolume }

theorem totalIntegratedTwoSectorBoundaryAction_exchange
    (data : IntegratedTwoSectorBoundaryActionValues) :
    totalIntegratedTwoSectorBoundaryAction (exchangeGravitationalSectors data) =
      totalIntegratedTwoSectorBoundaryAction data := by
  unfold totalIntegratedTwoSectorBoundaryAction exchangeGravitationalSectors
  ring

/- Integration maps, causal compatibility for both metrics, joint/face
coherence, the actual LL auxiliary measure law, corner additivity, generator
reparametrization invariance and cancellation of the Einstein--Hilbert flux
remain separate gates. -/

end

end P0EFTJanusExplicitBoundaryDensityLedger
end JanusFormal
