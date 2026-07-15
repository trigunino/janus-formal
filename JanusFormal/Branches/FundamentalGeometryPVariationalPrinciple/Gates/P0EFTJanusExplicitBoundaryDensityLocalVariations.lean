import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLedger
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Local first variations of the explicit pointwise boundary-density ledger.
Each curve varies one supplied slot while all metric, inverse-metric and
measure data on that stratum remain fixed.

These identities do not prove cancellation of the Einstein--Hilbert boundary
flux, null-generator reparametrization invariance, or any auxiliary
worldvolume equation of motion.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitBoundaryDensityLocalVariations

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger

theorem affineScalar_hasDerivAt (base variation : ℝ) :
    HasDerivAt (fun t : ℝ => base + t * variation) variation 0 := by
  have h : HasDerivAt (fun t : ℝ => base + t * variation)
      (1 * variation) 0 :=
    (hasDerivAt_id 0).mul_const variation |>.const_add base
  exact h.congr_deriv (one_mul variation)

/-- Pointwise non-null density along an affine extrinsic-curvature variation,
with the induced metric and its supplied inverse held fixed. -/
def nonNullGHYExtrinsicCurve
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (extrinsicVariation : Matrix3) (t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.inducedMetric| *
      Matrix.trace
        (data.inducedInverse *
          (data.extrinsicCurvature + t • extrinsicVariation))

/-- Coefficient of the extrinsic-curvature variation at fixed induced data. -/
def nonNullGHYExtrinsicVariation
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (extrinsicVariation : Matrix3) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.inducedMetric| *
      Matrix.trace (data.inducedInverse * extrinsicVariation)

theorem nonNullGHYExtrinsicCurve_affine
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (extrinsicVariation : Matrix3) (t : ℝ) :
    nonNullGHYExtrinsicCurve einsteinScale data extrinsicVariation t =
      nonNullGHYDensity einsteinScale data +
        t * nonNullGHYExtrinsicVariation
          einsteinScale data extrinsicVariation := by
  simp [nonNullGHYExtrinsicCurve, nonNullGHYDensity,
    nonNullGHYExtrinsicVariation, meanCurvatureTrace, Matrix.mul_add]
  ring

theorem nonNullGHYExtrinsicCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (extrinsicVariation : Matrix3) :
    HasDerivAt
      (nonNullGHYExtrinsicCurve einsteinScale data extrinsicVariation)
      (nonNullGHYExtrinsicVariation
        einsteinScale data extrinsicVariation) 0 := by
  have hAffine : HasDerivAt
      (fun t : ℝ =>
        nonNullGHYDensity einsteinScale data +
          t * nonNullGHYExtrinsicVariation
            einsteinScale data extrinsicVariation)
      (nonNullGHYExtrinsicVariation
        einsteinScale data extrinsicVariation) 0 := by
    exact affineScalar_hasDerivAt
      (nonNullGHYDensity einsteinScale data)
      (nonNullGHYExtrinsicVariation
        einsteinScale data extrinsicVariation)
  exact hAffine.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      nonNullGHYExtrinsicCurve_affine
        einsteinScale data extrinsicVariation t)

/-- Null-generator density along an inaffinity variation, with the screen
metric, its inverse and the generator convention otherwise fixed. -/
def nullGeneratorInaffinityCurve
    (einsteinScale : ℝ) (data : NullBoundaryPointData)
    (inaffinityVariation t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.screenMetric| *
      (data.inaffinity + t * inaffinityVariation)

def nullGeneratorInaffinityVariation
    (einsteinScale : ℝ) (data : NullBoundaryPointData)
    (inaffinityVariation : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.screenMetric| * inaffinityVariation

theorem nullGeneratorInaffinityCurve_affine
    (einsteinScale : ℝ) (data : NullBoundaryPointData)
    (inaffinityVariation t : ℝ) :
    nullGeneratorInaffinityCurve
        einsteinScale data inaffinityVariation t =
      nullGeneratorDensity einsteinScale data +
        t * nullGeneratorInaffinityVariation
          einsteinScale data inaffinityVariation := by
  unfold nullGeneratorInaffinityCurve nullGeneratorDensity
    nullGeneratorInaffinityVariation
  ring

theorem nullGeneratorInaffinityCurve_hasDerivAt
    (einsteinScale : ℝ) (data : NullBoundaryPointData)
    (inaffinityVariation : ℝ) :
    HasDerivAt
      (nullGeneratorInaffinityCurve
        einsteinScale data inaffinityVariation)
      (nullGeneratorInaffinityVariation
        einsteinScale data inaffinityVariation) 0 := by
  have hAffine : HasDerivAt
      (fun t : ℝ =>
        nullGeneratorDensity einsteinScale data +
          t * nullGeneratorInaffinityVariation
            einsteinScale data inaffinityVariation)
      (nullGeneratorInaffinityVariation
        einsteinScale data inaffinityVariation) 0 := by
    exact affineScalar_hasDerivAt
      (nullGeneratorDensity einsteinScale data)
      (nullGeneratorInaffinityVariation
        einsteinScale data inaffinityVariation)
  exact hAffine.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      nullGeneratorInaffinityCurve_affine
        einsteinScale data inaffinityVariation t)

/-- Joint density along an angle variation, with the corner metric and its
supplied inverse held fixed. -/
def jointAngleCurve
    (einsteinScale : ℝ) (data : JointPointData)
    (angleVariation t : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.cornerMetric| *
      (data.jointAngle + t * angleVariation)

def jointAngleVariation
    (einsteinScale : ℝ) (data : JointPointData)
    (angleVariation : ℝ) : ℝ :=
  einsteinScale * data.orientationSign *
    Real.sqrt |Matrix.det data.cornerMetric| * angleVariation

theorem jointAngleCurve_affine
    (einsteinScale : ℝ) (data : JointPointData)
    (angleVariation t : ℝ) :
    jointAngleCurve einsteinScale data angleVariation t =
      jointDensity einsteinScale data +
        t * jointAngleVariation einsteinScale data angleVariation := by
  unfold jointAngleCurve jointDensity jointAngleVariation
  ring

theorem jointAngleCurve_hasDerivAt
    (einsteinScale : ℝ) (data : JointPointData)
    (angleVariation : ℝ) :
    HasDerivAt (jointAngleCurve einsteinScale data angleVariation)
      (jointAngleVariation einsteinScale data angleVariation) 0 := by
  have hAffine : HasDerivAt
      (fun t : ℝ =>
        jointDensity einsteinScale data +
          t * jointAngleVariation einsteinScale data angleVariation)
      (jointAngleVariation einsteinScale data angleVariation) 0 := by
    exact affineScalar_hasDerivAt
      (jointDensity einsteinScale data)
      (jointAngleVariation einsteinScale data angleVariation)
  exact hAffine.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      jointAngleCurve_affine
        einsteinScale data angleVariation t)

/-- Worldvolume density along simultaneous local-Lagrangian and tension
variations, with the supplied measure held fixed. -/
def worldvolumeLocalCurve
    (data : WorldvolumePointData)
    (localLagrangianVariation tensionVariation t : ℝ) : ℝ :=
  data.measureDensity *
    ((data.localLagrangian + t * localLagrangianVariation) -
      (data.tension + t * tensionVariation))

def worldvolumeLocalVariation
    (data : WorldvolumePointData)
    (localLagrangianVariation tensionVariation : ℝ) : ℝ :=
  data.measureDensity *
    (localLagrangianVariation - tensionVariation)

theorem worldvolumeLocalCurve_affine
    (data : WorldvolumePointData)
    (localLagrangianVariation tensionVariation t : ℝ) :
    worldvolumeLocalCurve
        data localLagrangianVariation tensionVariation t =
      worldvolumeDensity data +
        t * worldvolumeLocalVariation
          data localLagrangianVariation tensionVariation := by
  unfold worldvolumeLocalCurve worldvolumeDensity worldvolumeLocalVariation
  ring

theorem worldvolumeLocalCurve_hasDerivAt
    (data : WorldvolumePointData)
    (localLagrangianVariation tensionVariation : ℝ) :
    HasDerivAt
      (worldvolumeLocalCurve
        data localLagrangianVariation tensionVariation)
      (worldvolumeLocalVariation
        data localLagrangianVariation tensionVariation) 0 := by
  have hAffine : HasDerivAt
      (fun t : ℝ =>
        worldvolumeDensity data +
          t * worldvolumeLocalVariation
            data localLagrangianVariation tensionVariation)
      (worldvolumeLocalVariation
        data localLagrangianVariation tensionVariation) 0 := by
    exact affineScalar_hasDerivAt
      (worldvolumeDensity data)
      (worldvolumeLocalVariation
        data localLagrangianVariation tensionVariation)
  exact hAffine.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      worldvolumeLocalCurve_affine
        data localLagrangianVariation tensionVariation t)

theorem worldvolumeLocalLagrangianCurve_hasDerivAt
    (data : WorldvolumePointData) (localLagrangianVariation : ℝ) :
    HasDerivAt
      (worldvolumeLocalCurve data localLagrangianVariation 0)
      (data.measureDensity * localLagrangianVariation) 0 := by
  simpa [worldvolumeLocalVariation] using
    worldvolumeLocalCurve_hasDerivAt data localLagrangianVariation 0

theorem worldvolumeTensionCurve_hasDerivAt
    (data : WorldvolumePointData) (tensionVariation : ℝ) :
    HasDerivAt
      (worldvolumeLocalCurve data 0 tensionVariation)
      (-data.measureDensity * tensionVariation) 0 := by
  convert worldvolumeLocalCurve_hasDerivAt data 0 tensionVariation using 1
  simp [worldvolumeLocalVariation]

/- The four curves above remain pointwise data on different strata.  No
summation across face, joint and worldvolume dimensions is made here. -/

end

end P0EFTJanusExplicitBoundaryDensityLocalVariations
end JanusFormal
