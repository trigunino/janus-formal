import Mathlib.Analysis.Calculus.Deriv.Star
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D

/-!
# Inter-level orthogonality in the primitive SpinC geometric L2 product

The scalar null powers are diagonalized by the rotation Casimir on the
round sphere.  Rotation-invariance of the sphere measure makes that Casimir
symmetric, hence different sphere levels are orthogonal.  The result is then
transported to the explicit primitive SpinC packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate Manifold ContDiff
open P0EFTJanusInvariantMeasureFlowIPP4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

local instance complexNormedSpaceReal : NormedSpace Real Complex :=
  NormedAlgebra.toNormedSpace Complex

private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)

private abbrev SphereMeasure : Measure MonopoleSphere :=
  (volume : Measure EuclideanR3).toSphere

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData :=
  fixedEquatorData period hPeriod

private abbrev ThroatBase :=
  MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) :=
  borel _

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

private def euclideanCoordinateCLM
    (coordinate : Fin 3) : EuclideanR3 →L[Real] Real :=
  (ContinuousLinearMap.proj coordinate).comp
    (EuclideanSpace.equiv (Fin 3) Real).toContinuousLinearMap

/-- The ambient null linear form as a real continuous linear map. -/
def primitiveSpinCNullLinearFunctional
    (parameter : Complex) : EuclideanR3 →L[Real] Complex :=
  ∑ coordinate : Fin 3,
    ContinuousLinearMap.smulRight
      (euclideanCoordinateCLM coordinate)
      (primitiveSpinCSolidNullVector parameter coordinate)

@[simp]
theorem primitiveSpinCNullLinearFunctional_apply
    (parameter : Complex) (point : EuclideanR3) :
    primitiveSpinCNullLinearFunctional parameter point =
      ∑ coordinate : Fin 3,
        primitiveSpinCSolidNullVector parameter coordinate *
          (point coordinate : Complex) := by
  simp [primitiveSpinCNullLinearFunctional, euclideanCoordinateCLM]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact mul_comm _ _

@[simp]
theorem primitiveSpinCNullLinearFunctional_sphere
    (parameter : Complex) (point : MonopoleSphere) :
    primitiveSpinCNullLinearFunctional parameter point.1 =
      primitiveSpinCNullSphereScalar parameter point := by
  simp [primitiveSpinCNullSphereScalar, monopoleSphereCoordinate]

/-- First angular derivative of a null linear form. -/
def primitiveSpinCNullAngularDerivative
    (axis : Fin 3) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  primitiveSpinCNullLinearFunctional parameter
    (canonicalRotationVelocity axis point.1)

/-- Second angular derivative of a null linear form. -/
def primitiveSpinCNullAngularSecondDerivative
    (axis : Fin 3) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  primitiveSpinCNullLinearFunctional parameter
    (canonicalRotationVelocity axis
      (canonicalRotationVelocity axis point.1))

theorem primitiveSpinCNullSphereScalar_rotation_hasDerivAt
    (axis : Fin 3) (parameter : Complex)
    (point : MonopoleSphere) (angle : Real) :
    HasDerivAt
      (fun t =>
        primitiveSpinCNullSphereScalar parameter
          (standardSphereRotation axis t point))
      (primitiveSpinCNullAngularDerivative axis parameter
        (standardSphereRotation axis angle point))
      angle := by
  simpa [primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullSphereScalar, monopoleSphereCoordinate,
    Function.comp_def] using
    (primitiveSpinCNullLinearFunctional parameter).hasFDerivAt
      |>.comp_hasDerivAt angle
        (standardSphereRotation_coe_hasDerivAt axis point angle)

theorem primitiveSpinCNullAngularDerivative_rotation_hasDerivAt
    (axis : Fin 3) (parameter : Complex)
    (point : MonopoleSphere) (angle : Real) :
    HasDerivAt
      (fun t =>
        primitiveSpinCNullAngularDerivative axis parameter
          (standardSphereRotation axis t point))
      (primitiveSpinCNullAngularSecondDerivative axis parameter
        (standardSphereRotation axis angle point))
      angle := by
  simpa [primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullAngularSecondDerivative, Function.comp_def] using
    (primitiveSpinCNullLinearFunctional parameter).hasFDerivAt
      |>.comp_hasDerivAt angle
        ((canonicalRotationVelocityCLM axis).hasFDerivAt
          |>.comp_hasDerivAt angle
            (standardSphereRotation_coe_hasDerivAt axis point angle))

/-- Scalar null power on the physical sphere. -/
def primitiveSpinCNullSpherePower
    (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  primitiveSpinCNullSphereScalar parameter point ^ degree

/-- First angular derivative of a scalar null power. -/
def primitiveSpinCNullSpherePowerAngularDerivative
    (axis : Fin 3) (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  (degree : Complex) *
    primitiveSpinCNullSphereScalar parameter point ^ (degree - 1) *
    primitiveSpinCNullAngularDerivative axis parameter point

/-- Second angular derivative of a scalar null power. -/
def primitiveSpinCNullSpherePowerAngularSecondDerivative
    (axis : Fin 3) (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  (degree : Complex) * (degree - 1 : Nat) *
      primitiveSpinCNullSphereScalar parameter point ^ (degree - 2) *
      primitiveSpinCNullAngularDerivative axis parameter point ^ 2 +
    (degree : Complex) *
      primitiveSpinCNullSphereScalar parameter point ^ (degree - 1) *
      primitiveSpinCNullAngularSecondDerivative axis parameter point

theorem primitiveSpinCNullSpherePower_rotation_hasDerivAt
    (axis : Fin 3) (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) (angle : Real) :
    HasDerivAt
      (fun t =>
        primitiveSpinCNullSpherePower degree parameter
          (standardSphereRotation axis t point))
      (primitiveSpinCNullSpherePowerAngularDerivative
        axis degree parameter
        (standardSphereRotation axis angle point))
      angle := by
  simpa [primitiveSpinCNullSpherePower,
    primitiveSpinCNullSpherePowerAngularDerivative,
    mul_assoc] using!
      (primitiveSpinCNullSphereScalar_rotation_hasDerivAt
        axis parameter point angle).pow degree

theorem primitiveSpinCNullSpherePowerAngularDerivative_rotation_hasDerivAt
    (axis : Fin 3) (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) (angle : Real) :
    HasDerivAt
      (fun t =>
        primitiveSpinCNullSpherePowerAngularDerivative
          axis degree parameter
          (standardSphereRotation axis t point))
      (primitiveSpinCNullSpherePowerAngularSecondDerivative
        axis degree parameter
        (standardSphereRotation axis angle point))
      angle := by
  have hScalar :=
    primitiveSpinCNullSphereScalar_rotation_hasDerivAt
      axis parameter point angle
  have hAngular :=
    primitiveSpinCNullAngularDerivative_rotation_hasDerivAt
      axis parameter point angle
  have hPower := hScalar.pow (degree - 1)
  have hConstant :
      HasDerivAt (fun _ : Real => (degree : Complex)) 0 angle :=
    hasDerivAt_const angle _
  have hProduct := (hConstant.mul hPower).mul hAngular
  refine (hProduct.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [primitiveSpinCNullSpherePowerAngularSecondDerivative,
      Nat.sub_sub, pow_two]
    ring
  · filter_upwards with t
    rfl

/-- The three angular first derivatives obey the null-vector identity. -/
theorem primitiveSpinCNullAngularDerivative_sq_sum
    (parameter : Complex) (point : MonopoleSphere) :
    ∑ axis : Fin 3,
        primitiveSpinCNullAngularDerivative axis parameter point ^ 2 =
      -(primitiveSpinCNullSphereScalar parameter point ^ 2) := by
  simp [primitiveSpinCNullAngularDerivative,
    primitiveSpinCNullSphereScalar, monopoleSphereCoordinate,
    primitiveSpinCSolidNullVector, canonicalRotationVelocity,
    Fin.sum_univ_succ]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The trace of the three second rotation velocities is `-2x`. -/
theorem primitiveSpinCNullAngularSecondDerivative_sum
    (parameter : Complex) (point : MonopoleSphere) :
    ∑ axis : Fin 3,
        primitiveSpinCNullAngularSecondDerivative axis parameter point =
      -2 * primitiveSpinCNullSphereScalar parameter point := by
  simp [primitiveSpinCNullAngularSecondDerivative,
    primitiveSpinCNullSphereScalar, monopoleSphereCoordinate,
    canonicalRotationVelocity, Fin.sum_univ_succ]
  ring

/-- Positive rotation Casimir on a scalar null power. -/
def primitiveSpinCNullSpherePowerRotationCasimir
    (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) : Complex :=
  -∑ axis : Fin 3,
    primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis degree parameter point

/-- Every degree-`p` null power has the exact round-sphere Casimir
eigenvalue `p(p+1)`. -/
theorem primitiveSpinCNullSpherePowerRotationCasimir_eq
    (degree : Nat) (parameter : Complex)
    (point : MonopoleSphere) :
    primitiveSpinCNullSpherePowerRotationCasimir
        degree parameter point =
      (degree : Complex) * (degree + 1 : Nat) *
        primitiveSpinCNullSpherePower degree parameter point := by
  let scalar := primitiveSpinCNullSphereScalar parameter point
  have hFirst :
      (∑ axis : Fin 3,
        primitiveSpinCNullSpherePowerAngularSecondDerivative
          axis degree parameter point) =
        ((degree : Complex) * (degree - 1 : Nat) *
            scalar ^ (degree - 2)) *
            (∑ axis : Fin 3,
              primitiveSpinCNullAngularDerivative
                axis parameter point ^ 2) +
          ((degree : Complex) * scalar ^ (degree - 1)) *
            (∑ axis : Fin 3,
              primitiveSpinCNullAngularSecondDerivative
                axis parameter point) := by
    simp only [primitiveSpinCNullSpherePowerAngularSecondDerivative,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [primitiveSpinCNullSpherePowerRotationCasimir, hFirst,
    primitiveSpinCNullAngularDerivative_sq_sum,
    primitiveSpinCNullAngularSecondDerivative_sum]
  change
    -(((degree : Complex) * (degree - 1 : Nat) *
          scalar ^ (degree - 2)) * -(scalar ^ 2) +
        ((degree : Complex) * scalar ^ (degree - 1)) *
          (-2 * scalar)) =
      (degree : Complex) * (degree + 1 : Nat) *
        scalar ^ degree
  rcases degree with _ | _ | degree
  · simp
  · simp
  · simp [Nat.cast_add, pow_succ]
    ring

theorem sphere_integral_star_mul_derivative_eq_neg
    (axis : Fin 3)
    (first second firstDerivative secondDerivative :
      MonopoleSphere → Complex)
    (hFirst : Continuous first)
    (hSecond : Continuous second)
    (hFirstDerivative : Continuous firstDerivative)
    (hSecondDerivative : Continuous secondDerivative)
    (hFirstCurve : ∀ angle point,
      HasDerivAt
        (fun t => first (standardSphereRotation axis t point))
        (firstDerivative (standardSphereRotation axis angle point))
        angle)
    (hSecondCurve : ∀ angle point,
      HasDerivAt
        (fun t => second (standardSphereRotation axis t point))
        (secondDerivative (standardSphereRotation axis angle point))
        angle) :
    (∫ point,
        star (first point) * secondDerivative point
        ∂SphereMeasure) =
      -∫ point,
        star (firstDerivative point) * second point
        ∂SphereMeasure := by
  let F : Real → MonopoleSphere → Complex := fun angle point =>
    star (first (standardSphereRotation axis angle point)) *
      second (standardSphereRotation axis angle point)
  let F' : Real → MonopoleSphere → Complex := fun angle point =>
    star (first (standardSphereRotation axis angle point)) *
        secondDerivative (standardSphereRotation axis angle point) +
      star (firstDerivative (standardSphereRotation axis angle point)) *
        second (standardSphereRotation axis angle point)
  have hFlow : Continuous (fun input : Real × MonopoleSphere =>
      standardSphereRotation axis input.1 input.2) :=
    standardSphereJointRotation_continuous axis
  have hF : Continuous
      (fun input : Real × MonopoleSphere => F input.1 input.2) := by
    exact (hFirst.comp hFlow).star.mul (hSecond.comp hFlow)
  have hF' : Continuous
      (fun input : Real × MonopoleSphere => F' input.1 input.2) := by
    exact ((hFirst.comp hFlow).star.mul
      (hSecondDerivative.comp hFlow)).add
        ((hFirstDerivative.comp hFlow).star.mul
          (hSecond.comp hFlow))
  have hCurve : ∀ angle point,
      HasDerivAt (fun t => F t point) (F' angle point) angle := by
    intro angle point
    have hProduct :=
      (hFirstCurve angle point).star.mul
        (hSecondCurve angle point)
    refine (hProduct.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [F']
      ring
    · filter_upwards with t
      rfl
  have hInvariant : ∀ angle,
      (∫ point, F angle point ∂SphereMeasure) =
        ∫ point, F 0 point ∂SphereMeasure := by
    intro angle
    calc
      (∫ point, F angle point ∂SphereMeasure) =
          ∫ point, star (first point) * second point
            ∂SphereMeasure := by
              simpa [F] using
                (standardSphereRotation_measurePreserving axis angle)
                  |>.integral_comp
                    (standardSphereRotation_measurableEmbedding axis angle)
                    (fun point => star (first point) * second point)
      _ = ∫ point, F 0 point ∂SphereMeasure := by
        simp [F]
  have hSumZero :=
    integral_derivative_eq_zero_of_invariant_vector
      SphereMeasure F F' hF hF' hCurve hInvariant
  have hFirstTerm : Integrable
      (fun point =>
        star (first point) * secondDerivative point)
      SphereMeasure :=
    (hFirst.star.mul hSecondDerivative)
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hSecondTerm : Integrable
      (fun point =>
        star (firstDerivative point) * second point)
      SphereMeasure :=
    (hFirstDerivative.star.mul hSecond)
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp only [F', standardSphereRotation_zero] at hSumZero
  rw [integral_add hFirstTerm hSecondTerm] at hSumZero
  exact add_eq_zero_iff_eq_neg.mp hSumZero

theorem primitiveSpinCNullSpherePower_continuous
    (degree : Nat) (parameter : Complex) :
    Continuous (primitiveSpinCNullSpherePower degree parameter) := by
  unfold primitiveSpinCNullSpherePower primitiveSpinCNullSphereScalar
    monopoleSphereCoordinate
  fun_prop

theorem primitiveSpinCNullSphereScalar_continuous
    (parameter : Complex) :
    Continuous (primitiveSpinCNullSphereScalar parameter) := by
  unfold primitiveSpinCNullSphereScalar monopoleSphereCoordinate
  fun_prop

theorem primitiveSpinCNullAngularDerivative_continuous
    (axis : Fin 3) (parameter : Complex) :
    Continuous (primitiveSpinCNullAngularDerivative axis parameter) := by
  change Continuous (fun point : MonopoleSphere =>
    primitiveSpinCNullLinearFunctional parameter
      (canonicalRotationVelocityCLM axis point.1))
  exact (primitiveSpinCNullLinearFunctional parameter).continuous.comp
    ((canonicalRotationVelocityCLM axis).continuous.comp
      continuous_subtype_val)

theorem primitiveSpinCNullAngularSecondDerivative_continuous
    (axis : Fin 3) (parameter : Complex) :
    Continuous
      (primitiveSpinCNullAngularSecondDerivative axis parameter) := by
  change Continuous (fun point : MonopoleSphere =>
    primitiveSpinCNullLinearFunctional parameter
      (canonicalRotationVelocityCLM axis
        (canonicalRotationVelocityCLM axis point.1)))
  exact (primitiveSpinCNullLinearFunctional parameter).continuous.comp
    ((canonicalRotationVelocityCLM axis).continuous.comp
      ((canonicalRotationVelocityCLM axis).continuous.comp
        continuous_subtype_val))

theorem primitiveSpinCNullSpherePowerAngularDerivative_continuous
    (axis : Fin 3) (degree : Nat) (parameter : Complex) :
    Continuous
      (primitiveSpinCNullSpherePowerAngularDerivative
        axis degree parameter) := by
  unfold primitiveSpinCNullSpherePowerAngularDerivative
  exact (continuous_const.mul
      ((primitiveSpinCNullSphereScalar_continuous parameter).pow
        (degree - 1))).mul
          (primitiveSpinCNullAngularDerivative_continuous
            axis parameter)

theorem primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
    (axis : Fin 3) (degree : Nat) (parameter : Complex) :
    Continuous
      (primitiveSpinCNullSpherePowerAngularSecondDerivative
        axis degree parameter) := by
  have hFirst : Continuous (fun point : MonopoleSphere =>
      ((degree : Complex) * (degree - 1 : Nat)) *
        primitiveSpinCNullSphereScalar parameter point ^ (degree - 2) *
        primitiveSpinCNullAngularDerivative axis parameter point ^ 2) :=
    (continuous_const.mul
      ((primitiveSpinCNullSphereScalar_continuous parameter).pow
        (degree - 2))).mul
          ((primitiveSpinCNullAngularDerivative_continuous
            axis parameter).pow 2)
  have hSecond : Continuous (fun point : MonopoleSphere =>
      (degree : Complex) *
        primitiveSpinCNullSphereScalar parameter point ^ (degree - 1) *
        primitiveSpinCNullAngularSecondDerivative axis parameter point) :=
    (continuous_const.mul
      ((primitiveSpinCNullSphereScalar_continuous parameter).pow
        (degree - 1))).mul
          (primitiveSpinCNullAngularSecondDerivative_continuous
            axis parameter)
  unfold primitiveSpinCNullSpherePowerAngularSecondDerivative
  exact hFirst.add hSecond

/-- One rotation generator is skew-Hermitian on arbitrary null powers. -/
theorem primitiveSpinCNullSpherePower_angular_ipp
    (axis : Fin 3)
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            axis secondDegree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star (primitiveSpinCNullSpherePowerAngularDerivative
          axis firstDegree firstParameter point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure := by
  exact sphere_integral_star_mul_derivative_eq_neg axis
    (primitiveSpinCNullSpherePower firstDegree firstParameter)
    (primitiveSpinCNullSpherePower secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis secondDegree secondParameter)
    (primitiveSpinCNullSpherePower_continuous
      firstDegree firstParameter)
    (primitiveSpinCNullSpherePower_continuous
      secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis secondDegree secondParameter)
    (fun angle point =>
      primitiveSpinCNullSpherePower_rotation_hasDerivAt
        axis firstDegree firstParameter point angle)
    (fun angle point =>
      primitiveSpinCNullSpherePower_rotation_hasDerivAt
        axis secondDegree secondParameter point angle)

/-- The square of one rotation generator is Hermitian symmetric on null
powers. -/
theorem primitiveSpinCNullSpherePower_angularSecond_symmetric
    (axis : Fin 3)
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
          primitiveSpinCNullSpherePowerAngularSecondDerivative
            axis secondDegree secondParameter point
        ∂SphereMeasure) =
      ∫ point,
        star (primitiveSpinCNullSpherePowerAngularSecondDerivative
          axis firstDegree firstParameter point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure := by
  have hFirst := sphere_integral_star_mul_derivative_eq_neg axis
    (primitiveSpinCNullSpherePower firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis secondDegree secondParameter)
    (primitiveSpinCNullSpherePower_continuous
      firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
      axis secondDegree secondParameter)
    (fun angle point =>
      primitiveSpinCNullSpherePower_rotation_hasDerivAt
        axis firstDegree firstParameter point angle)
    (fun angle point =>
      primitiveSpinCNullSpherePowerAngularDerivative_rotation_hasDerivAt
        axis secondDegree secondParameter point angle)
  have hSecond := sphere_integral_star_mul_derivative_eq_neg axis
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePower secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative
      axis secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePower_continuous
      secondDegree secondParameter)
    (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
      axis firstDegree firstParameter)
    (primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis secondDegree secondParameter)
    (fun angle point =>
      primitiveSpinCNullSpherePowerAngularDerivative_rotation_hasDerivAt
        axis firstDegree firstParameter point angle)
    (fun angle point =>
      primitiveSpinCNullSpherePower_rotation_hasDerivAt
        axis secondDegree secondParameter point angle)
  rw [hFirst, hSecond]
  simp

/-- The full positive rotation Casimir is Hermitian symmetric on the null
packet. -/
theorem primitiveSpinCNullSpherePower_rotationCasimir_symmetric
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
          primitiveSpinCNullSpherePowerRotationCasimir
            secondDegree secondParameter point
        ∂SphereMeasure) =
      ∫ point,
        star (primitiveSpinCNullSpherePowerRotationCasimir
          firstDegree firstParameter point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure := by
  let first :=
    primitiveSpinCNullSpherePower firstDegree firstParameter
  let second :=
    primitiveSpinCNullSpherePower secondDegree secondParameter
  let firstSecondDerivative := fun axis : Fin 3 =>
    primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis firstDegree firstParameter
  let secondSecondDerivative := fun axis : Fin 3 =>
    primitiveSpinCNullSpherePowerAngularSecondDerivative
      axis secondDegree secondParameter
  have hLeftIntegrable (axis : Fin 3) : Integrable
      (fun point =>
        star (first point) * secondSecondDerivative axis point)
      SphereMeasure :=
    ((primitiveSpinCNullSpherePower_continuous
      firstDegree firstParameter).star.mul
        (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
          axis secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRightIntegrable (axis : Fin 3) : Integrable
      (fun point =>
        star (firstSecondDerivative axis point) * second point)
      SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
      axis firstDegree firstParameter).star.mul
        (primitiveSpinCNullSpherePower_continuous
          secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hLeftExpansion :
      (fun point =>
        star (first point) *
          primitiveSpinCNullSpherePowerRotationCasimir
            secondDegree secondParameter point) =
        fun point =>
          -∑ axis : Fin 3,
            star (first point) *
              secondSecondDerivative axis point := by
    funext point
    simp [primitiveSpinCNullSpherePowerRotationCasimir,
      secondSecondDerivative, Finset.mul_sum]
  have hRightExpansion :
      (fun point =>
        star (primitiveSpinCNullSpherePowerRotationCasimir
          firstDegree firstParameter point) * second point) =
        fun point =>
          -∑ axis : Fin 3,
            star (firstSecondDerivative axis point) *
              second point := by
    funext point
    simp [primitiveSpinCNullSpherePowerRotationCasimir,
      firstSecondDerivative, Finset.sum_mul]
  have hLeftIntegral :
      (∫ point,
        ∑ axis : Fin 3,
          star (first point) * secondSecondDerivative axis point
        ∂SphereMeasure) =
        ∑ axis : Fin 3,
          ∫ point,
            star (first point) * secondSecondDerivative axis point
            ∂SphereMeasure := by
    rw [integral_finsetSum]
    intro axis _
    exact hLeftIntegrable axis
  have hRightIntegral :
      (∫ point,
        ∑ axis : Fin 3,
          star (firstSecondDerivative axis point) * second point
        ∂SphereMeasure) =
        ∑ axis : Fin 3,
          ∫ point,
            star (firstSecondDerivative axis point) * second point
            ∂SphereMeasure := by
    rw [integral_finsetSum]
    intro axis _
    exact hRightIntegrable axis
  rw [show primitiveSpinCNullSpherePower
      firstDegree firstParameter = first by rfl,
    show primitiveSpinCNullSpherePower
      secondDegree secondParameter = second by rfl,
    hLeftExpansion, hRightExpansion, integral_neg, integral_neg,
    hLeftIntegral, hRightIntegral]
  congr 1
  apply Finset.sum_congr rfl
  intro axis _
  exact primitiveSpinCNullSpherePower_angularSecond_symmetric
    axis firstDegree secondDegree firstParameter secondParameter

/-- Scalar null harmonics of distinct sphere degrees are exactly
orthogonal for the round-sphere measure. -/
theorem primitiveSpinCNullSpherePower_level_orthogonal
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex)
    (hDegrees : firstDegree ≠ secondDegree) :
    (∫ point,
        star (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure) = 0 := by
  let pairing :=
    ∫ point,
      star (primitiveSpinCNullSpherePower
        firstDegree firstParameter point) *
        primitiveSpinCNullSpherePower
          secondDegree secondParameter point
      ∂SphereMeasure
  have hSymmetric :=
    primitiveSpinCNullSpherePower_rotationCasimir_symmetric
      firstDegree secondDegree firstParameter secondParameter
  have hEigenRelation :
      ((secondDegree : Complex) * (secondDegree + 1 : Nat)) * pairing =
        ((firstDegree : Complex) * (firstDegree + 1 : Nat)) *
          pairing := by
    calc
      ((secondDegree : Complex) * (secondDegree + 1 : Nat)) *
          pairing =
          ∫ point,
            star (primitiveSpinCNullSpherePower
              firstDegree firstParameter point) *
              primitiveSpinCNullSpherePowerRotationCasimir
                secondDegree secondParameter point
            ∂SphereMeasure := by
              simp_rw [primitiveSpinCNullSpherePowerRotationCasimir_eq]
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with point
              simp
              ring
      _ = ∫ point,
            star (primitiveSpinCNullSpherePowerRotationCasimir
              firstDegree firstParameter point) *
              primitiveSpinCNullSpherePower
                secondDegree secondParameter point
            ∂SphereMeasure := hSymmetric
      _ = ((firstDegree : Complex) * (firstDegree + 1 : Nat)) *
          pairing := by
            simp_rw [primitiveSpinCNullSpherePowerRotationCasimir_eq]
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with point
            simp
            ring
  have hNatEigen :
      secondDegree * (secondDegree + 1) ≠
        firstDegree * (firstDegree + 1) := by
    rcases Nat.lt_or_gt_of_ne hDegrees.symm with hLess | hGreater
    · exact ne_of_lt (by nlinarith)
    · exact ne_of_gt (by nlinarith)
  have hComplexEigen :
      (secondDegree : Complex) * (secondDegree + 1 : Nat) ≠
        (firstDegree : Complex) * (firstDegree + 1 : Nat) := by
    exact_mod_cast hNatEigen
  have hProduct :
      (((secondDegree : Complex) * (secondDegree + 1 : Nat)) -
        ((firstDegree : Complex) * (firstDegree + 1 : Nat))) *
          pairing = 0 := by
    linear_combination hEigenRelation
  exact (mul_eq_zero.mp hProduct).resolve_left
    (sub_ne_zero.mpr hComplexEigen)

/-- The two local Hopf coordinates have constant squared norm two. -/
theorem primitiveMonopoleZeroLocalValue_normSq_sum
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart) :
    star (primitiveMonopoleZeroLocalValue chart point) *
          primitiveMonopoleZeroLocalValue chart point +
        star (primitiveMonopoleZeroComplementLocalValue chart point) *
          primitiveMonopoleZeroComplementLocalValue chart point =
      2 := by
  cases chart with
  | north =>
      have hPositive :
          0 < 1 + monopoleSphereCoordinate point 2 :=
        one_add_monopoleSphereCoordinate_two_pos_of_mem_north
          point hChart
      have hSqrtNe :
          Real.sqrt (1 + monopoleSphereCoordinate point 2) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hPositive
      have hSqrtSq :
          Real.sqrt (1 + monopoleSphereCoordinate point 2) ^ 2 =
            1 + monopoleSphereCoordinate point 2 :=
        Real.sq_sqrt (le_of_lt hPositive)
      change
        conj (primitiveMonopoleZeroNorthValue point) *
              primitiveMonopoleZeroNorthValue point +
            conj
                (primitiveMonopoleZeroComplementNorthValue point) *
              primitiveMonopoleZeroComplementNorthValue point =
          2
      rw [← Complex.normSq_eq_conj_mul_self,
        ← Complex.normSq_eq_conj_mul_self]
      simp [primitiveMonopoleZeroNorthValue,
        primitiveMonopoleZeroComplementNorthValue,
        Complex.real_smul, Complex.normSq_apply,
        monopoleSphereXY]
      norm_cast
      field_simp [hSqrtNe]
      nlinarith [monopoleSphereCoordinate_sq_sum point]
  | south =>
      have hPositive :
          0 < 1 - monopoleSphereCoordinate point 2 :=
        one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
          point hChart
      have hSqrtNe :
          Real.sqrt (1 - monopoleSphereCoordinate point 2) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hPositive
      have hSqrtSq :
          Real.sqrt (1 - monopoleSphereCoordinate point 2) ^ 2 =
            1 - monopoleSphereCoordinate point 2 :=
        Real.sq_sqrt (le_of_lt hPositive)
      change
        conj (primitiveMonopoleZeroSouthValue point) *
              primitiveMonopoleZeroSouthValue point +
            conj
                (primitiveMonopoleZeroComplementSouthValue point) *
              primitiveMonopoleZeroComplementSouthValue point =
          2
      rw [← Complex.normSq_eq_conj_mul_self,
        ← Complex.normSq_eq_conj_mul_self]
      simp [primitiveMonopoleZeroSouthValue,
        primitiveMonopoleZeroComplementSouthValue,
        Complex.real_smul, Complex.normSq_apply,
        monopoleSphereXY]
      norm_cast
      field_simp [hSqrtNe]
      nlinarith [monopoleSphereCoordinate_sq_sum point]

theorem ambientHalfSpinorHermitianPairing_smul_self
    (scalar : Complex) (spinor : AmbientHalfSpinor2) :
    ambientHalfSpinorHermitianPairing
        (scalar • spinor) (scalar • spinor) =
      star scalar * scalar *
        ambientHalfSpinorHermitianPairing spinor spinor := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    Fin.sum_univ_succ]
  ring

theorem d9DoubledMatterSpinorHermitianPairing_plane_self
    (matter : D9DoubledMatterFiber)
    (firstScalar secondScalar : Complex)
    (firstVector secondVector : AmbientHalfSpinor2)
    (hMatter :
      d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
        (firstScalar • firstVector, secondScalar • secondVector))
    (hFirstVector :
      ambientHalfSpinorHermitianPairing firstVector firstVector = 2)
    (hSecondVector :
      ambientHalfSpinorHermitianPairing secondVector secondVector = 2) :
    d9DoubledMatterSpinorHermitianPairing matter matter =
      2 * (star firstScalar * firstScalar +
        star secondScalar * secondScalar) := by
  have hFirst :
      matterFiberHalfSpinorLinearEquiv matter.1 =
        firstScalar • firstVector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hMatter
  have hSecond :
      matterFiberHalfSpinorLinearEquiv matter.2 =
        secondScalar • secondVector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hMatter
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  rw [hFirst, hSecond,
    ambientHalfSpinorHermitianPairing_smul_self,
    ambientHalfSpinorHermitianPairing_smul_self,
    hFirstVector, hSecondVector]
  ring

@[simp]
theorem ambientHalfGammaPositiveEigenvector_self_pairing :
    ambientHalfSpinorHermitianPairing
        ambientHalfGammaPositiveEigenvector
        ambientHalfGammaPositiveEigenvector = 2 := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    ambientHalfGammaPositiveEigenvector, Fin.sum_univ_succ]
  norm_num

@[simp]
theorem ambientHalfGammaTransverseVector_self_pairing :
    ambientHalfSpinorHermitianPairing
        ambientHalfGammaTransverseVector
        ambientHalfGammaTransverseVector = 2 := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    ambientHalfGammaTransverseVector, Fin.sum_univ_succ]
  norm_num

theorem primitiveSpinCHopfZeroModeLocalCoordinate_self_eq_eight
    (period : Real) (hPeriod : period ≠ 0)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) =
      8 := by
  let matter :=
    primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point 0 chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector mode)
  let first := primitiveMonopoleZeroLocalValue chart point
  let second :=
    primitiveMonopoleZeroComplementLocalValue chart point
  have hNorm :
      star first * first + star second * second = 2 := by
    exact primitiveMonopoleZeroLocalValue_normSq_sum
      point chart hChart
  cases sector with
  | positiveQuarter =>
      have hMatter :
          d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
            ((first + second) • ambientHalfGammaPositiveEigenvector,
              (Complex.I * (first - second)) •
                ambientHalfGammaTransverseVector) := by
        simpa [matter, first, second, normalRootSpinFramePhase,
          normalRootSpinFramePhaseAngle] using
            primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
              period hPeriod point chart hChart mode 0
      calc
        d9DoubledMatterSpinorHermitianPairing matter matter =
            2 * (star (first + second) * (first + second) +
              star (Complex.I * (first - second)) *
                (Complex.I * (first - second))) :=
          d9DoubledMatterSpinorHermitianPairing_plane_self
            matter (first + second)
              (Complex.I * (first - second))
              ambientHalfGammaPositiveEigenvector
              ambientHalfGammaTransverseVector hMatter
              ambientHalfGammaPositiveEigenvector_self_pairing
              ambientHalfGammaTransverseVector_self_pairing
        _ = 8 := by
          simp only [Complex.star_def, map_add, map_sub, map_mul,
            Complex.conj_I]
          ring_nf
          rw [Complex.I_sq]
          simp only [starRingEnd_apply]
          linear_combination 4 * hNorm
  | negativeQuarter =>
      have hMatter :
          d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
            ((Complex.I * (second - first)) •
                ambientHalfGammaTransverseVector,
              (first + second) •
                ambientHalfGammaPositiveEigenvector) := by
        simpa [matter, first, second, normalRootSpinFramePhase,
          normalRootSpinFramePhaseAngle] using
            primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
              period hPeriod point chart hChart mode 0
      calc
        d9DoubledMatterSpinorHermitianPairing matter matter =
            2 * (star (Complex.I * (second - first)) *
                (Complex.I * (second - first)) +
              star (first + second) * (first + second)) :=
          d9DoubledMatterSpinorHermitianPairing_plane_self
            matter (Complex.I * (second - first))
              (first + second)
              ambientHalfGammaTransverseVector
              ambientHalfGammaPositiveEigenvector hMatter
              ambientHalfGammaTransverseVector_self_pairing
              ambientHalfGammaPositiveEigenvector_self_pairing
        _ = 8 := by
          simp only [Complex.star_def, map_add, map_sub, map_mul,
            Complex.conj_I]
          ring_nf
          rw [Complex.I_sq]
          simp only [starRingEnd_apply]
          linear_combination 4 * hNorm

/-- At witness time zero, two null powers in one sector have the scalar
sphere pairing times the exact Hopf-fiber norm eight. -/
theorem primitiveSpinCNullPowerLocalCoordinate_pairing_eq_eight_mul
    (period : Real) (hPeriod : period ≠ 0)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (firstParameter secondParameter : Complex)
    (sector : NormalRootChoice) (mode : Int)
    (firstDegree secondDegree : Nat) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullPowerSection
            period hPeriod firstParameter sector mode firstDegree))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullPowerSection
            period hPeriod secondParameter sector mode secondDegree)) =
      8 *
        star (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
        primitiveSpinCNullSpherePower
          secondDegree secondParameter point := by
  rw [
    primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
      period hPeriod point chart hChart 0 firstParameter,
    primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
      period hPeriod point chart hChart 0 secondParameter,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroModeLocalCoordinate_self_eq_eight
      period hPeriod point chart hChart sector mode]
  simp only [primitiveSpinCNullSpherePower, starRingEnd_apply]
  ring

/-- The time-zero local pairing of two raw vectors in one block has the
same exact scalar factorization. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_local_level_pairing_eq
    (period : Real) (hPeriod : period ≠ 0)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (firstLevel secondLevel : Nat)
    (sector : NormalRootChoice) (mode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector mode firstMultiplicity))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel sector mode secondMultiplicity)) =
      8 *
        star (primitiveSpinCNullSpherePower firstLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            firstLevel firstMultiplicity) point) *
        primitiveSpinCNullSpherePower secondLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            secondLevel secondMultiplicity) point := by
  let firstIndex : PrimitiveSpinCAllFullJointIndex :=
    ⟨(sector, mode), ⟨firstLevel, firstMultiplicity⟩⟩
  let secondIndex : PrimitiveSpinCAllFullJointIndex :=
    ⟨(sector, mode), ⟨secondLevel, secondMultiplicity⟩⟩
  change
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv firstIndex)))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv secondIndex))) =
      8 *
        star (primitiveSpinCNullSpherePower firstLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            firstLevel firstMultiplicity) point) *
        primitiveSpinCNullSpherePower secondLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            secondLevel secondMultiplicity) point
  rw [← primitiveSpinCAllFullJointFamily_eq_allMode,
    ← primitiveSpinCAllFullJointFamily_eq_allMode]
  exact primitiveSpinCNullPowerLocalCoordinate_pairing_eq_eight_mul
    period hPeriod point chart hChart
    (primitiveSpinCFullLevelNullGeometricParameter
      firstLevel firstMultiplicity)
    (primitiveSpinCFullLevelNullGeometricParameter
      secondLevel secondMultiplicity)
    sector mode firstLevel secondLevel

/-- The scalar level factorization is intrinsic and therefore independent
of the chosen monopole chart. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_pointwise_level_pairing_eq
    (period : Real) (hPeriod : period ≠ 0)
    (point : MonopoleSphere)
    (firstLevel secondLevel : Nat)
    (sector : NormalRootChoice) (mode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector mode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector mode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0) =
      8 *
        star (primitiveSpinCNullSpherePower firstLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            firstLevel firstMultiplicity) point) *
        primitiveSpinCNullSpherePower secondLevel
          (primitiveSpinCFullLevelNullGeometricParameter
            secondLevel secondMultiplicity) point := by
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  rw [d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point 0 chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point 0)
    (primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart 0)]
  exact
    primitiveSpinCGeometricL2RawBlockFamily_local_level_pairing_eq
      period hPeriod point chart hChart firstLevel secondLevel sector mode
      firstMultiplicity secondMultiplicity

/-- Raw multiplicity vectors at distinct sphere levels are orthogonal in
the independently integrated geometric L2 product. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
    (period : Real) (hPeriod : period ≠ 0)
    (firstLevel secondLevel : Nat) (hLevels : firstLevel ≠ secondLevel)
    (sector : NormalRootChoice) (mode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector mode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector mode secondMultiplicity) =
      0 := by
  rw [d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral]
  have hIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter
      (primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod firstLevel sector mode firstMultiplicity)
      (primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod secondLevel sector mode secondMultiplicity)
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hIntrinsic
  have hPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector mode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector mode secondMultiplicity)
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  unfold canonicalLatitudeBaseMeasure at hPullback ⊢
  rw [integral_prod _ hPullback]
  let timeMass : Complex :=
    ∫ time,
      (starRingEnd Complex)
          (normalRootSpinFrameExponential period sector mode time) *
        normalRootSpinFrameExponential period sector mode time
      ∂(volume.restrict (canonicalLatitudeTimeInterval period))
  calc
    _ = ∫ point,
          timeMass *
            (8 *
              star (primitiveSpinCNullSpherePower firstLevel
                (primitiveSpinCFullLevelNullGeometricParameter
                  firstLevel firstMultiplicity) point) *
              primitiveSpinCNullSpherePower secondLevel
                (primitiveSpinCFullLevelNullGeometricParameter
                  secondLevel secondMultiplicity) point)
          ∂SphereMeasure := by
      apply integral_congr_ae
      filter_upwards with point
      rw [show
          (fun time : Real =>
            d9PrimitiveSpinCPointwiseHermitianPairing
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod firstLevel sector mode firstMultiplicity)
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod secondLevel sector mode secondMultiplicity)
              (canonicalLatitudeThroatMap
                period hPeriod (point, time))) =
            fun time : Real =>
              ((starRingEnd Complex)
                  (normalRootSpinFrameExponential
                    period sector mode time) *
                normalRootSpinFrameExponential
                  period sector mode time) *
              d9PrimitiveSpinCPointwiseHermitianPairing
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricL2RawBlockFamily
                  period hPeriod firstLevel sector mode firstMultiplicity)
                (primitiveSpinCGeometricL2RawBlockFamily
                  period hPeriod secondLevel sector mode secondMultiplicity)
                (primitiveSpinCNullPacketMovingWitnessBase
                  period hPeriod point 0) by
        funext time
        rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
        exact
          primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor_all
            period hPeriod point firstLevel secondLevel sector mode mode
            firstMultiplicity secondMultiplicity time]
      rw [integral_mul_const,
        primitiveSpinCGeometricL2RawBlockFamily_pointwise_level_pairing_eq
          period hPeriod point firstLevel secondLevel sector mode
          firstMultiplicity secondMultiplicity]
    _ = (timeMass * 8) *
        (∫ point,
          star (primitiveSpinCNullSpherePower firstLevel
            (primitiveSpinCFullLevelNullGeometricParameter
              firstLevel firstMultiplicity) point) *
          primitiveSpinCNullSpherePower secondLevel
            (primitiveSpinCFullLevelNullGeometricParameter
              secondLevel secondMultiplicity) point
          ∂SphereMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with point
      ring
    _ = 0 := by
      rw [primitiveSpinCNullSpherePower_level_orthogonal
        firstLevel secondLevel
        (primitiveSpinCFullLevelNullGeometricParameter
          firstLevel firstMultiplicity)
        (primitiveSpinCFullLevelNullGeometricParameter
          secondLevel secondMultiplicity)
        hLevels]
      simp

/-- The complete finite multiplicity spans remain orthogonal across
distinct sphere levels in one sector and circle mode. -/
theorem primitiveSpinCGeometricL2RawBlockSpans_level_isOrtho
    (period : Real) (hPeriod : period ≠ 0)
    (firstLevel secondLevel : Nat) (hLevels : firstLevel ≠ secondLevel)
    (sector : NormalRootChoice) (mode : Int) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector mode)) ⟂
      Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel sector mode)) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨firstMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector mode firstMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨secondMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector mode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector mode
                secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
          period hPeriod firstLevel secondLevel hLevels sector mode
          firstMultiplicity secondMultiplicity
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

/-- Gram-Schmidt normalization preserves inter-level orthogonality. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockFamily_level_orthogonal
    (period : Real) (hPeriod : period ≠ 0)
    (firstLevel secondLevel : Nat) (hLevels : firstLevel ≠ secondLevel)
    (sector : NormalRootChoice) (mode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector mode firstMultiplicity)
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector mode secondMultiplicity) =
      0 := by
  have hFirst :
      primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector mode firstMultiplicity ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector mode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    exact Submodule.subset_span (Set.mem_range_self firstMultiplicity)
  have hSecond :
      primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector mode secondMultiplicity ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector mode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    exact Submodule.subset_span (Set.mem_range_self secondMultiplicity)
  have hOrthogonal :=
    (primitiveSpinCGeometricL2RawBlockSpans_level_isOrtho
      period hPeriod firstLevel secondLevel hLevels sector mode).inner_eq
        hFirst hSecond
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector mode firstMultiplicity)
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector mode secondMultiplicity) =
      0 at hOrthogonal
  exact hOrthogonal

/-- Arbitrary finite normalized block syntheses are orthogonal across
distinct sphere levels in one sector and circle mode. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockSynthesis_level_orthogonal
    (period : Real) (hPeriod : period ≠ 0)
    (firstLevel secondLevel : Nat) (hLevels : firstLevel ≠ secondLevel)
    (sector : NormalRootChoice) (mode : Int)
    (first :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy firstLevel)))
    (second :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy secondLevel))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector mode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector mode second) =
      0 := by
  have hFirst :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector mode first ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector mode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        first multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod firstLevel sector mode multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hSecond :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector mode second ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector mode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        second multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod secondLevel sector mode multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hOrthogonal :=
    (primitiveSpinCGeometricL2RawBlockSpans_level_isOrtho
      period hPeriod firstLevel secondLevel hLevels sector mode).inner_eq
        hFirst hSecond
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector mode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector mode second) =
      0 at hOrthogonal
  exact hOrthogonal

/-- Assumption-free certificate for geometric inter-level orthogonality. -/
structure ProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
    (period : Real) (hPeriod : period ≠ 0) where
  rawLevelOrthogonal :
    ∀ (firstLevel secondLevel : Nat), firstLevel ≠ secondLevel →
      ∀ (sector : NormalRootChoice) (mode : Int)
        (firstMultiplicity :
          Fin (primitiveSphereModeDegeneracy firstLevel))
        (secondMultiplicity :
          Fin (primitiveSphereModeDegeneracy secondLevel)),
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector mode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector mode secondMultiplicity) =
          0
  normalizedLevelOrthogonal :
    ∀ (firstLevel secondLevel : Nat), firstLevel ≠ secondLevel →
      ∀ (sector : NormalRootChoice) (mode : Int)
        (first :
          EuclideanSpace Complex
            (Fin (primitiveSphereModeDegeneracy firstLevel)))
        (second :
          EuclideanSpace Complex
            (Fin (primitiveSphereModeDegeneracy secondLevel))),
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod firstLevel sector mode first)
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod secondLevel sector mode second) =
          0

def programPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
    (period : Real) (hPeriod : period ≠ 0) :
    ProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
      period hPeriod where
  rawLevelOrthogonal :=
    primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
      period hPeriod
  normalizedLevelOrthogonal :=
    primitiveSpinCGeometricL2OrthonormalBlockSynthesis_level_orthogonal
      period hPeriod

theorem primitiveSpinCGeometricL2LevelOrthogonality_gate
    (period : Real) (hPeriod : period ≠ 0) :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
    period hPeriod⟩

end

end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
end JanusFormal
