import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D

/-!
# Intrinsic Levi--Civita Bianchi identity

This gate packages the local Levi--Civita coefficients as endomorphism-valued
connection coefficients and proves the covariant second Bianchi identity
directly from Schwarz symmetry and the noncommutative Jacobi identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev Endomorphism4 := Vector4 →L[Real] Vector4

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

section AbstractConnection

variable {A : Type*} [NormedRing A] [NormedAlgebra Real A]

/-- Constant-coordinate directional derivative of an algebra-valued field. -/
def algebraDirectionalDerivative
    (field : Vector4 → A) (coordinate : Vector4)
    (direction : Index4) : A :=
  fderiv Real field coordinate (coordinateBasisVector direction)

/-- Curvature of an algebra-valued connection in a coordinate frame. -/
def algebraConnectionCurvature
    (connection : Vector4 → Index4 → A)
    (coordinate : Vector4) (first second : Index4) : A :=
  algebraDirectionalDerivative (fun current => connection current second)
      coordinate first -
    algebraDirectionalDerivative (fun current => connection current first)
      coordinate second +
    connection coordinate first * connection coordinate second -
    connection coordinate second * connection coordinate first

/-- Covariant derivative of an arbitrary endomorphism-valued two-form. -/
def algebraCovariantTwoFormDerivative
    (connection : Vector4 → Index4 → A)
    (curvature : Vector4 → Index4 → Index4 → A)
    (coordinate : Vector4)
    (derivative first second : Index4) : A :=
  algebraDirectionalDerivative
      (fun current => curvature current first second)
      coordinate derivative +
    connection coordinate derivative * curvature coordinate first second -
    curvature coordinate first second * connection coordinate derivative

/-- Covariant derivative of curvature in the endomorphism algebra. -/
def algebraCovariantCurvatureDerivative
    (connection : Vector4 → Index4 → A)
    (coordinate : Vector4)
    (derivative first second : Index4) : A :=
  algebraCovariantTwoFormDerivative connection
    (fun current first second =>
      algebraConnectionCurvature connection current first second)
    coordinate derivative first second

/-- Cyclic covariant derivative of an arbitrary endomorphism-valued
two-form. -/
def algebraBianchiDifferential
    (connection : Vector4 → Index4 → A)
    (curvature : Vector4 → Index4 → Index4 → A)
    (coordinate : Vector4) (first second third : Index4) : A :=
  algebraCovariantTwoFormDerivative connection curvature coordinate
      first second third +
    algebraCovariantTwoFormDerivative connection curvature coordinate
      second third first +
    algebraCovariantTwoFormDerivative connection curvature coordinate
      third first second

private theorem algebraDirectionalDerivative_add
    {first second : Vector4 → A} {coordinate : Vector4}
    (direction : Index4)
    (hFirst : DifferentiableAt Real first coordinate)
    (hSecond : DifferentiableAt Real second coordinate) :
    algebraDirectionalDerivative (first + second) coordinate direction =
      algebraDirectionalDerivative first coordinate direction +
        algebraDirectionalDerivative second coordinate direction := by
  unfold algebraDirectionalDerivative
  exact congrArg
    (fun derivative => derivative (coordinateBasisVector direction))
    (fderiv_add hFirst hSecond)

private theorem algebraDirectionalDerivative_sub
    {first second : Vector4 → A} {coordinate : Vector4}
    (direction : Index4)
    (hFirst : DifferentiableAt Real first coordinate)
    (hSecond : DifferentiableAt Real second coordinate) :
    algebraDirectionalDerivative (first - second) coordinate direction =
      algebraDirectionalDerivative first coordinate direction -
        algebraDirectionalDerivative second coordinate direction := by
  unfold algebraDirectionalDerivative
  exact congrArg
    (fun derivative => derivative (coordinateBasisVector direction))
    (fderiv_sub hFirst hSecond)

private theorem algebraDirectionalDerivative_mul
    {first second : Vector4 → A} {coordinate : Vector4}
    (direction : Index4)
    (hFirst : DifferentiableAt Real first coordinate)
    (hSecond : DifferentiableAt Real second coordinate) :
    algebraDirectionalDerivative (first * second) coordinate direction =
      algebraDirectionalDerivative first coordinate direction *
          second coordinate +
        first coordinate *
          algebraDirectionalDerivative second coordinate direction := by
  unfold algebraDirectionalDerivative
  have hDerivative :=
    congrArg (fun derivative =>
      derivative (coordinateBasisVector direction))
      (fderiv_mul' hFirst hSecond)
  simpa only [add_apply, smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul, op_smul_eq_mul, add_comm] using hDerivative

private theorem algebraDirectionalDerivative_commutes
    (field : Vector4 → A)
    (hField : ContDiff Real ∞ field)
    (coordinate : Vector4) (first second : Index4) :
    algebraDirectionalDerivative
        (fun current =>
          algebraDirectionalDerivative field current second)
        coordinate first =
      algebraDirectionalDerivative
        (fun current =>
          algebraDirectionalDerivative field current first)
        coordinate second := by
  unfold algebraDirectionalDerivative
  have hFDeriv :
      DifferentiableAt Real (fderiv Real field) coordinate :=
    ((hField.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp)) coordinate
  have hApply (direction : Index4) :
      fderiv Real
          (fun current =>
            fderiv Real field current (coordinateBasisVector direction))
          coordinate =
        (fderiv Real (fderiv Real field) coordinate).flip
          (coordinateBasisVector direction) := by
    rw [fderiv_clm_apply hFDeriv (differentiableAt_const _)]
    simp
  rw [hApply second, hApply first]
  have hSmooth :
      minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (hField.contDiffAt.isSymmSndFDerivAt hSmooth).eq
      (coordinateBasisVector first) (coordinateBasisVector second)

private theorem algebraConnectionCurvature_directionalDerivative
    (connection : Vector4 → Index4 → A)
    (hConnection : ∀ index, ContDiff Real ∞
      (fun coordinate => connection coordinate index))
    (coordinate : Vector4) (derivative first second : Index4) :
    algebraDirectionalDerivative
        (fun current =>
          algebraConnectionCurvature connection current first second)
        coordinate derivative =
      algebraDirectionalDerivative
          (fun current =>
            algebraDirectionalDerivative
              (fun point => connection point second) current first)
          coordinate derivative -
        algebraDirectionalDerivative
          (fun current =>
            algebraDirectionalDerivative
              (fun point => connection point first) current second)
          coordinate derivative +
        (algebraDirectionalDerivative
            (fun current => connection current first)
            coordinate derivative *
              connection coordinate second +
          connection coordinate first *
            algebraDirectionalDerivative
              (fun current => connection current second)
              coordinate derivative) -
        (algebraDirectionalDerivative
            (fun current => connection current second)
            coordinate derivative *
              connection coordinate first +
          connection coordinate second *
            algebraDirectionalDerivative
              (fun current => connection current first)
              coordinate derivative) := by
  unfold algebraConnectionCurvature
  have hDiff (index : Index4) :
      Differentiable Real (fun current => connection current index) :=
    (hConnection index).differentiable (by simp)
  have hDiffDerivative (direction index : Index4) :
      Differentiable Real (fun current =>
        algebraDirectionalDerivative
          (fun point => connection point index) current direction) :=
    ((hConnection index).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const |>.differentiable (by simp)
  have hFirstDerivative :
      DifferentiableAt Real
        (fun current =>
          algebraDirectionalDerivative
            (fun point => connection point second) current first)
        coordinate :=
    hDiffDerivative first second coordinate
  have hSecondDerivative :
      DifferentiableAt Real
        (fun current =>
          algebraDirectionalDerivative
            (fun point => connection point first) current second)
        coordinate :=
    hDiffDerivative second first coordinate
  have hFirstProduct :
      DifferentiableAt Real
        ((fun current => connection current first) *
          (fun current => connection current second))
        coordinate :=
    (hDiff first coordinate).mul (hDiff second coordinate)
  have hSecondProduct :
      DifferentiableAt Real
        ((fun current => connection current second) *
          (fun current => connection current first))
        coordinate :=
    (hDiff second coordinate).mul (hDiff first coordinate)
  change algebraDirectionalDerivative
      (((fun current =>
          algebraDirectionalDerivative
            (fun point => connection point second) current first) -
        (fun current =>
          algebraDirectionalDerivative
            (fun point => connection point first) current second)) +
        ((fun current => connection current first) *
          (fun current => connection current second)) -
        ((fun current => connection current second) *
          (fun current => connection current first)))
      coordinate derivative = _
  rw [algebraDirectionalDerivative_sub derivative
    ((hFirstDerivative.sub hSecondDerivative).add hFirstProduct)
    hSecondProduct]
  rw [algebraDirectionalDerivative_add derivative
    (hFirstDerivative.sub hSecondDerivative) hFirstProduct]
  rw [algebraDirectionalDerivative_sub derivative
    hFirstDerivative hSecondDerivative]
  rw [algebraDirectionalDerivative_mul derivative
    (hDiff first coordinate) (hDiff second coordinate)]
  rw [algebraDirectionalDerivative_mul derivative
    (hDiff second coordinate) (hDiff first coordinate)]

/-- Algebraic second Bianchi identity for every smooth connection. -/
theorem algebraConnection_secondBianchi
    (connection : Vector4 → Index4 → A)
    (hConnection : ∀ index, ContDiff Real ∞
      (fun coordinate => connection coordinate index))
    (coordinate : Vector4) (first second third : Index4) :
    algebraCovariantCurvatureDerivative connection coordinate
          first second third +
        algebraCovariantCurvatureDerivative connection coordinate
          second third first +
        algebraCovariantCurvatureDerivative connection coordinate
          third first second =
      0 := by
  unfold algebraCovariantCurvatureDerivative
    algebraCovariantTwoFormDerivative
  rw [algebraConnectionCurvature_directionalDerivative connection hConnection
      coordinate first second third]
  rw [algebraConnectionCurvature_directionalDerivative connection hConnection
      coordinate second third first]
  rw [algebraConnectionCurvature_directionalDerivative connection hConnection
      coordinate third first second]
  have h₁ :=
    algebraDirectionalDerivative_commutes
      (fun point => connection point third) (hConnection third)
      coordinate first second
  have h₂ :=
    algebraDirectionalDerivative_commutes
      (fun point => connection point first) (hConnection first)
      coordinate second third
  have h₃ :=
    algebraDirectionalDerivative_commutes
      (fun point => connection point second) (hConnection second)
      coordinate third first
  unfold algebraConnectionCurvature
  rw [h₁, h₂, h₃]
  noncomm_ring

/-- The Bianchi differential annihilates the curvature of the same smooth
connection. -/
theorem algebraBianchiDifferential_connectionCurvature_eq_zero
    (connection : Vector4 → Index4 → A)
    (hConnection : ∀ index, ContDiff Real ∞
      (fun coordinate => connection coordinate index))
    (coordinate : Vector4) (first second third : Index4) :
    algebraBianchiDifferential connection
        (fun current left right =>
          algebraConnectionCurvature connection current left right)
        coordinate first second third = 0 := by
  simpa [algebraBianchiDifferential, algebraCovariantCurvatureDerivative] using
    algebraConnection_secondBianchi connection hConnection coordinate
      first second third

end AbstractConnection

variable (period : Real) (hPeriod : period ≠ 0)

/-- Matrix-valued Levi--Civita coefficient in one genuine Janus chart. -/
def localLeviCivitaConnectionMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction : Index4) : Matrix4 :=
  fun upper lower =>
    localLeviCivitaChristoffel period hPeriod metric patch coordinate
      upper direction lower

/-- The same coefficient acting on the actual four-dimensional tangent
coordinate model. -/
def localLeviCivitaConnectionEndomorphism
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (direction : Index4) : Endomorphism4 :=
  LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin
      (localLeviCivitaConnectionMatrix period hPeriod metric patch
        coordinate direction))

@[simp]
theorem localLeviCivitaConnectionEndomorphism_basis_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (direction upper lower : Index4) :
    localLeviCivitaConnectionEndomorphism period hPeriod metric patch
        coordinate direction (coordinateBasisVector lower) upper =
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
        upper direction lower := by
  simp [localLeviCivitaConnectionEndomorphism,
    localLeviCivitaConnectionMatrix, coordinateBasisVector,
    Matrix.mulVec]

theorem localLeviCivitaConnectionEndomorphism_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (direction : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localLeviCivitaConnectionEndomorphism period hPeriod metric patch
        coordinate direction) := by
  rw [contDiff_clm_apply_iff]
  intro vector
  apply contDiff_pi.mpr
  intro upper
  change ContDiff Real ∞ (fun coordinate =>
    ∑ lower : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper direction lower * vector lower)
  apply ContDiff.sum
  intro lower _
  exact
    (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
      upper direction lower).mul contDiff_const

/-- Intrinsic local Riemann endomorphism computed from the genuine
Levi--Civita connection. -/
def localLeviCivitaRiemannEndomorphism
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) : Endomorphism4 :=
  algebraConnectionCurvature
    (localLeviCivitaConnectionEndomorphism period hPeriod metric patch)
    coordinate first second

/-- The genuine local Levi--Civita curvature as an
endomorphism-valued two-form. -/
def localLeviCivitaCurvatureField
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Vector4 → Index4 → Index4 → Endomorphism4 :=
  fun coordinate first second =>
    localLeviCivitaRiemannEndomorphism period hPeriod metric patch coordinate
      first second

/-- Bianchi differential on an arbitrary local curvature presentation. -/
def localLeviCivitaBianchiDifferential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (curvature : Vector4 → Index4 → Index4 → Endomorphism4)
    (coordinate : Vector4)
    (first second third : Index4) : Endomorphism4 :=
  algebraBianchiDifferential
    (localLeviCivitaConnectionEndomorphism period hPeriod metric patch)
    curvature coordinate first second third

/-- Genuine local Bianchi operator, including all connection-curvature
commutators. -/
def localLeviCivitaBianchiOperator
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second third : Index4) : Endomorphism4 :=
  localLeviCivitaBianchiDifferential period hPeriod metric patch
    (localLeviCivitaCurvatureField period hPeriod metric patch)
    coordinate first second third

/-- The genuine chartwise Levi--Civita curvature satisfies the covariant
second Bianchi identity. -/
@[simp]
theorem localLeviCivitaBianchiOperator_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second third : Index4) :
    localLeviCivitaBianchiOperator period hPeriod metric patch coordinate
      first second third = 0 := by
  exact algebraBianchiDifferential_connectionCurvature_eq_zero
    (localLeviCivitaConnectionEndomorphism period hPeriod metric patch)
    (localLeviCivitaConnectionEndomorphism_contDiff
      period hPeriod metric patch)
    coordinate first second third

end
end P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D
end JanusFormal
