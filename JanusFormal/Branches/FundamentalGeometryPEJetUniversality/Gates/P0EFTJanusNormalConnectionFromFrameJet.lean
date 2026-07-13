import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMetricNormalConnectionCurvature

namespace JanusFormal
namespace P0EFTJanusNormalConnectionFromFrameJet

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusMetricNormalConnectionCurvature

universe u v w

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- Two-jet at one point of a normal orthonormal frame

`E : N -> Ambient`.

`first x` is `d_x E`, and `second x y` is `d_x d_y E`. The two metric identities
are the first and second derivatives of

`<E xi,E eta> = <xi,eta>`.

The ambient connection is flat in this coefficient model. In a curved ambient
chart the derivatives below must be replaced by covariant derivatives. -/
structure OrthonormalNormalFrameTwoJet
    (Tangent : Type u) (Normal : Type v) (Ambient : Type w)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient] where
  value : Normal →ₗᵢ[ℝ] Ambient
  first : Tangent →ₗ[ℝ] Normal →L[ℝ] Ambient
  second : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] Normal →L[ℝ] Ambient
  first_metric : ∀ x firstNormal secondNormal,
    ⟪first x firstNormal, value secondNormal⟫_ℝ +
      ⟪value firstNormal, first x secondNormal⟫_ℝ = 0
  second_metric : ∀ x y firstNormal secondNormal,
    ⟪second x y firstNormal, value secondNormal⟫_ℝ +
      ⟪first y firstNormal, first x secondNormal⟫_ℝ +
      ⟪first x firstNormal, first y secondNormal⟫_ℝ +
      ⟪value firstNormal, second x y secondNormal⟫_ℝ = 0

/-- Algebraic bilinear form defining the normal connection coefficient:

`b_x(xi,eta) = <d_x E(xi), E(eta)>`. -/
def frameConnectionCoefficientBilinearLinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) : Normal →ₗ[ℝ] Normal →ₗ[ℝ] ℝ where
  toFun := fun firstNormal =>
    { toFun := fun secondNormal =>
        ⟪frame.first x firstNormal, frame.value secondNormal⟫_ℝ
      map_add' := by
        intro first second
        rw [map_add, inner_add_right]
      map_smul' := by
        intro scalar normal
        simp }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro normal
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_left]
  map_smul' := by
    intro scalar normal
    apply LinearMap.ext
    intro secondNormal
    simp

/-- Continuous bilinear coefficient form. Finite dimensionality of the normal
model supplies continuity. -/
def frameConnectionCoefficientBilinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) : Normal →L[ℝ] Normal →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    (frameConnectionCoefficientBilinearLinear frame x)

@[simp]
theorem frameConnectionCoefficientBilinear_apply
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) (firstNormal secondNormal : Normal) :
    frameConnectionCoefficientBilinear frame x firstNormal secondNormal =
      ⟪frame.first x firstNormal, frame.value secondNormal⟫_ℝ := by
  rfl

/-- Riesz representation of the normal connection coefficient `omega_x`. -/
def frameNormalConnectionCoefficient
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) : Normal →L[ℝ] Normal :=
  InnerProductSpace.continuousLinearMapOfBilin
    (frameConnectionCoefficientBilinear frame x)

/-- Characterizing coefficient identity. -/
@[simp]
theorem frameNormalConnectionCoefficient_inner
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) (firstNormal secondNormal : Normal) :
    ⟪frameNormalConnectionCoefficient frame x firstNormal,
      secondNormal⟫_ℝ =
      ⟪frame.first x firstNormal, frame.value secondNormal⟫_ℝ := by
  change
    ⟪InnerProductSpace.continuousLinearMapOfBilin
        (frameConnectionCoefficientBilinear frame x) firstNormal,
      secondNormal⟫_ℝ = _
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- The differentiated orthonormality identity makes `omega_x` skew-adjoint. -/
theorem frameNormalConnectionCoefficient_skew
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) :
    IsSkewAdjointOperator (frameNormalConnectionCoefficient frame x) := by
  intro firstNormal secondNormal
  calc
    ⟪frameNormalConnectionCoefficient frame x firstNormal,
        secondNormal⟫_ℝ =
      ⟪frame.first x firstNormal, frame.value secondNormal⟫_ℝ :=
      frameNormalConnectionCoefficient_inner frame x firstNormal secondNormal
    _ = -⟪frame.value firstNormal, frame.first x secondNormal⟫_ℝ := by
      linarith [frame.first_metric x firstNormal secondNormal]
    _ = -⟪frame.first x secondNormal, frame.value firstNormal⟫_ℝ := by
      rw [real_inner_comm]
    _ = -⟪frameNormalConnectionCoefficient frame x secondNormal,
        firstNormal⟫_ℝ := by
      rw [frameNormalConnectionCoefficient_inner]
    _ = -⟪firstNormal,
        frameNormalConnectionCoefficient frame x secondNormal⟫_ℝ := by
      rw [real_inner_comm]

/-- Additivity of the connection coefficient in the tangent direction. -/
theorem frameNormalConnectionCoefficient_add_direction
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (first second : Tangent) :
    frameNormalConnectionCoefficient frame (first + second) =
      frameNormalConnectionCoefficient frame first +
        frameNormalConnectionCoefficient frame second := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_add_left]

/-- Homogeneity of the connection coefficient in the tangent direction. -/
theorem frameNormalConnectionCoefficient_smul_direction
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (scalar : ℝ) (x : Tangent) :
    frameNormalConnectionCoefficient frame (scalar • x) =
      scalar • frameNormalConnectionCoefficient frame x := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_smul_left]

/-- The connection coefficients form a tangent one-form with values in normal
endomorphisms. -/
def frameNormalConnectionCoefficientLinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient) :
    Tangent →ₗ[ℝ] Normal →L[ℝ] Normal where
  toFun := frameNormalConnectionCoefficient frame
  map_add' := frameNormalConnectionCoefficient_add_direction frame
  map_smul' := frameNormalConnectionCoefficient_smul_direction frame

/-- Bilinear scalar form defining `partial_x omega_y`:

`<partial_x omega_y xi,eta>
  = <d_x d_y E(xi),E(eta)> + <d_y E(xi),d_x E(eta)>`. -/
def frameConnectionDerivativeBilinearLinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) : Normal →ₗ[ℝ] Normal →ₗ[ℝ] ℝ where
  toFun := fun firstNormal =>
    { toFun := fun secondNormal =>
        ⟪frame.second x y firstNormal, frame.value secondNormal⟫_ℝ +
          ⟪frame.first y firstNormal, frame.first x secondNormal⟫_ℝ
      map_add' := by
        intro first second
        simp [inner_add_right]
      map_smul' := by
        intro scalar normal
        simp [inner_smul_right] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro normal
    simp [inner_add_left]
  map_smul' := by
    intro scalar normal
    apply LinearMap.ext
    intro secondNormal
    simp [inner_smul_left]

/-- Continuous bilinear derivative form. -/
def frameConnectionDerivativeBilinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) : Normal →L[ℝ] Normal →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    (frameConnectionDerivativeBilinearLinear frame x y)

@[simp]
theorem frameConnectionDerivativeBilinear_apply
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    frameConnectionDerivativeBilinear frame x y firstNormal secondNormal =
      ⟪frame.second x y firstNormal, frame.value secondNormal⟫_ℝ +
        ⟪frame.first y firstNormal, frame.first x secondNormal⟫_ℝ := by
  rfl

/-- Riesz representation of the first derivative `partial_x omega_y`. -/
def frameNormalConnectionDerivative
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) : Normal →L[ℝ] Normal :=
  InnerProductSpace.continuousLinearMapOfBilin
    (frameConnectionDerivativeBilinear frame x y)

/-- Characterizing derivative identity. -/
@[simp]
theorem frameNormalConnectionDerivative_inner
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    ⟪frameNormalConnectionDerivative frame x y firstNormal,
      secondNormal⟫_ℝ =
      ⟪frame.second x y firstNormal, frame.value secondNormal⟫_ℝ +
        ⟪frame.first y firstNormal, frame.first x secondNormal⟫_ℝ := by
  change
    ⟪InnerProductSpace.continuousLinearMapOfBilin
        (frameConnectionDerivativeBilinear frame x y) firstNormal,
      secondNormal⟫_ℝ = _
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- The twice-differentiated orthonormality identity makes every
`partial_x omega_y` skew-adjoint. -/
theorem frameNormalConnectionDerivative_skew
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) :
    IsSkewAdjointOperator (frameNormalConnectionDerivative frame x y) := by
  intro firstNormal secondNormal
  calc
    ⟪frameNormalConnectionDerivative frame x y firstNormal,
        secondNormal⟫_ℝ =
      ⟪frame.second x y firstNormal, frame.value secondNormal⟫_ℝ +
        ⟪frame.first y firstNormal, frame.first x secondNormal⟫_ℝ :=
      frameNormalConnectionDerivative_inner frame x y
        firstNormal secondNormal
    _ = -(
        ⟪frame.value firstNormal, frame.second x y secondNormal⟫_ℝ +
          ⟪frame.first x firstNormal, frame.first y secondNormal⟫_ℝ) := by
      linarith [frame.second_metric x y firstNormal secondNormal]
    _ = -(
        ⟪frame.second x y secondNormal, frame.value firstNormal⟫_ℝ +
          ⟪frame.first y secondNormal, frame.first x firstNormal⟫_ℝ) := by
      rw [real_inner_comm (frame.value firstNormal)
          (frame.second x y secondNormal),
        real_inner_comm (frame.first x firstNormal)
          (frame.first y secondNormal)]
    _ = -⟪frameNormalConnectionDerivative frame x y secondNormal,
        firstNormal⟫_ℝ := by
      rw [frameNormalConnectionDerivative_inner]
    _ = -⟪firstNormal,
        frameNormalConnectionDerivative frame x y secondNormal⟫_ℝ := by
      rw [real_inner_comm]

/-- Additivity in the second tangent direction. -/
theorem frameNormalConnectionDerivative_add_second
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x first second : Tangent) :
    frameNormalConnectionDerivative frame x (first + second) =
      frameNormalConnectionDerivative frame x first +
        frameNormalConnectionDerivative frame x second := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_add_left, inner_add_right]
  ring

/-- Homogeneity in the second tangent direction. -/
theorem frameNormalConnectionDerivative_smul_second
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) (scalar : ℝ) (y : Tangent) :
    frameNormalConnectionDerivative frame x (scalar • y) =
      scalar • frameNormalConnectionDerivative frame x y := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_smul_left, inner_smul_right]
  ring

/-- Additivity in the first tangent direction. -/
theorem frameNormalConnectionDerivative_add_first
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (first second y : Tangent) :
    frameNormalConnectionDerivative frame (first + second) y =
      frameNormalConnectionDerivative frame first y +
        frameNormalConnectionDerivative frame second y := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_add_left, inner_add_right]
  ring

/-- Homogeneity in the first tangent direction. -/
theorem frameNormalConnectionDerivative_smul_first
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (scalar : ℝ) (x y : Tangent) :
    frameNormalConnectionDerivative frame (scalar • x) y =
      scalar • frameNormalConnectionDerivative frame x y := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  simp [inner_smul_left, inner_smul_right]
  ring

/-- The first derivatives of the connection coefficient form a bilinear tangent
map. -/
def frameNormalConnectionDerivativeLinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient) :
    Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] Normal →L[ℝ] Normal where
  toFun := fun x =>
    { toFun := frameNormalConnectionDerivative frame x
      map_add' := frameNormalConnectionDerivative_add_second frame x
      map_smul' := frameNormalConnectionDerivative_smul_second frame x }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro y
    exact frameNormalConnectionDerivative_add_first frame first second y
  map_smul' := by
    intro scalar x
    apply LinearMap.ext
    intro y
    exact frameNormalConnectionDerivative_smul_first frame scalar x y

/-- The normal-frame two-jet canonically produces the metric normal-connection
one-jet required by the curvature/Ricci theorem. -/
def metricNormalConnectionOneJetOfFrame
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient) :
    MetricNormalConnectionOneJet Tangent Normal where
  coefficient := frameNormalConnectionCoefficientLinear frame
  derivative := frameNormalConnectionDerivativeLinear frame
  coefficient_skew := frameNormalConnectionCoefficient_skew frame
  derivative_skew := frameNormalConnectionDerivative_skew frame

@[simp]
theorem metricNormalConnectionOneJetOfFrame_coefficient
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x : Tangent) :
    (metricNormalConnectionOneJetOfFrame frame).coefficient x =
      frameNormalConnectionCoefficient frame x := by
  rfl

@[simp]
theorem metricNormalConnectionOneJetOfFrame_derivative
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (x y : Tangent) :
    (metricNormalConnectionOneJetOfFrame frame).derivative x y =
      frameNormalConnectionDerivative frame x y := by
  rfl

/-- The frame two-jet therefore produces a normal curvature and a derived Ricci
identity through the preceding metric-connection theorem. -/
theorem normalFrameTwoJet_satisfies_Ricci
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (form : P0EFTJanusRieszShapeOperator.FiniteSecondFundamentalForm
      Tangent Normal) :
    P0EFTJanusRicciNormalEquation.SatisfiesRicciNormalEquation
      (normalConnectionCurvatureScalar
        (metricNormalConnectionOneJetOfFrame frame))
      (splitAmbientMixedCurvatureScalar
        (metricNormalConnectionOneJetOfFrame frame) form)
      (P0EFTJanusRieszShapeOperator.rieszShapeOperatorData form) :=
  metricNormalConnection_satisfies_Ricci
    (metricNormalConnectionOneJetOfFrame frame) form

/-- Exact progress boundary after extracting the metric normal connection from
an orthonormal frame two-jet. -/
structure NormalConnectionFromFrameStatus where
  orthonormalNormalFrameTwoJetDefined : Prop
  firstMetricIdentityEncoded : Prop
  secondMetricIdentityEncoded : Prop
  connectionCoefficientExtractedByRiesz : Prop
  coefficientSkewAdjointnessDerived : Prop
  connectionDerivativeExtractedByRiesz : Prop
  derivativeSkewAdjointnessDerived : Prop
  metricNormalConnectionJetConstructed : Prop
  ricciEquationDerivedFromFrameJet : Prop
  frameJetExtractedFromSmoothNormalFrame : Prop
  ambientCovariantDerivativeInserted : Prop
  varyingFrameGaugeLawProved : Prop
  smoothBundleCompatibilityProved : Prop

/-- Closure of the genuine manifold frame-to-connection stage. -/
def normalConnectionFromFrameClosed
    (s : NormalConnectionFromFrameStatus) : Prop :=
  s.orthonormalNormalFrameTwoJetDefined /\
  s.firstMetricIdentityEncoded /\
  s.secondMetricIdentityEncoded /\
  s.connectionCoefficientExtractedByRiesz /\
  s.coefficientSkewAdjointnessDerived /\
  s.connectionDerivativeExtractedByRiesz /\
  s.derivativeSkewAdjointnessDerived /\
  s.metricNormalConnectionJetConstructed /\
  s.ricciEquationDerivedFromFrameJet /\
  s.frameJetExtractedFromSmoothNormalFrame /\
  s.ambientCovariantDerivativeInserted /\
  s.varyingFrameGaugeLawProved /\
  s.smoothBundleCompatibilityProved

/-- The algebraic frame two-jet still has to be obtained from the smooth normal
frame constructed earlier in the program. -/
theorem missing_smooth_frame_jet_blocks_manifold_connection
    (s : NormalConnectionFromFrameStatus)
    (hMissing : Not s.frameJetExtractedFromSmoothNormalFrame) :
    Not (normalConnectionFromFrameClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalConnectionFromFrameJet
end JanusFormal
