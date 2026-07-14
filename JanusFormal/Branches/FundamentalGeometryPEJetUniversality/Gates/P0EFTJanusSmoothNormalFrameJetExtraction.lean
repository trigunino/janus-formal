import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalConnectionFromFrameJet

namespace JanusFormal
namespace P0EFTJanusSmoothNormalFrameJetExtraction

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusNormalConnectionFromFrameJet

universe u v w

variable {Base : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Base] [InnerProductSpace ℝ Base]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- A `C²` orthonormal normal-frame field represented by explicit first and
second Fréchet-derivative witnesses.

The target of `field` is the Banach space of continuous linear maps
`Normal →L Ambient`. The derivative fields are stored explicitly so that the
metric identities required by `OrthonormalNormalFrameTwoJet` can be derived from
ordinary Fréchet calculus rather than postulated independently. -/
structure SmoothOrthonormalNormalFrameTwoJetField
    (Base : Type u) (Normal : Type v) (Ambient : Type w)
    [NormedAddCommGroup Base] [InnerProductSpace ℝ Base]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient] where
  field : Base → Normal →L[ℝ] Ambient
  first : Base → Base →L[ℝ] Normal →L[ℝ] Ambient
  second : Base → Base →L[ℝ] Base →L[ℝ] Normal →L[ℝ] Ambient
  field_hasFDerivAt : ∀ base,
    HasFDerivAt field (first base) base
  first_hasFDerivAt : ∀ base,
    HasFDerivAt first (second base) base
  orthonormal : ∀ base firstNormal secondNormal,
    ⟪field base firstNormal, field base secondNormal⟫_ℝ =
      ⟪firstNormal, secondNormal⟫_ℝ

/-- Evaluation of the frame field on a fixed normal vector has the expected
Fréchet derivative. -/
theorem field_apply_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base : Base) (normal : Normal) :
    HasFDerivAt
      (fun point => frame.field point normal)
      ((frame.first base).flip normal)
      base := by
  simpa using
    (frame.field_hasFDerivAt base).clm_apply
      (hasFDerivAt_const normal base)

/-- Evaluation of the first derivative on a fixed tangent direction has the
expected derivative supplied by the second derivative field. -/
theorem first_direction_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base direction : Base) :
    HasFDerivAt
      (fun point => frame.first point direction)
      ((frame.second base).flip direction)
      base := by
  simpa using
    (frame.first_hasFDerivAt base).clm_apply
      (hasFDerivAt_const direction base)

/-- Evaluation of the first derivative on fixed tangent and normal vectors. -/
theorem first_direction_apply_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base direction : Base) (normal : Normal) :
    HasFDerivAt
      (fun point => frame.first point direction normal)
      (((frame.second base).flip direction).flip normal)
      base := by
  simpa using
    (first_direction_hasFDerivAt frame base direction).clm_apply
      (hasFDerivAt_const normal base)

/-- The first differentiated orthonormality identity is forced by the derivative
of the constant scalar pairing

`point ↦ ⟪E(point) ξ,E(point) η⟫`. -/
theorem first_metric_identity
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base direction : Base)
    (firstNormal secondNormal : Normal) :
    ⟪frame.first base direction firstNormal,
        frame.field base secondNormal⟫_ℝ +
      ⟪frame.field base firstNormal,
        frame.first base direction secondNormal⟫_ℝ = 0 := by
  let pairing : Base → ℝ := fun point =>
    ⟪frame.field point firstNormal,
      frame.field point secondNormal⟫_ℝ
  have hPairing : HasFDerivAt pairing
      ((fderivInnerCLM ℝ
          (frame.field base firstNormal,
            frame.field base secondNormal)).comp
        (((frame.first base).flip firstNormal).prod
          ((frame.first base).flip secondNormal))) base := by
    exact (field_apply_hasFDerivAt frame base firstNormal).inner ℝ
      (field_apply_hasFDerivAt frame base secondNormal)
  have hPairingConst : pairing = fun _ =>
      ⟪firstNormal, secondNormal⟫_ℝ := by
    funext point
    exact frame.orthonormal point firstNormal secondNormal
  have hZero : HasFDerivAt pairing (0 : Base →L[ℝ] ℝ) base := by
    rw [hPairingConst]
    exact hasFDerivAt_const _ _
  have hDerivative := hPairing.unique hZero
  have hAt := congrArg
    (fun derivative : Base →L[ℝ] ℝ => derivative direction)
    hDerivative
  change
    ⟪frame.field base firstNormal,
        frame.first base direction secondNormal⟫_ℝ +
      ⟪frame.first base direction firstNormal,
        frame.field base secondNormal⟫_ℝ = 0 at hAt
  simpa [add_comm] using hAt

/-- Scalar field obtained by differentiating orthonormality once in a fixed
base-space direction. -/
def firstMetricScalarField
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (direction : Base)
    (firstNormal secondNormal : Normal) : Base → ℝ :=
  (fun base =>
    ⟪frame.first base direction firstNormal,
      frame.field base secondNormal⟫_ℝ) +
  (fun base =>
    ⟪frame.field base firstNormal,
      frame.first base direction secondNormal⟫_ℝ)

/-- The first metric scalar field vanishes identically. -/
theorem firstMetricScalarField_eq_zero
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (direction : Base)
    (firstNormal secondNormal : Normal) :
    firstMetricScalarField frame direction firstNormal secondNormal = 0 := by
  funext base
  change
    ⟪frame.first base direction firstNormal,
        frame.field base secondNormal⟫_ℝ +
      ⟪frame.field base firstNormal,
        frame.first base direction secondNormal⟫_ℝ = 0
  exact first_metric_identity frame base direction
    firstNormal secondNormal

/-- The second differentiated orthonormality identity is obtained by
differentiating the first identity once more. The four terms are exactly the
Leibniz expansion required by `OrthonormalNormalFrameTwoJet.second_metric`. -/
theorem second_metric_identity
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base x y : Base)
    (firstNormal secondNormal : Normal) :
    ⟪frame.second base x y firstNormal,
        frame.field base secondNormal⟫_ℝ +
      ⟪frame.first base y firstNormal,
        frame.first base x secondNormal⟫_ℝ +
      ⟪frame.first base x firstNormal,
        frame.first base y secondNormal⟫_ℝ +
      ⟪frame.field base firstNormal,
        frame.second base x y secondNormal⟫_ℝ = 0 := by
  have hFirstTerm :=
    (first_direction_apply_hasFDerivAt frame base y firstNormal).inner ℝ
      (field_apply_hasFDerivAt frame base secondNormal)
  have hSecondTerm :=
    (field_apply_hasFDerivAt frame base firstNormal).inner ℝ
      (first_direction_apply_hasFDerivAt frame base y secondNormal)
  have hDerivative : HasFDerivAt
      (firstMetricScalarField frame y firstNormal secondNormal)
      (((fderivInnerCLM ℝ
          (frame.first base y firstNormal,
            frame.field base secondNormal)).comp
        ((((frame.second base).flip y).flip firstNormal).prod
          ((frame.first base).flip secondNormal))) +
       ((fderivInnerCLM ℝ
          (frame.field base firstNormal,
            frame.first base y secondNormal)).comp
        (((frame.first base).flip firstNormal).prod
          (((frame.second base).flip y).flip secondNormal))))
      base := by
    simpa only [firstMetricScalarField] using
      hFirstTerm.add hSecondTerm
  have hZero : HasFDerivAt
      (firstMetricScalarField frame y firstNormal secondNormal)
      (0 : Base →L[ℝ] ℝ) base := by
    rw [firstMetricScalarField_eq_zero]
    exact hasFDerivAt_const _ _
  have hUnique := hDerivative.unique hZero
  have hAt := congrArg
    (fun derivative : Base →L[ℝ] ℝ => derivative x)
    hUnique
  change
    (⟪frame.first base y firstNormal,
        frame.first base x secondNormal⟫_ℝ +
      ⟪frame.second base x y firstNormal,
        frame.field base secondNormal⟫_ℝ) +
    (⟪frame.field base firstNormal,
        frame.second base x y secondNormal⟫_ℝ +
      ⟪frame.first base x firstNormal,
        frame.first base y secondNormal⟫_ℝ) = 0 at hAt
  linarith

/-- The value of a smooth orthonormal frame field at a point, bundled as a
linear isometry. -/
def frameValueAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base : Base) : Normal →ₗᵢ[ℝ] Ambient where
  toLinearMap := (frame.field base).toLinearMap
  norm_map' normal := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    change ‖frame.field base normal‖ ^ 2 = ‖normal‖ ^ 2
    simpa only [real_inner_self_eq_norm_sq] using
      frame.orthonormal base normal normal

/-- Convert the continuous second derivative at one point to the nested algebraic
linear-map representation used by the local frame-two-jet gate. -/
def frameSecondLinearAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base : Base) :
    Base →ₗ[ℝ] Base →ₗ[ℝ] Normal →L[ℝ] Ambient where
  toFun := fun x => (frame.second base x).toLinearMap
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro y
    apply ContinuousLinearMap.ext
    intro normal
    simp
  map_smul' := by
    intro scalar x
    apply LinearMap.ext
    intro y
    apply ContinuousLinearMap.ext
    intro normal
    simp

/-- Actual extraction of the algebraic orthonormal normal-frame two-jet from a
smooth frame field with explicit Fréchet derivative witnesses. -/
def orthonormalNormalFrameTwoJetAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base : Base) :
    OrthonormalNormalFrameTwoJet Base Normal Ambient where
  value := frameValueAt frame base
  first := (frame.first base).toLinearMap
  second := frameSecondLinearAt frame base
  first_metric := first_metric_identity frame base
  second_metric := second_metric_identity frame base

/-- The extracted frame two-jet canonically produces the metric normal connection
one-jet used in the local curvature theorem. -/
def metricNormalConnectionOneJetAt
    [FiniteDimensional ℝ Base]
    [FiniteDimensional ℝ Normal]
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base : Base) : MetricNormalConnectionOneJet Base Normal :=
  metricNormalConnectionOneJetOfFrame
    (orthonormalNormalFrameTwoJetAt frame base)

/-- The coefficient obtained from the smooth frame is characterized directly by
its first Fréchet derivative. -/
theorem metricNormalConnectionOneJetAt_coefficient_inner
    [FiniteDimensional ℝ Base]
    [FiniteDimensional ℝ Normal]
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base x : Base) (firstNormal secondNormal : Normal) :
    ⟪(metricNormalConnectionOneJetAt frame base).coefficient x firstNormal,
      secondNormal⟫_ℝ =
      ⟪frame.first base x firstNormal,
        frame.field base secondNormal⟫_ℝ := by
  exact frameNormalConnectionCoefficient_inner
    (orthonormalNormalFrameTwoJetAt frame base)
    x firstNormal secondNormal

/-- The coefficient derivative obtained from the smooth frame is characterized
by the second Fréchet derivative and the quadratic first-derivative correction. -/
theorem metricNormalConnectionOneJetAt_derivative_inner
    [FiniteDimensional ℝ Base]
    [FiniteDimensional ℝ Normal]
    (frame : SmoothOrthonormalNormalFrameTwoJetField Base Normal Ambient)
    (base x y : Base) (firstNormal secondNormal : Normal) :
    ⟪(metricNormalConnectionOneJetAt frame base).derivative x y firstNormal,
      secondNormal⟫_ℝ =
      ⟪frame.second base x y firstNormal,
        frame.field base secondNormal⟫_ℝ +
      ⟪frame.first base y firstNormal,
        frame.first base x secondNormal⟫_ℝ := by
  exact frameNormalConnectionDerivative_inner
    (orthonormalNormalFrameTwoJetAt frame base)
    x y firstNormal secondNormal

/-- Exact boundary after extracting a flat-chart frame two-jet from smooth data. -/
structure SmoothNormalFrameJetExtractionStatus where
  clmValuedFrameFieldDefined : Prop
  firstFrechetDerivativeWitnessed : Prop
  secondFrechetDerivativeWitnessed : Prop
  pointwiseOrthonormalityStored : Prop
  firstMetricIdentityDerived : Prop
  secondMetricIdentityDerived : Prop
  orthonormalFrameTwoJetExtracted : Prop
  metricNormalConnectionJetExtracted : Prop
  ambientCovariantDerivativeInserted : Prop
  manifoldChartCompatibilityProved : Prop
  smoothOverlapGaugeJetExtracted : Prop
  globalNormalConnectionDescended : Prop

/-- Closure of the smooth-frame extraction stage. -/
def smoothNormalFrameJetExtractionClosed
    (s : SmoothNormalFrameJetExtractionStatus) : Prop :=
  s.clmValuedFrameFieldDefined /\
  s.firstFrechetDerivativeWitnessed /\
  s.secondFrechetDerivativeWitnessed /\
  s.pointwiseOrthonormalityStored /\
  s.firstMetricIdentityDerived /\
  s.secondMetricIdentityDerived /\
  s.orthonormalFrameTwoJetExtracted /\
  s.metricNormalConnectionJetExtracted /\
  s.ambientCovariantDerivativeInserted /\
  s.manifoldChartCompatibilityProved /\
  s.smoothOverlapGaugeJetExtracted /\
  s.globalNormalConnectionDescended

/-- Flat Fréchet derivatives still have to be replaced by ambient covariant
derivatives before the extracted jet is the genuine manifold normal connection. -/
theorem missing_ambient_covariant_derivative_blocks_geometric_extraction
    (s : SmoothNormalFrameJetExtractionStatus)
    (hMissing : Not s.ambientCovariantDerivativeInserted) :
    Not (smoothNormalFrameJetExtractionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusSmoothNormalFrameJetExtraction
end JanusFormal
