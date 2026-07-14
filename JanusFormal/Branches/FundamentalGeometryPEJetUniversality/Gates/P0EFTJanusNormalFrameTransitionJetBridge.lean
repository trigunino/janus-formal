import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothOrthogonalGaugeJetExtraction

namespace JanusFormal
namespace P0EFTJanusNormalFrameTransitionJetBridge

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusSmoothNormalFrameJetExtraction
open P0EFTJanusNormalFrameConnectionGaugeLaw
open P0EFTJanusNormalConnectionCurvatureGaugeLaw
open P0EFTJanusSmoothOrthogonalGaugeJetExtraction

universe u v

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type*}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

/-- First derivative predicted by differentiating the adjoint formula
`g = e₁† e₂`:

`d_x g = (d_x e₁)† e₂ + e₁† (d_x e₂)`.
-/
def adjointTransitionFirstFormula
    (first second :
      SmoothOrthonormalNormalFrameTwoJetField Tangent Normal Ambient)
    (base x : Tangent) : Normal →L[ℝ] Normal :=
  (ContinuousLinearMap.adjoint (first.first base x)).comp
      (second.field base) +
    (ContinuousLinearMap.adjoint (first.field base)).comp
      (second.first base x)

/-- Second derivative predicted by differentiating the first derivative formula:

`d²_{x,y} g = (d²_{x,y} e₁)† e₂
             + (d_y e₁)† (d_x e₂)
             + (d_x e₁)† (d_y e₂)
             + e₁† d²_{x,y} e₂`.
-/
def adjointTransitionSecondFormula
    (first second :
      SmoothOrthonormalNormalFrameTwoJetField Tangent Normal Ambient)
    (base x y : Tangent) : Normal →L[ℝ] Normal :=
  (ContinuousLinearMap.adjoint (first.second base x y)).comp
      (second.field base) +
    (ContinuousLinearMap.adjoint (first.first base y)).comp
      (second.first base x) +
    (ContinuousLinearMap.adjoint (first.first base x)).comp
      (second.first base y) +
    (ContinuousLinearMap.adjoint (first.field base)).comp
      (second.second base x y)

/-- A complete two-jet realization of the canonical transition between two
smooth orthonormal normal frames. The derivative witnesses are not merely
arbitrary: they are required to equal the explicit derivatives of `e₁† e₂`.

This structure is the precise bridge between the smooth canonical transition
module and `SmoothOrthogonalGaugeTwoJetField`. -/
structure CanonicalNormalFrameTransitionTwoJet
    (Tangent : Type u) (Normal : Type v) (Ambient : Type*)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
    [FiniteDimensional ℝ Tangent]
    [FiniteDimensional ℝ Normal]
    [FiniteDimensional ℝ Ambient] where
  firstFrame :
    SmoothOrthonormalNormalFrameTwoJetField Tangent Normal Ambient
  secondFrame :
    SmoothOrthonormalNormalFrameTwoJetField Tangent Normal Ambient
  sameRange : ∀ base,
    normalFrameRange (frameValueAt firstFrame base) =
      normalFrameRange (frameValueAt secondFrame base)
  gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal
  field_eq : ∀ base,
    gauge.field base =
      normalFrameAdjointTransition
        (frameValueAt firstFrame base) (frameValueAt secondFrame base)
  first_eq : ∀ base x,
    gauge.first base x =
      adjointTransitionFirstFormula firstFrame secondFrame base x
  second_eq : ∀ base x y,
    gauge.second base x y =
      adjointTransitionSecondFormula firstFrame secondFrame base x y

/-- The gauge value stored by the bridge is exactly the canonical orthogonal
transition `e₁⁻¹e₂`, not only the adjoint-composition continuous map. -/
theorem bridge_gauge_value_eq_canonical
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base : Tangent) :
    smoothGaugeValueAt bridge.gauge base =
      normalFrameTransition
        (frameValueAt bridge.firstFrame base)
        (frameValueAt bridge.secondFrame base)
        (bridge.sameRange base) := by
  apply LinearIsometryEquiv.ext
  intro normal
  change bridge.gauge.field base normal = _
  rw [bridge.field_eq]
  have hCanonical := normalFrameAdjointTransition_eq_canonical
    (frameValueAt bridge.firstFrame base)
    (frameValueAt bridge.secondFrame base)
    (bridge.sameRange base)
  exact congrArg (fun operator : Normal →L[ℝ] Normal => operator normal)
    hCanonical

/-- The first jet extracted by the existing gauge module has the canonical
transition as value and the differentiated-adjoint formula as derivative. -/
theorem bridge_oneJet_value
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base : Tangent) :
    (orthogonalNormalGaugeOneJetAt bridge.gauge base).value =
      normalFrameTransition
        (frameValueAt bridge.firstFrame base)
        (frameValueAt bridge.secondFrame base)
        (bridge.sameRange base) :=
  bridge_gauge_value_eq_canonical bridge base

/-- Exact first-derivative identification in the extracted gauge one-jet. -/
theorem bridge_oneJet_derivative
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base x : Tangent) :
    (orthogonalNormalGaugeOneJetAt bridge.gauge base).derivative x =
      adjointTransitionFirstFormula
        bridge.firstFrame bridge.secondFrame base x := by
  exact bridge.first_eq base x

/-- Exact second-derivative identification used by the Maurer--Cartan extraction. -/
theorem bridge_second_derivative
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base x y : Tangent) :
    bridge.gauge.second base x y =
      adjointTransitionSecondFormula
        bridge.firstFrame bridge.secondFrame base x y :=
  bridge.second_eq base x y

/-- The logarithmic derivative extracted by the existing module is therefore the
canonical transition inverse applied to the explicit first derivative of
`e₁†e₂`. -/
theorem bridge_logDerivative_formula
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base x : Tangent) (normal : Normal) :
    smoothGaugeLogDerivative bridge.gauge base x normal =
      (normalFrameTransition
        (frameValueAt bridge.firstFrame base)
        (frameValueAt bridge.secondFrame base)
        (bridge.sameRange base)).symm
          (adjointTransitionFirstFormula
            bridge.firstFrame bridge.secondFrame base x normal) := by
  rw [smoothGaugeLogDerivative_apply, bridge.first_eq]
  let value := adjointTransitionFirstFormula
    bridge.firstFrame bridge.secondFrame base x normal
  calc
    bridge.gauge.inverse base value =
        (smoothGaugeValueAt bridge.gauge base).symm value :=
      (smoothGaugeValueAt_symm_apply bridge.gauge base value).symm
    _ = (normalFrameTransition
          (frameValueAt bridge.firstFrame base)
          (frameValueAt bridge.secondFrame base)
          (bridge.sameRange base)).symm value := by
      rw [bridge_gauge_value_eq_canonical]

/-- The full Maurer--Cartan two-jet used by the normal-curvature gauge law is now
canonically attached to the two frame jets through the bridge. -/
def bridgeMaurerCartanTwoJetAt
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base : Tangent) :
    OrthogonalGaugeMaurerCartanTwoJet Tangent Normal :=
  orthogonalGaugeMaurerCartanTwoJetAt bridge.gauge base

/-- Curvature covariance for the canonical normal-frame transition, obtained by
feeding the bridged first and second jets into the already-proved gauge module. -/
theorem canonicalTransition_curvature_covariance
    (bridge : CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient)
    (base : Tangent)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    gaugeTransformedCurvatureEndomorphism
        (bridgeMaurerCartanTwoJetAt bridge base) jet x y =
      orthogonalConjugate
        (normalFrameTransition
          (frameValueAt bridge.firstFrame base)
          (frameValueAt bridge.secondFrame base)
          (bridge.sameRange base))
        (normalConnectionCurvatureEndomorphism jet x y) := by
  change
    gaugeTransformedCurvatureEndomorphism
        (orthogonalGaugeMaurerCartanTwoJetAt bridge.gauge base) jet x y = _
  rw [curvature_covariance_of_smoothOrthogonalGauge]
  rw [bridge_gauge_value_eq_canonical]

/-- Exact remaining boundary: the bridge records and uses the differentiated
adjoint formulas, while the next theorem must construct this bridge directly
from the two frame fields by Fréchet differentiation, with no extra witnesses. -/
structure NormalFrameTransitionJetBridgeStatus where
  adjointFirstFormulaDefined : Prop
  adjointSecondFormulaDefined : Prop
  canonicalGaugeTwoJetInterfaceDefined : Prop
  gaugeValueMatchedToCanonicalTransition : Prop
  firstJetMatchedToAdjointDerivative : Prop
  secondJetMatchedToAdjointDerivative : Prop
  maurerCartanJetLinked : Prop
  curvatureCovarianceLinked : Prop
  bridgeConstructedDirectlyFromFrameFrechetData : Prop

/-- Closure of the transition-jet bridge stage. -/
def normalFrameTransitionJetBridgeClosed
    (s : NormalFrameTransitionJetBridgeStatus) : Prop :=
  s.adjointFirstFormulaDefined ∧
  s.adjointSecondFormulaDefined ∧
  s.canonicalGaugeTwoJetInterfaceDefined ∧
  s.gaugeValueMatchedToCanonicalTransition ∧
  s.firstJetMatchedToAdjointDerivative ∧
  s.secondJetMatchedToAdjointDerivative ∧
  s.maurerCartanJetLinked ∧
  s.curvatureCovarianceLinked ∧
  s.bridgeConstructedDirectlyFromFrameFrechetData

/-- Merely supplying the exact derivative witnesses does not yet prove that they
are generated automatically from the two frame fields. -/
theorem missing_direct_frechet_construction_blocks_full_bridge
    (s : NormalFrameTransitionJetBridgeStatus)
    (hMissing : Not s.bridgeConstructedDirectlyFromFrameFrechetData) :
    Not (normalFrameTransitionJetBridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2

end

end P0EFTJanusNormalFrameTransitionJetBridge
end JanusFormal
