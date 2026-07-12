import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHessianHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusInvariantMapNoetherHelmholtz

set_option autoImplicit false

open P0EFTJanusHessianHelmholtzReconstruction

/-- Two-component field variation. -/
@[ext] structure FieldVector2 where
  x : ℝ
  y : ℝ

/-- Linear scalar invariant extracted from fields. -/
@[ext] structure LinearInvariant where
  xCoefficient : ℝ
  yCoefficient : ℝ

/-- Evaluate the invariant. -/
def evaluateInvariant
    (invariant : LinearInvariant)
    (field : FieldVector2) : ℝ :=
  invariant.xCoefficient * field.x +
    invariant.yCoefficient * field.y

/-- Gauge direction in field space. -/
abbrev GaugeDirection := FieldVector2

/-- The invariant is constant along the infinitesimal gauge direction. -/
def GaugeInvariant
    (invariant : LinearInvariant)
    (gaugeDirection : GaugeDirection) : Prop :=
  evaluateInvariant invariant gaugeDirection = 0

/-- Rank-one Hessian induced by a scalar target pairing. -/
def inducedHessian
    (pairingWeight : ℝ)
    (invariant : LinearInvariant) : LinearOperator2 :=
  { xx := pairingWeight * invariant.xCoefficient ^ 2
    xy := pairingWeight * invariant.xCoefficient * invariant.yCoefficient
    yx := pairingWeight * invariant.yCoefficient * invariant.xCoefficient
    yy := pairingWeight * invariant.yCoefficient ^ 2 }

/-- Apply a linear operator to a field vector. -/
def applyLinearOperator
    (operator : LinearOperator2)
    (field : FieldVector2) : FieldVector2 :=
  { x := operator.xx * field.x + operator.xy * field.y
    y := operator.yx * field.x + operator.yy * field.y }

/-- The induced Hessian is automatically formally self-adjoint. -/
theorem induced_hessian_formally_self_adjoint
    (pairingWeight : ℝ)
    (invariant : LinearInvariant) :
    FormallySelfAdjoint
      (inducedHessian pairingWeight invariant) := by
  unfold FormallySelfAdjoint inducedHessian
  ring

/-- Applying the induced Hessian factors through the invariant value. -/
theorem induced_hessian_action_factorization
    (pairingWeight : ℝ)
    (invariant : LinearInvariant)
    (field : FieldVector2) :
    applyLinearOperator
        (inducedHessian pairingWeight invariant) field =
      { x := pairingWeight * invariant.xCoefficient *
          evaluateInvariant invariant field
        y := pairingWeight * invariant.yCoefficient *
          evaluateInvariant invariant field } := by
  apply FieldVector2.ext <;>
    simp [applyLinearOperator, inducedHessian,
      evaluateInvariant] <;>
    ring

/-- Gauge invariance of the geometric invariant implies the linearized Noether identity. -/
theorem gauge_invariant_map_implies_noether
    (pairingWeight : ℝ)
    (invariant : LinearInvariant)
    (gaugeDirection : GaugeDirection)
    (hInvariant : GaugeInvariant invariant gaugeDirection) :
    applyLinearOperator
        (inducedHessian pairingWeight invariant)
        gaugeDirection = { x := 0, y := 0 } := by
  rw [induced_hessian_action_factorization]
  unfold GaugeInvariant at hInvariant
  rw [hInvariant]
  apply FieldVector2.ext <;> simp

/-- The same construction satisfies Helmholtz reciprocity. -/
theorem invariant_map_pairing_implies_helmholtz
    (pairingWeight : ℝ)
    (invariant : LinearInvariant) :
    ∃ potential : QuadraticPotential2,
      hessianOperator potential =
        inducedHessian pairingWeight invariant := by
  exact (helmholtz_realizability_iff
    (inducedHessian pairingWeight invariant)).2
    (induced_hessian_formally_self_adjoint
      pairingWeight invariant)

/-- Exact joint bridge from invariant map plus symmetric target pairing. -/
theorem invariant_map_gives_noether_and_helmholtz
    (pairingWeight : ℝ)
    (invariant : LinearInvariant)
    (gaugeDirection : GaugeDirection)
    (hInvariant : GaugeInvariant invariant gaugeDirection) :
    FormallySelfAdjoint
        (inducedHessian pairingWeight invariant) /\
    applyLinearOperator
        (inducedHessian pairingWeight invariant)
        gaugeDirection = { x := 0, y := 0 } /\
    ∃ potential : QuadraticPotential2,
      hessianOperator potential =
        inducedHessian pairingWeight invariant := by
  exact ⟨induced_hessian_formally_self_adjoint
      pairingWeight invariant,
    gauge_invariant_map_implies_noether
      pairingWeight invariant gaugeDirection hInvariant,
    invariant_map_pairing_implies_helmholtz
      pairingWeight invariant⟩

/-- A concrete gauge direction. -/
def standardGaugeDirection : GaugeDirection :=
  { x := 1, y := 0 }

/-- A concrete invariant insensitive to that gauge direction. -/
def transverseInvariant : LinearInvariant :=
  { xCoefficient := 0, yCoefficient := 1 }

/-- The concrete invariant is gauge invariant. -/
theorem transverse_invariant_is_gauge_invariant :
    GaugeInvariant transverseInvariant standardGaugeDirection := by
  norm_num [GaugeInvariant, evaluateInvariant,
    transverseInvariant, standardGaugeDirection]

/-- Identity response is symmetric but does not annihilate the gauge direction. -/
def identityResponse : LinearOperator2 :=
  { xx := 1, xy := 0, yx := 0, yy := 1 }

/-- Helmholtz alone does not imply Noether. -/
theorem helmholtz_does_not_imply_noether :
    FormallySelfAdjoint identityResponse /\
    applyLinearOperator identityResponse standardGaugeDirection ≠
      { x := 0, y := 0 } := by
  constructor
  · rfl
  · intro hEqual
    have hX := congrArg FieldVector2.x hEqual
    norm_num [applyLinearOperator,
      identityResponse, standardGaugeDirection] at hX

/-- Non-self-adjoint response that nevertheless annihilates the gauge direction. -/
def noetherButNonHelmholtzResponse : LinearOperator2 :=
  { xx := 0, xy := 1, yx := 0, yy := 1 }

/-- Noether alone does not imply Helmholtz. -/
theorem noether_does_not_imply_helmholtz :
    applyLinearOperator noetherButNonHelmholtzResponse
        standardGaugeDirection = { x := 0, y := 0 } /\
    Not (FormallySelfAdjoint noetherButNonHelmholtzResponse) := by
  constructor
  · apply FieldVector2.ext <;>
      norm_num [applyLinearOperator,
        noetherButNonHelmholtzResponse,
        standardGaugeDirection]
  · norm_num [FormallySelfAdjoint,
      noetherButNonHelmholtzResponse]

/--
Correct complex-level interpretation:

* the geometric compatibility/Bianchi layer supplies an invariant map `K` with
  `K R = 0` along gauge directions `R`;
* a symmetric target pairing supplies `H`;
* the source Hessian `Kᵀ H K` is Helmholtz and satisfies the Noether identity;
* Noether and Helmholtz are independent if either ingredient is omitted.
-/
structure InvariantMapComplexBridgeStatus where
  gaugeComplexConstructed : Prop
  compatibleInvariantMapConstructed : Prop
  geometricBianchiIdentityProved : Prop
  targetPairingConstructed : Prop
  targetPairingSelfAdjointProved : Prop
  sourceHessianIdentifiedAsPullback : Prop
  noetherIdentityDerived : Prop
  helmholtzReciprocityDerived : Prop
  variationalPrimitiveReconstructed : Prop


def invariantMapComplexBridgeClosed
    (s : InvariantMapComplexBridgeStatus) : Prop :=
  s.gaugeComplexConstructed /\
  s.compatibleInvariantMapConstructed /\
  s.geometricBianchiIdentityProved /\
  s.targetPairingConstructed /\
  s.targetPairingSelfAdjointProved /\
  s.sourceHessianIdentifiedAsPullback /\
  s.noetherIdentityDerived /\
  s.helmholtzReciprocityDerived /\
  s.variationalPrimitiveReconstructed

end P0EFTJanusInvariantMapNoetherHelmholtz
end JanusFormal
