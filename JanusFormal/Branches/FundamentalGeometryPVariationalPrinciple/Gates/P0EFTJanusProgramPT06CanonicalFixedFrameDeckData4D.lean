import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalDeckJetProlongation4D

/-!
# Canonical fixed-frame deck data for the complete physical jet tower

The fixed-throat deck map already has product-coordinate form
`(sphere, time) ↦ (sphere, time + n * period)`.  Hence its linear part in the
fixed throat model frame is the identity.  The induced actions on a framed
covector and a framed covariant two-tensor are therefore the identity linear
equivalences.  This supplies the two pieces isolated as hypotheses in the
conditional full-carrier Gate.

Together with the identity action on the three LL coefficients and the
existing doubled-SpinC monodromy, this gate gives an unconditional action on
all eleven T02 value components and specializes every value- and jet-level
law from the conditional Gate.

This is a fixed-product-frame statement.  It does not identify the action in
an arbitrary moving throat trivialization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalDeckJetProlongation4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-! ## Linear part of the fixed-throat deck translation -/

/-- The affine fixed-frame coordinate form of one throat deck winding. -/
def programPT06FixedFrameDeckCoordinateTranslation
    (period : Real) (winding : Int)
    (coordinate : ThroatCoverCoordinates) : ThroatCoverCoordinates :=
  (coordinate.1, coordinate.2 + (winding : Real) * period)

/-- The linear part of every fixed-frame throat deck translation is the
identity. -/
def programPT06FixedFrameTangentDeckLinearEquiv (_winding : Int) :
    ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates :=
  LinearEquiv.refl Real ThroatCoverCoordinates

@[simp] theorem programPT06FixedFrameTangentDeckLinearEquiv_apply
    (winding : Int) (direction : ThroatCoverCoordinates) :
    programPT06FixedFrameTangentDeckLinearEquiv winding direction =
      direction :=
  rfl

/-- Exact affine-increment formula exhibiting the preceding linear part. -/
theorem programPT06FixedFrameDeckCoordinateTranslation_add_direction
    (period : Real) (winding : Int)
    (coordinate direction : ThroatCoverCoordinates) :
    programPT06FixedFrameDeckCoordinateTranslation period winding
        (coordinate + direction) =
      programPT06FixedFrameDeckCoordinateTranslation period winding
          coordinate +
        programPT06FixedFrameTangentDeckLinearEquiv winding direction := by
  apply Prod.ext
  · rfl
  · simp [programPT06FixedFrameDeckCoordinateTranslation,
      add_assoc, add_left_comm, add_comm]

/-! ## Canonical gauge and metric representations -/

/-- Pullback action on a gauge covector in the fixed product frame.  Since
the tangent linear part is the identity, so is the contragredient action. -/
def programPT06ActualGaugeFixedFrameDeckLinearEquiv (_winding : Int) :
    ActualGaugeValueFiber ≃ₗ[Real] ActualGaugeValueFiber :=
  LinearEquiv.refl Real ActualGaugeValueFiber

@[simp] theorem programPT06ActualGaugeFixedFrameDeckLinearEquiv_apply
    (winding : Int) (value : ActualGaugeValueFiber) :
    programPT06ActualGaugeFixedFrameDeckLinearEquiv winding value = value :=
  rfl

@[simp] theorem programPT06ActualGaugeFixedFrameDeckLinearEquiv_zero
    (value : ActualGaugeValueFiber) :
    programPT06ActualGaugeFixedFrameDeckLinearEquiv 0 value = value :=
  rfl

theorem programPT06ActualGaugeFixedFrameDeckLinearEquiv_add
    (first second : Int) (value : ActualGaugeValueFiber) :
    programPT06ActualGaugeFixedFrameDeckLinearEquiv (first + second) value =
      programPT06ActualGaugeFixedFrameDeckLinearEquiv first
        (programPT06ActualGaugeFixedFrameDeckLinearEquiv second value) :=
  rfl

/-- Pullback action on a covariant two-tensor in the fixed product frame. -/
def programPT06ActualMetricFixedFrameDeckLinearEquiv (_winding : Int) :
    ActualMetricValueFiber ≃ₗ[Real] ActualMetricValueFiber :=
  LinearEquiv.refl Real ActualMetricValueFiber

@[simp] theorem programPT06ActualMetricFixedFrameDeckLinearEquiv_apply
    (winding : Int) (value : ActualMetricValueFiber) :
    programPT06ActualMetricFixedFrameDeckLinearEquiv winding value = value :=
  rfl

@[simp] theorem programPT06ActualMetricFixedFrameDeckLinearEquiv_zero
    (value : ActualMetricValueFiber) :
    programPT06ActualMetricFixedFrameDeckLinearEquiv 0 value = value :=
  rfl

theorem programPT06ActualMetricFixedFrameDeckLinearEquiv_add
    (first second : Int) (value : ActualMetricValueFiber) :
    programPT06ActualMetricFixedFrameDeckLinearEquiv (first + second) value =
      programPT06ActualMetricFixedFrameDeckLinearEquiv first
        (programPT06ActualMetricFixedFrameDeckLinearEquiv second value) :=
  rfl

/-- Canonical discharge of the two fixed-frame hypotheses in the conditional
full physical deck Gate. -/
def programPT06ActualPhysicalCanonicalFixedFrameDeckData4D :
    ProgramPT06ActualPhysicalFixedFrameDeckData4D where
  gauge := programPT06ActualGaugeFixedFrameDeckLinearEquiv
  metric := programPT06ActualMetricFixedFrameDeckLinearEquiv
  gauge_zero := programPT06ActualGaugeFixedFrameDeckLinearEquiv_zero
  gauge_add := programPT06ActualGaugeFixedFrameDeckLinearEquiv_add
  metric_zero := programPT06ActualMetricFixedFrameDeckLinearEquiv_zero
  metric_add := programPT06ActualMetricFixedFrameDeckLinearEquiv_add

@[simp] theorem programPT06ActualGaugeValueProductCanonicalDeckAction_zero
    (value : ActualGaugeValueProductFiber) :
    programPT06ActualGaugeValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D 0 value =
      value :=
  programPT06ActualGaugeValueProductDeckAction_zero
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D value

theorem programPT06ActualGaugeValueProductCanonicalDeckAction_add
    (first second : Int) (value : ActualGaugeValueProductFiber) :
    programPT06ActualGaugeValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
        (first + second) value =
      programPT06ActualGaugeValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D first
        (programPT06ActualGaugeValueProductDeckAction
          programPT06ActualPhysicalCanonicalFixedFrameDeckData4D second
          value) :=
  programPT06ActualGaugeValueProductDeckAction_add
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
    first second value

@[simp] theorem programPT06ActualMetricValueProductCanonicalDeckAction_zero
    (value : ActualMetricValueProductFiber) :
    programPT06ActualMetricValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D 0 value =
      value :=
  programPT06ActualMetricValueProductDeckAction_zero
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D value

theorem programPT06ActualMetricValueProductCanonicalDeckAction_add
    (first second : Int) (value : ActualMetricValueProductFiber) :
    programPT06ActualMetricValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
        (first + second) value =
      programPT06ActualMetricValueProductDeckAction
        programPT06ActualPhysicalCanonicalFixedFrameDeckData4D first
        (programPT06ActualMetricValueProductDeckAction
          programPT06ActualPhysicalCanonicalFixedFrameDeckData4D second
          value) :=
  programPT06ActualMetricValueProductDeckAction_add
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
    first second value

/-! ## Unconditional action on all eleven values -/

/-- The resulting unconditional full physical value action. -/
def programPT06ActualPhysicalCanonicalValueDeckAction
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    ActualPhysicalValueProductFiber :=
  programPT06ActualPhysicalValueProductDeckAction
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
    choice winding value

/-- Component formula: the four gauge, three LL and two metric values are
fixed, while the two doubled-SpinC values carry the already proved
monodromy. -/
@[simp] theorem programPT06ActualPhysicalCanonicalValueDeckAction_apply
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice winding value =
      (((value.1.1.1, value.1.1.2), value.1.2),
        (d9DoubledMatterSpinorMonodromy choice winding value.2.1,
          d9DoubledMatterSpinorMonodromy choice winding value.2.2)) :=
  rfl

@[simp] theorem programPT06ActualPhysicalCanonicalValueDeckAction_zero
    (choice : NormalRootChoice) (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice 0 value =
      value :=
  programPT06ActualPhysicalValueProductDeckAction_zero
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice value

theorem programPT06ActualPhysicalCanonicalValueDeckAction_add
    (choice : NormalRootChoice) (first second : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice
        (first + second) value =
      programPT06ActualPhysicalCanonicalValueDeckAction choice first
        (programPT06ActualPhysicalCanonicalValueDeckAction choice second
          value) :=
  programPT06ActualPhysicalValueProductDeckAction_add
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    first second value

theorem programPT06ActualPhysicalCanonicalValueDeckAction_inverse_left
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice (-winding)
        (programPT06ActualPhysicalCanonicalValueDeckAction choice winding
          value) = value :=
  programPT06ActualPhysicalValueProductDeckAction_inverse_left
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    winding value

theorem programPT06ActualPhysicalCanonicalValueDeckAction_inverse_right
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice winding
        (programPT06ActualPhysicalCanonicalValueDeckAction choice (-winding)
          value) = value :=
  programPT06ActualPhysicalValueProductDeckAction_inverse_right
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    winding value

/-! ## Unconditional jet prolongation laws -/

/-- Coefficientwise prolongation of the unconditional eleven-component
action. -/
def programPT06ActualPhysicalCanonicalJetDeckAction
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order :=
  programPT06ActualPhysicalJetDeckAction
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D
    choice winding order jet

@[simp] theorem programPT06ActualPhysicalCanonicalJetDeckAction_zero
    (choice : NormalRootChoice) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalCanonicalJetDeckAction choice 0 order jet =
      jet :=
  programPT06ActualPhysicalJetDeckAction_zero
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice order jet

theorem programPT06ActualPhysicalCanonicalJetDeckAction_add
    (choice : NormalRootChoice) (first second : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalCanonicalJetDeckAction choice
        (first + second) order jet =
      programPT06ActualPhysicalCanonicalJetDeckAction choice first order
        (programPT06ActualPhysicalCanonicalJetDeckAction choice second order
          jet) :=
  programPT06ActualPhysicalJetDeckAction_add
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    first second order jet

theorem programPT06ActualPhysicalCanonicalJetDeckAction_inverse_left
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalCanonicalJetDeckAction choice (-winding) order
        (programPT06ActualPhysicalCanonicalJetDeckAction choice winding order
          jet) = jet :=
  programPT06ActualPhysicalJetDeckAction_inverse_left
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    winding order jet

theorem programPT06ActualPhysicalCanonicalJetDeckAction_inverse_right
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalCanonicalJetDeckAction choice winding order
        (programPT06ActualPhysicalCanonicalJetDeckAction choice (-winding)
          order jet) = jet :=
  programPT06ActualPhysicalJetDeckAction_inverse_right
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice
    winding order jet

theorem programPT06ActualPhysicalCanonicalJetDeckAction_commutes_truncation
    (choice : NormalRootChoice) (winding : Int)
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ActualPhysicalCanonicalJetDeckAction choice winding higher
          jet) =
      programPT06ActualPhysicalCanonicalJetDeckAction choice winding lower
        (truncateThroatSpatialMultiindexJet hOrder jet) :=
  programPT06ActualPhysicalJetDeckAction_commutes_truncation
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice winding
    hOrder jet

theorem programPT06ActualPhysicalCanonicalJetDeckAction_commutes_totalDerivative
    (choice : NormalRootChoice) (winding : Int)
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualPhysicalCanonicalJetDeckAction choice winding
          (order + 1) jet) =
      programPT06ActualPhysicalCanonicalJetDeckAction choice winding order
        (throatSpatialTotalDerivative direction jet) :=
  programPT06ActualPhysicalJetDeckAction_commutes_totalDerivative
    programPT06ActualPhysicalCanonicalFixedFrameDeckData4D choice winding
    direction jet

end
end P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D
end JanusFormal
