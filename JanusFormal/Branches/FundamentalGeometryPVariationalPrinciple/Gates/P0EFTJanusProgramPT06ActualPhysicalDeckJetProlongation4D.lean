import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D

/-!
# Conditional deck action on the complete physical jet tower

Gate874's value carrier has eleven components: four gauge covectors, the
three trivial LL coefficient fibers, two metric tensors and two doubled SpinC
fibers.  The doubled SpinC monodromy is already an integer deck action, and
the LL coefficient fibers carry the identity action.  The current fixed-frame
API does not supply a point-independent deck action on either
`FramedCovector ThroatCoverCoordinates` or
`FramedCovariantTwoTensor ThroatCoverCoordinates`.

This gate isolates exactly those two missing representations as input data,
assembles the resulting action on all eleven value components, and reuses
Gate885's coefficientwise prolongation on every finite Finsupp jet order.  It
proves identity, composition, inverse, truncation naturality and formal total
derivative naturality.  No existence claim for the missing fixed-frame gauge
or metric representations, and no terminal T06 classification, is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalDeckJetProlongation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-- The two fixed-frame representations still required to turn the available
physical component actions into an action on Gate874's full value carrier. -/
structure ProgramPT06ActualPhysicalFixedFrameDeckData4D where
  gauge : Int → ActualGaugeValueFiber ≃ₗ[Real] ActualGaugeValueFiber
  metric : Int → ActualMetricValueFiber ≃ₗ[Real] ActualMetricValueFiber
  gauge_zero : ∀ value, gauge 0 value = value
  gauge_add : ∀ first second value,
    gauge (first + second) value = gauge first (gauge second value)
  metric_zero : ∀ value, metric 0 value = value
  metric_add : ∀ first second value,
    metric (first + second) value = metric first (metric second value)

/-- Componentwise action on the four gauge covectors. -/
def programPT06ActualGaugeValueProductDeckAction
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (winding : Int) (value : ActualGaugeValueProductFiber) :
    ActualGaugeValueProductFiber :=
  ((data.gauge winding value.1.1, data.gauge winding value.1.2),
    (data.gauge winding value.2.1, data.gauge winding value.2.2))

@[simp] theorem programPT06ActualGaugeValueProductDeckAction_zero
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (value : ActualGaugeValueProductFiber) :
    programPT06ActualGaugeValueProductDeckAction data 0 value = value := by
  rcases value with ⟨⟨first, second⟩, ⟨third, fourth⟩⟩
  simp [programPT06ActualGaugeValueProductDeckAction, data.gauge_zero]

theorem programPT06ActualGaugeValueProductDeckAction_add
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (first second : Int) (value : ActualGaugeValueProductFiber) :
    programPT06ActualGaugeValueProductDeckAction data (first + second) value =
      programPT06ActualGaugeValueProductDeckAction data first
        (programPT06ActualGaugeValueProductDeckAction data second value) := by
  rcases value with ⟨⟨firstValue, secondValue⟩, ⟨thirdValue, fourthValue⟩⟩
  simp [programPT06ActualGaugeValueProductDeckAction, data.gauge_add]

/-- Identity action on the three LL coefficient fibers. -/
def programPT06ActualLLValueProductDeckAction
    (_winding : Int) (value : ActualLLValueProductFiber) :
    ActualLLValueProductFiber :=
  value

/-- Componentwise action on the two metric tensors. -/
def programPT06ActualMetricValueProductDeckAction
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (winding : Int) (value : ActualMetricValueProductFiber) :
    ActualMetricValueProductFiber :=
  (data.metric winding value.1, data.metric winding value.2)

@[simp] theorem programPT06ActualMetricValueProductDeckAction_zero
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (value : ActualMetricValueProductFiber) :
    programPT06ActualMetricValueProductDeckAction data 0 value = value := by
  rcases value with ⟨first, second⟩
  simp [programPT06ActualMetricValueProductDeckAction, data.metric_zero]

theorem programPT06ActualMetricValueProductDeckAction_add
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (first second : Int) (value : ActualMetricValueProductFiber) :
    programPT06ActualMetricValueProductDeckAction data (first + second) value =
      programPT06ActualMetricValueProductDeckAction data first
        (programPT06ActualMetricValueProductDeckAction data second value) := by
  rcases value with ⟨firstValue, secondValue⟩
  simp [programPT06ActualMetricValueProductDeckAction, data.metric_add]

/-- The existing doubled-matter monodromy on both SpinC value components. -/
def programPT06ActualSpinCValueProductDeckAction
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualSpinCValueProductFiber) :
    ActualSpinCValueProductFiber :=
  (d9DoubledMatterSpinorMonodromy choice winding value.1,
    d9DoubledMatterSpinorMonodromy choice winding value.2)

@[simp] theorem programPT06ActualSpinCValueProductDeckAction_zero
    (choice : NormalRootChoice) (value : ActualSpinCValueProductFiber) :
    programPT06ActualSpinCValueProductDeckAction choice 0 value = value := by
  rcases value with ⟨first, second⟩
  simp [programPT06ActualSpinCValueProductDeckAction]

theorem programPT06ActualSpinCValueProductDeckAction_add
    (choice : NormalRootChoice) (first second : Int)
    (value : ActualSpinCValueProductFiber) :
    programPT06ActualSpinCValueProductDeckAction choice (first + second) value =
      programPT06ActualSpinCValueProductDeckAction choice first
        (programPT06ActualSpinCValueProductDeckAction choice second value) := by
  rcases value with ⟨firstValue, secondValue⟩
  simp [programPT06ActualSpinCValueProductDeckAction,
    d9DoubledMatterSpinorMonodromy_add]

/-- Conditional integer deck action on Gate874's exact eleven-component
physical value product. -/
def programPT06ActualPhysicalValueProductDeckAction
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    ActualPhysicalValueProductFiber :=
  (((programPT06ActualGaugeValueProductDeckAction data winding value.1.1.1,
      programPT06ActualLLValueProductDeckAction winding value.1.1.2),
    programPT06ActualMetricValueProductDeckAction data winding value.1.2),
    programPT06ActualSpinCValueProductDeckAction choice winding value.2)

@[simp] theorem programPT06ActualPhysicalValueProductDeckAction_zero
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalValueProductDeckAction data choice 0 value =
      value := by
  rcases value with ⟨⟨⟨gauge, ll⟩, metric⟩, spinC⟩
  simp [programPT06ActualPhysicalValueProductDeckAction,
    programPT06ActualLLValueProductDeckAction]

theorem programPT06ActualPhysicalValueProductDeckAction_add
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (first second : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalValueProductDeckAction data choice
        (first + second) value =
      programPT06ActualPhysicalValueProductDeckAction data choice first
        (programPT06ActualPhysicalValueProductDeckAction data choice second
          value) := by
  rcases value with ⟨⟨⟨gauge, ll⟩, metric⟩, spinC⟩
  simp [programPT06ActualPhysicalValueProductDeckAction,
    programPT06ActualLLValueProductDeckAction,
    programPT06ActualGaugeValueProductDeckAction_add,
    programPT06ActualMetricValueProductDeckAction_add,
    programPT06ActualSpinCValueProductDeckAction_add]

theorem programPT06ActualPhysicalValueProductDeckAction_inverse_left
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalValueProductDeckAction data choice (-winding)
        (programPT06ActualPhysicalValueProductDeckAction data choice winding
          value) = value := by
  calc
    _ = programPT06ActualPhysicalValueProductDeckAction data choice
        ((-winding) + winding) value :=
      (programPT06ActualPhysicalValueProductDeckAction_add data choice
        (-winding) winding value).symm
    _ = value := by simp

theorem programPT06ActualPhysicalValueProductDeckAction_inverse_right
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int)
    (value : ActualPhysicalValueProductFiber) :
    programPT06ActualPhysicalValueProductDeckAction data choice winding
        (programPT06ActualPhysicalValueProductDeckAction data choice (-winding)
          value) = value := by
  calc
    _ = programPT06ActualPhysicalValueProductDeckAction data choice
        (winding + (-winding)) value :=
      (programPT06ActualPhysicalValueProductDeckAction_add data choice
        winding (-winding) value).symm
    _ = value := by simp

/-- Gate885 coefficientwise prolongation of the full physical value action. -/
def programPT06ActualPhysicalJetDeckAction
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order :=
  programPT06ThroatSpatialJetProlongation
    (programPT06ActualPhysicalValueProductDeckAction data choice winding)
    order jet

@[simp] theorem programPT06ActualPhysicalJetDeckAction_zero
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalJetDeckAction data choice 0 order jet = jet := by
  funext index
  exact programPT06ActualPhysicalValueProductDeckAction_zero data choice
    (jet index)

theorem programPT06ActualPhysicalJetDeckAction_add
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (first second : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalJetDeckAction data choice (first + second) order
        jet =
      programPT06ActualPhysicalJetDeckAction data choice first order
        (programPT06ActualPhysicalJetDeckAction data choice second order
          jet) := by
  funext index
  exact programPT06ActualPhysicalValueProductDeckAction_add data choice
    first second (jet index)

theorem programPT06ActualPhysicalJetDeckAction_inverse_left
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalJetDeckAction data choice (-winding) order
        (programPT06ActualPhysicalJetDeckAction data choice winding order
          jet) = jet := by
  funext index
  exact programPT06ActualPhysicalValueProductDeckAction_inverse_left
    data choice winding (jet index)

theorem programPT06ActualPhysicalJetDeckAction_inverse_right
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber order) :
    programPT06ActualPhysicalJetDeckAction data choice winding order
        (programPT06ActualPhysicalJetDeckAction data choice (-winding) order
          jet) = jet := by
  funext index
  exact programPT06ActualPhysicalValueProductDeckAction_inverse_right
    data choice winding (jet index)

/-- The full conditional action commutes with every jet truncation. -/
theorem programPT06ActualPhysicalJetDeckAction_commutes_truncation
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int)
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ActualPhysicalJetDeckAction data choice winding higher
          jet) =
      programPT06ActualPhysicalJetDeckAction data choice winding lower
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_truncation
    (programPT06ActualPhysicalValueProductDeckAction data choice winding)
    hOrder jet

/-- The full conditional action commutes with every formal spatial total
derivative. -/
theorem programPT06ActualPhysicalJetDeckAction_commutes_totalDerivative
    (data : ProgramPT06ActualPhysicalFixedFrameDeckData4D)
    (choice : NormalRootChoice) (winding : Int)
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualPhysicalValueProductFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualPhysicalJetDeckAction data choice winding
          (order + 1) jet) =
      programPT06ActualPhysicalJetDeckAction data choice winding order
        (throatSpatialTotalDerivative direction jet) := by
  exact programPT06ThroatSpatialJetProlongation_commutes_totalDerivative
    (programPT06ActualPhysicalValueProductDeckAction data choice winding)
    direction jet

end
end P0EFTJanusProgramPT06ActualPhysicalDeckJetProlongation4D
end JanusFormal
