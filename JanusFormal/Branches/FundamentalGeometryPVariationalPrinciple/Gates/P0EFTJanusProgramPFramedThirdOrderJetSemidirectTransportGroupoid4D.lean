import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D

/-!
# Generic groupoid criterion for semidirect third-jet transport

Identity coefficients act trivially, and the third-order base chain rule and
fiber Leibniz rule imply exact composition of the induced third-jet
transports.  All coefficient identities are explicit; no geometric atlas or
quotient descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D

private theorem transport_value_explicit
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    (change.transport jet).value = change.fiberValue jet.value :=
  rfl

private theorem transport_firstDerivative_apply_explicit
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (direction : X) :
    (change.transport jet).firstDerivative direction =
      change.fiberValue
          (jet.firstDerivative (change.baseFirst direction)) +
        change.fiberFirst direction jet.value :=
  rfl

private theorem transport_secondDerivative_apply_explicit
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second : X) :
    (change.transport jet).secondDerivative first second =
      change.fiberValue
          (jet.secondDerivative
            (change.baseFirst first) (change.baseFirst second)) +
        change.fiberValue
          (jet.firstDerivative (change.baseSecond first second)) +
        change.fiberFirst first
          (jet.firstDerivative (change.baseFirst second)) +
        change.fiberFirst second
          (jet.firstDerivative (change.baseFirst first)) +
        change.fiberSecond first second jet.value :=
  rfl

private theorem transport_thirdDerivative_apply_explicit
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) :
    (change.transport jet).thirdDerivative first second third =
      change.fiberValue
          (jet.thirdDerivative
            (change.baseFirst first)
            (change.baseFirst second)
            (change.baseFirst third)) +
        change.fiberValue
          (jet.secondDerivative
            (change.baseSecond first second) (change.baseFirst third)) +
        change.fiberValue
          (jet.secondDerivative
            (change.baseSecond first third) (change.baseFirst second)) +
        change.fiberValue
          (jet.secondDerivative
            (change.baseSecond second third) (change.baseFirst first)) +
        change.fiberValue
          (jet.firstDerivative (change.baseThird first second third)) +
        change.fiberFirst first
          (jet.secondDerivative
            (change.baseFirst second) (change.baseFirst third)) +
        change.fiberFirst second
          (jet.secondDerivative
            (change.baseFirst first) (change.baseFirst third)) +
        change.fiberFirst third
          (jet.secondDerivative
            (change.baseFirst first) (change.baseFirst second)) +
        change.fiberFirst first
          (jet.firstDerivative (change.baseSecond second third)) +
        change.fiberFirst second
          (jet.firstDerivative (change.baseSecond first third)) +
        change.fiberFirst third
          (jet.firstDerivative (change.baseSecond first second)) +
        change.fiberSecond first second
          (jet.firstDerivative (change.baseFirst third)) +
        change.fiberSecond first third
          (jet.firstDerivative (change.baseFirst second)) +
        change.fiberSecond second third
          (jet.firstDerivative (change.baseFirst first)) +
        change.fiberThird first second third jet.value :=
  rfl

/-- Identity coefficients induce the identity on every framed third jet. -/
theorem framedThirdOrderJetSemidirectTransport_self_of_coefficients
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (hBaseFirst : ∀ direction, change.baseFirst direction = direction)
    (hBaseSecond : ∀ first second, change.baseSecond first second = 0)
    (hBaseThird : ∀ first second third,
      change.baseThird first second third = 0)
    (hFiberValue : ∀ value, change.fiberValue value = value)
    (hFiberFirst : ∀ direction value,
      change.fiberFirst direction value = 0)
    (hFiberSecond : ∀ first second value,
      change.fiberSecond first second value = 0)
    (hFiberThird : ∀ first second third value,
      change.fiberThird first second third value = 0)
    (jet : FramedThirdOrderJet X V) :
    change.transport jet = jet := by
  apply FramedThirdOrderJet.ext_components
  · simpa only [
      FramedThirdOrderJetSemidirectChange.transport_toFramedSecondOrderJet,
      FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply]
      using
        framedSecondOrderJetSemidirectTransport_self_of_coefficients
          change.toFramedSecondOrderJetSemidirectChange
          hBaseFirst hBaseSecond hFiberValue hFiberFirst hFiberSecond
          jet.toFramedSecondOrderJet
  · ext first second third
    simp only [transport_thirdDerivative_apply_explicit,
      hBaseFirst, hBaseSecond, hBaseThird, hFiberValue, hFiberFirst,
      hFiberSecond, hFiberThird, map_zero, zero_apply, add_zero]

/-- Coefficient-level chain and Leibniz rules imply exact composition of
semidirect third-jet transports. -/
theorem framedThirdOrderJetSemidirectTransport_comp_of_coefficients
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]
    (firstMiddle middleLast firstLast :
      FramedThirdOrderJetSemidirectChange X V)
    (hBaseFirst : ∀ direction,
      firstLast.baseFirst direction =
        firstMiddle.baseFirst (middleLast.baseFirst direction))
    (hBaseSecond : ∀ first second,
      firstLast.baseSecond first second =
        firstMiddle.baseSecond
            (middleLast.baseFirst first) (middleLast.baseFirst second) +
          firstMiddle.baseFirst (middleLast.baseSecond first second))
    (hBaseThird : ∀ first second third,
      firstLast.baseThird first second third =
        firstMiddle.baseThird
            (middleLast.baseFirst first)
            (middleLast.baseFirst second)
            (middleLast.baseFirst third) +
          firstMiddle.baseSecond
            (middleLast.baseSecond first second)
            (middleLast.baseFirst third) +
          firstMiddle.baseSecond
            (middleLast.baseSecond first third)
            (middleLast.baseFirst second) +
          firstMiddle.baseSecond
            (middleLast.baseSecond second third)
            (middleLast.baseFirst first) +
          firstMiddle.baseFirst
            (middleLast.baseThird first second third))
    (hFiberValue : ∀ value,
      firstLast.fiberValue value =
        middleLast.fiberValue (firstMiddle.fiberValue value))
    (hFiberFirst : ∀ direction value,
      firstLast.fiberFirst direction value =
        middleLast.fiberValue
            (firstMiddle.fiberFirst
              (middleLast.baseFirst direction) value) +
          middleLast.fiberFirst direction
            (firstMiddle.fiberValue value))
    (hFiberSecond : ∀ first second value,
      firstLast.fiberSecond first second value =
        middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseFirst first)
              (middleLast.baseFirst second) value) +
          middleLast.fiberValue
            (firstMiddle.fiberFirst
              (middleLast.baseSecond first second) value) +
          middleLast.fiberFirst first
            (firstMiddle.fiberFirst
              (middleLast.baseFirst second) value) +
          middleLast.fiberFirst second
            (firstMiddle.fiberFirst
              (middleLast.baseFirst first) value) +
          middleLast.fiberSecond first second
            (firstMiddle.fiberValue value))
    (hFiberThird : ∀ first second third value,
      firstLast.fiberThird first second third value =
        middleLast.fiberValue
            (firstMiddle.fiberThird
              (middleLast.baseFirst first)
              (middleLast.baseFirst second)
              (middleLast.baseFirst third) value) +
          middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseSecond first second)
              (middleLast.baseFirst third) value) +
          middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseSecond first third)
              (middleLast.baseFirst second) value) +
          middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseSecond second third)
              (middleLast.baseFirst first) value) +
          middleLast.fiberValue
            (firstMiddle.fiberFirst
              (middleLast.baseThird first second third) value) +
          middleLast.fiberFirst first
            (firstMiddle.fiberSecond
              (middleLast.baseFirst second)
              (middleLast.baseFirst third) value) +
          middleLast.fiberFirst second
            (firstMiddle.fiberSecond
              (middleLast.baseFirst first)
              (middleLast.baseFirst third) value) +
          middleLast.fiberFirst third
            (firstMiddle.fiberSecond
              (middleLast.baseFirst first)
              (middleLast.baseFirst second) value) +
          middleLast.fiberFirst first
            (firstMiddle.fiberFirst
              (middleLast.baseSecond second third) value) +
          middleLast.fiberFirst second
            (firstMiddle.fiberFirst
              (middleLast.baseSecond first third) value) +
          middleLast.fiberFirst third
            (firstMiddle.fiberFirst
              (middleLast.baseSecond first second) value) +
          middleLast.fiberSecond first second
            (firstMiddle.fiberFirst
              (middleLast.baseFirst third) value) +
          middleLast.fiberSecond first third
            (firstMiddle.fiberFirst
              (middleLast.baseFirst second) value) +
          middleLast.fiberSecond second third
            (firstMiddle.fiberFirst
              (middleLast.baseFirst first) value) +
          middleLast.fiberThird first second third
            (firstMiddle.fiberValue value))
    (jet : FramedThirdOrderJet X V) :
    firstLast.transport jet =
      middleLast.transport (firstMiddle.transport jet) := by
  apply FramedThirdOrderJet.ext_components
  · simpa only [
      FramedThirdOrderJetSemidirectChange.transport_toFramedSecondOrderJet,
      FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply]
      using
        framedSecondOrderJetSemidirectTransport_comp_of_coefficients
          firstMiddle.toFramedSecondOrderJetSemidirectChange
          middleLast.toFramedSecondOrderJetSemidirectChange
          firstLast.toFramedSecondOrderJetSemidirectChange
          hBaseFirst hBaseSecond hFiberValue hFiberFirst hFiberSecond
          jet.toFramedSecondOrderJet
  · ext first second third
    simp only [transport_thirdDerivative_apply_explicit,
      transport_secondDerivative_apply_explicit,
      transport_firstDerivative_apply_explicit, transport_value_explicit,
      hBaseFirst, hBaseSecond, hBaseThird, hFiberValue, hFiberFirst,
      hFiberSecond, hFiberThird, map_add, add_apply]
    abel

end
end P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D
end JanusFormal
