import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

/-!
# Generic groupoid criterion for semidirect second-jet transport

Componentwise chain and Leibniz identities imply composition of the induced
continuous-linear transports.  This is independent of any geometric atlas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

/-- Identity coefficients induce the identity on every framed second jet. -/
theorem framedSecondOrderJetSemidirectTransport_self_of_coefficients
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]
    (change : FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : ∀ direction, change.baseFirst direction = direction)
    (hBaseSecond : ∀ first second, change.baseSecond first second = 0)
    (hFiberValue : ∀ value, change.fiberValue value = value)
    (hFiberFirst : ∀ direction value, change.fiberFirst direction value = 0)
    (hFiberSecond : ∀ first second value,
      change.fiberSecond first second value = 0)
    (jet : FramedSecondOrderJet X V) :
    change.toContinuousLinearMap jet = jet := by
  apply FramedSecondOrderJet.ext_components
  · simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, hFiberValue]
  · ext direction
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      hBaseFirst, hFiberValue, hFiberFirst, add_zero]
  · ext first second
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_secondDerivative_apply,
      hBaseFirst, hBaseSecond, hFiberValue, hFiberFirst, hFiberSecond,
      map_zero, add_zero]

/-- Coefficient-level chain rules imply exact composition of semidirect
second-jet transports. -/
theorem framedSecondOrderJetSemidirectTransport_comp_of_coefficients
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]
    (firstMiddle middleLast firstLast :
      FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : ∀ direction,
      firstLast.baseFirst direction =
        firstMiddle.baseFirst (middleLast.baseFirst direction))
    (hBaseSecond : ∀ first second,
      firstLast.baseSecond first second =
        firstMiddle.baseSecond
            (middleLast.baseFirst first) (middleLast.baseFirst second) +
          firstMiddle.baseFirst (middleLast.baseSecond first second))
    (hFiberValue : ∀ value,
      firstLast.fiberValue value =
        middleLast.fiberValue (firstMiddle.fiberValue value))
    (hFiberFirst : ∀ direction value,
      firstLast.fiberFirst direction value =
        middleLast.fiberValue
            (firstMiddle.fiberFirst (middleLast.baseFirst direction) value) +
          middleLast.fiberFirst direction (firstMiddle.fiberValue value))
    (hFiberSecond : ∀ first second value,
      firstLast.fiberSecond first second value =
        middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseFirst first) (middleLast.baseFirst second) value) +
          middleLast.fiberValue
            (firstMiddle.fiberFirst
              (middleLast.baseSecond first second) value) +
          middleLast.fiberFirst first
            (firstMiddle.fiberFirst (middleLast.baseFirst second) value) +
          middleLast.fiberFirst second
            (firstMiddle.fiberFirst (middleLast.baseFirst first) value) +
          middleLast.fiberSecond first second
            (firstMiddle.fiberValue value))
    (jet : FramedSecondOrderJet X V) :
    firstLast.toContinuousLinearMap jet =
      middleLast.toContinuousLinearMap
        (firstMiddle.toContinuousLinearMap jet) := by
  apply FramedSecondOrderJet.ext_components
  · simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, hFiberValue]
  · ext direction
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      hBaseFirst, hFiberValue, hFiberFirst, map_add]
    abel
  · ext first second
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_secondDerivative_apply,
      hBaseFirst, hBaseSecond, hFiberValue, hFiberFirst, hFiberSecond,
      map_add]
    simp only [FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, map_add]
    abel

end
end P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D
end JanusFormal
