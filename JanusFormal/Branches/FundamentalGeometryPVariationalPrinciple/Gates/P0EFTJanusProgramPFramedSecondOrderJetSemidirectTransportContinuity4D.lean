import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

/-!
# Continuity of generic semidirect second-jet transport

Continuous families of the six frozen base/fiber coefficients induce a
continuous family of continuous linear maps on framed second jets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

variable
    {Parameter X V : Type*}
    [TopologicalSpace Parameter]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]

/-- The semidirect action depends continuously on any continuous family of
its six coefficient fields.  The two symmetry witnesses are proof data and
do not enter the topology. -/
theorem continuous_semidirectTransport
    (change : Parameter → FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : Continuous (fun point ↦ (change point).baseFirst))
    (hBaseSecond : Continuous (fun point ↦ (change point).baseSecond))
    (hFiberValue : Continuous (fun point ↦ (change point).fiberValue))
    (hFiberFirst : Continuous (fun point ↦ (change point).fiberFirst))
    (hFiberSecond : Continuous (fun point ↦ (change point).fiberSecond)) :
    Continuous (fun point ↦ (change point).toContinuousLinearMap) := by
  rw [continuous_clm_apply]
  intro jet
  have hValue : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).value) := by
    simpa only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value] using
      hFiberValue.clm_apply (continuous_const : Continuous (fun _ : Parameter ↦ jet.value))
  have hFirstDerivative : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).firstDerivative) := by
    rw [continuous_clm_apply]
    intro direction
    have hBaseApply : Continuous (fun point ↦
        (change point).baseFirst direction) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ direction))
    have hSourceDerivative : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst direction)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseApply
    have hTransportedDerivative : Continuous (fun point ↦
        (change point).fiberValue
          (jet.firstDerivative ((change point).baseFirst direction))) :=
      hFiberValue.clm_apply hSourceDerivative
    have hFiberFirstApply : Continuous (fun point ↦
        (change point).fiberFirst direction) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ direction))
    have hFiberFirstValue : Continuous (fun point ↦
        (change point).fiberFirst direction jet.value) :=
      hFiberFirstApply.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ jet.value))
    change Continuous (fun point ↦
      (change point).fiberValue
          (jet.firstDerivative ((change point).baseFirst direction)) +
        (change point).fiberFirst direction jet.value)
    convert hTransportedDerivative.add hFiberFirstValue using 1
    funext point
    rfl
  have hSecondDerivative : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).secondDerivative) := by
    rw [continuous_clm_apply]
    intro first
    rw [continuous_clm_apply]
    intro second
    have hBaseFirstApply : Continuous (fun point ↦
        (change point).baseFirst first) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hBaseSecondApply : Continuous (fun point ↦
        (change point).baseFirst second) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hJetSecondFirst : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply hBaseFirstApply
    have hJetSecond : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)) :=
      hJetSecondFirst.clm_apply hBaseSecondApply
    have hFirstTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst second))) :=
      hFiberValue.clm_apply hJetSecond
    have hBaseSecondFirst : Continuous (fun point ↦
        (change point).baseSecond first) :=
      hBaseSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hBaseSecondBoth : Continuous (fun point ↦
        (change point).baseSecond first second) :=
      hBaseSecondFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hJetFirstBaseSecond : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseSecond first second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseSecondBoth
    have hSecondTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.firstDerivative ((change point).baseSecond first second))) :=
      hFiberValue.clm_apply hJetFirstBaseSecond
    have hFiberFirstFirst : Continuous (fun point ↦
        (change point).fiberFirst first) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hJetFirstSecond : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseSecondApply
    have hThirdTerm : Continuous (fun point ↦
        (change point).fiberFirst first
          (jet.firstDerivative ((change point).baseFirst second))) :=
      hFiberFirstFirst.clm_apply hJetFirstSecond
    have hFiberFirstSecond : Continuous (fun point ↦
        (change point).fiberFirst second) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hJetFirstFirst : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst first)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseFirstApply
    have hFourthTerm : Continuous (fun point ↦
        (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseFirst first))) :=
      hFiberFirstSecond.clm_apply hJetFirstFirst
    have hFiberSecondFirst : Continuous (fun point ↦
        (change point).fiberSecond first) :=
      (ContinuousLinearMap.apply Real
        (X →L[Real] V →L[Real] V) first).continuous.comp hFiberSecond
    have hFiberSecondBoth : Continuous (fun point ↦
        (change point).fiberSecond first second) :=
      (ContinuousLinearMap.apply Real
        (V →L[Real] V) second).continuous.comp hFiberSecondFirst
    have hFifthTerm : Continuous (fun point ↦
        (change point).fiberSecond first second jet.value) :=
      (ContinuousLinearMap.apply Real V jet.value).continuous.comp
        hFiberSecondBoth
    change Continuous (fun point ↦
      (change point).fiberValue
            (jet.secondDerivative ((change point).baseFirst first)
              ((change point).baseFirst second)) +
          (change point).fiberValue
            (jet.firstDerivative ((change point).baseSecond first second)) +
        (change point).fiberFirst first
            (jet.firstDerivative ((change point).baseFirst second)) +
      (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseFirst first)) +
      (change point).fiberSecond first second jet.value)
    convert
      ((((hFirstTerm.add hSecondTerm).add hThirdTerm).add hFourthTerm).add
        hFifthTerm) using 1
    funext point
    rfl
  have hComponents : Continuous (fun point ↦
      (((change point).toContinuousLinearMap jet).value,
        ((change point).toContinuousLinearMap jet).firstDerivative,
        ((change point).toContinuousLinearMap jet).secondDerivative)) :=
    hValue.prodMk (hFirstDerivative.prodMk hSecondDerivative)
  let componentEquiv :=
    framedSecondOrderJetLinearIsometryEquivSymmetricSubmodule X V
  have hSubtype : Continuous (fun point ↦
      componentEquiv ((change point).toContinuousLinearMap jet)) := by
    exact hComponents.subtype_mk _
  have hBack := componentEquiv.symm.continuous.comp hSubtype
  convert hBack using 1
  funext point
  exact (componentEquiv.symm_apply_apply _).symm

end
end P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
end JanusFormal
