import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetNormedSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D

/-!
# Continuity of generic semidirect third-jet transport

Continuous families of the seven frozen base/fiber coefficients induce a
continuous family of continuous linear maps on framed third jets.
-/

namespace JanusFormal

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D

namespace P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D.FramedThirdOrderJetSemidirectChange

set_option autoImplicit false

noncomputable section

variable
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]

/-- Continuous-linear packaging of third-order semidirect transport. -/
def toContinuousLinearMap
    (change : FramedThirdOrderJetSemidirectChange X V) :
    FramedThirdOrderJet X V →L[Real] FramedThirdOrderJet X V :=
  LinearMap.toContinuousLinearMap change.toLinearMap

@[simp]
theorem toContinuousLinearMap_apply
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    change.toContinuousLinearMap jet = change.transport jet :=
  rfl

end
end P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D.FramedThirdOrderJetSemidirectChange

namespace P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable
    {Parameter X V : Type*}
    [TopologicalSpace Parameter]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]

private abbrev JetFirstDerivative := X →L[Real] V

local instance jetFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetFirstDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetFirstDerivativeNormedSpace :
    NormedSpace Real (JetFirstDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev JetSecondDerivative :=
  X →L[Real] JetFirstDerivative (X := X) (V := V)

local instance jetSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetSecondDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSecondDerivativeNormedSpace :
    NormedSpace Real (JetSecondDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev JetThirdDerivative :=
  X →L[Real] JetSecondDerivative (X := X) (V := V)

local instance jetThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetThirdDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetThirdDerivativeNormedSpace :
    NormedSpace Real (JetThirdDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberEndomorphism := V →L[Real] V

local instance fiberEndomorphismNormedAddCommGroup :
    NormedAddCommGroup (FiberEndomorphism (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberEndomorphismNormedSpace :
    NormedSpace Real (FiberEndomorphism (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberFirstCoefficient :=
  X →L[Real] FiberEndomorphism (V := V)

local instance fiberFirstCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberFirstCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberFirstCoefficientNormedSpace :
    NormedSpace Real (FiberFirstCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberSecondCoefficient :=
  X →L[Real] FiberFirstCoefficient (X := X) (V := V)

local instance fiberSecondCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberSecondCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberSecondCoefficientNormedSpace :
    NormedSpace Real (FiberSecondCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberThirdCoefficient :=
  X →L[Real] FiberSecondCoefficient (X := X) (V := V)

local instance fiberThirdCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberThirdCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberThirdCoefficientNormedSpace :
    NormedSpace Real (FiberThirdCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

/-- The third-order semidirect action depends continuously on any continuous
family of its seven coefficient fields.  Symmetry witnesses are proof data and
do not enter the topology. -/
theorem continuous_semidirectTransport
    (change : Parameter → FramedThirdOrderJetSemidirectChange X V)
    (hBaseFirst : Continuous (fun point ↦ (change point).baseFirst))
    (hBaseSecond : Continuous (fun point ↦ (change point).baseSecond))
    (hBaseThird : Continuous (fun point ↦ (change point).baseThird))
    (hFiberValue : Continuous (fun point ↦ (change point).fiberValue))
    (hFiberFirst : Continuous (fun point ↦ (change point).fiberFirst))
    (hFiberSecond : Continuous (fun point ↦ (change point).fiberSecond))
    (hFiberThird : Continuous (fun point ↦ (change point).fiberThird)) :
    Continuous (fun point ↦
      (change point).toContinuousLinearMap) := by
  rw [continuous_clm_apply]
  intro jet
  have hLowerMap : Continuous (fun point ↦
      (change point).toFramedSecondOrderJetSemidirectChange.toContinuousLinearMap) :=
    P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D.continuous_semidirectTransport
      (fun point ↦ (change point).toFramedSecondOrderJetSemidirectChange)
      hBaseFirst hBaseSecond hFiberValue hFiberFirst hFiberSecond
  have hLowerJet : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).toFramedSecondOrderJet) := by
    simpa only [FramedThirdOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedThirdOrderJetSemidirectChange.transport_toFramedSecondOrderJet,
      FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply] using
      hLowerMap.clm_apply
        (continuous_const : Continuous
          (fun _ : Parameter ↦ jet.toFramedSecondOrderJet))
  have hThirdDerivative : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).thirdDerivative) := by
    rw [continuous_clm_apply]
    intro first
    rw [continuous_clm_apply]
    intro second
    rw [continuous_clm_apply]
    intro third
    have hBaseFirstFirst : Continuous (fun point ↦
        (change point).baseFirst first) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hBaseFirstSecond : Continuous (fun point ↦
        (change point).baseFirst second) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hBaseFirstThird : Continuous (fun point ↦
        (change point).baseFirst third) :=
      hBaseFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hBaseSecondFirst : Continuous (fun point ↦
        (change point).baseSecond first) :=
      hBaseSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hBaseSecondFirstSecond : Continuous (fun point ↦
        (change point).baseSecond first second) :=
      hBaseSecondFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hBaseSecondFirstThird : Continuous (fun point ↦
        (change point).baseSecond first third) :=
      hBaseSecondFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hBaseSecondSecond : Continuous (fun point ↦
        (change point).baseSecond second) :=
      hBaseSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hBaseSecondSecondThird : Continuous (fun point ↦
        (change point).baseSecond second third) :=
      hBaseSecondSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hBaseThirdFirst : Continuous (fun point ↦
        (change point).baseThird first) :=
      hBaseThird.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hBaseThirdFirstSecond : Continuous (fun point ↦
        (change point).baseThird first second) :=
      hBaseThirdFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hBaseThirdFirstSecondThird : Continuous (fun point ↦
        (change point).baseThird first second third) :=
      hBaseThirdFirstSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hFiberFirstFirst : Continuous (fun point ↦
        (change point).fiberFirst first) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hFiberFirstSecond : Continuous (fun point ↦
        (change point).fiberFirst second) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hFiberFirstThird : Continuous (fun point ↦
        (change point).fiberFirst third) :=
      hFiberFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hFiberSecondFirst : Continuous (fun point ↦
        (change point).fiberSecond first) :=
      hFiberSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hFiberSecondFirstSecond : Continuous (fun point ↦
        (change point).fiberSecond first second) :=
      hFiberSecondFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hFiberSecondFirstThird : Continuous (fun point ↦
        (change point).fiberSecond first third) :=
      hFiberSecondFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hFiberSecondSecond : Continuous (fun point ↦
        (change point).fiberSecond second) :=
      hFiberSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hFiberSecondSecondThird : Continuous (fun point ↦
        (change point).fiberSecond second third) :=
      hFiberSecondSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hFiberThirdFirst : Continuous (fun point ↦
        (change point).fiberThird first) :=
      hFiberThird.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ first))
    have hFiberThirdFirstSecond : Continuous (fun point ↦
        (change point).fiberThird first second) :=
      hFiberThirdFirst.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ second))
    have hFiberThirdFirstSecondThird : Continuous (fun point ↦
        (change point).fiberThird first second third) :=
      hFiberThirdFirstSecond.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ third))
    have hJetThirdFirst : Continuous (fun point ↦
        jet.thirdDerivative ((change point).baseFirst first)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.thirdDerivative)).clm_apply hBaseFirstFirst
    have hJetThirdFirstSecond : Continuous (fun point ↦
        jet.thirdDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)) :=
      hJetThirdFirst.clm_apply hBaseFirstSecond
    have hJetThird : Continuous (fun point ↦
        jet.thirdDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)
          ((change point).baseFirst third)) :=
      hJetThirdFirstSecond.clm_apply hBaseFirstThird
    have hFirstTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.thirdDerivative ((change point).baseFirst first)
            ((change point).baseFirst second)
            ((change point).baseFirst third))) :=
      hFiberValue.clm_apply hJetThird
    have hJetSecondBaseSecondFirstSecond : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond first second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply
          hBaseSecondFirstSecond
    have hJetSecondBaseSecondFirstSecondBaseFirstThird : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond first second)
          ((change point).baseFirst third)) :=
      hJetSecondBaseSecondFirstSecond.clm_apply hBaseFirstThird
    have hSecondTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond first second)
            ((change point).baseFirst third))) :=
      hFiberValue.clm_apply hJetSecondBaseSecondFirstSecondBaseFirstThird
    have hJetSecondBaseSecondFirstThird : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond first third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply
          hBaseSecondFirstThird
    have hJetSecondBaseSecondFirstThirdBaseFirstSecond : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond first third)
          ((change point).baseFirst second)) :=
      hJetSecondBaseSecondFirstThird.clm_apply hBaseFirstSecond
    have hThirdTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond first third)
            ((change point).baseFirst second))) :=
      hFiberValue.clm_apply hJetSecondBaseSecondFirstThirdBaseFirstSecond
    have hJetSecondBaseSecondSecondThird : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond second third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply
          hBaseSecondSecondThird
    have hJetSecondBaseSecondSecondThirdBaseFirstFirst : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseSecond second third)
          ((change point).baseFirst first)) :=
      hJetSecondBaseSecondSecondThird.clm_apply hBaseFirstFirst
    have hFourthTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond second third)
            ((change point).baseFirst first))) :=
      hFiberValue.clm_apply hJetSecondBaseSecondSecondThirdBaseFirstFirst
    have hJetFirstBaseThird : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseThird first second third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply
          hBaseThirdFirstSecondThird
    have hFifthTerm : Continuous (fun point ↦
        (change point).fiberValue
          (jet.firstDerivative ((change point).baseThird first second third))) :=
      hFiberValue.clm_apply hJetFirstBaseThird
    have hJetSecondBaseFirstSecond : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply hBaseFirstSecond
    have hJetSecondBaseFirstSecondThird : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst second)
          ((change point).baseFirst third)) :=
      hJetSecondBaseFirstSecond.clm_apply hBaseFirstThird
    have hSixthTerm : Continuous (fun point ↦
        (change point).fiberFirst first
          (jet.secondDerivative ((change point).baseFirst second)
            ((change point).baseFirst third))) :=
      hFiberFirstFirst.clm_apply hJetSecondBaseFirstSecondThird
    have hJetSecondBaseFirstFirst : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.secondDerivative)).clm_apply hBaseFirstFirst
    have hJetSecondBaseFirstFirstThird : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst third)) :=
      hJetSecondBaseFirstFirst.clm_apply hBaseFirstThird
    have hSeventhTerm : Continuous (fun point ↦
        (change point).fiberFirst second
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst third))) :=
      hFiberFirstSecond.clm_apply hJetSecondBaseFirstFirstThird
    have hJetSecondBaseFirstFirstSecond : Continuous (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)) :=
      hJetSecondBaseFirstFirst.clm_apply hBaseFirstSecond
    have hEighthTerm : Continuous (fun point ↦
        (change point).fiberFirst third
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst second))) :=
      hFiberFirstThird.clm_apply hJetSecondBaseFirstFirstSecond
    have hJetFirstBaseSecondSecondThird : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseSecond second third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply
          hBaseSecondSecondThird
    have hNinthTerm : Continuous (fun point ↦
        (change point).fiberFirst first
          (jet.firstDerivative ((change point).baseSecond second third))) :=
      hFiberFirstFirst.clm_apply hJetFirstBaseSecondSecondThird
    have hJetFirstBaseSecondFirstThird : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseSecond first third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply
          hBaseSecondFirstThird
    have hTenthTerm : Continuous (fun point ↦
        (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseSecond first third))) :=
      hFiberFirstSecond.clm_apply hJetFirstBaseSecondFirstThird
    have hJetFirstBaseSecondFirstSecond : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseSecond first second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply
          hBaseSecondFirstSecond
    have hEleventhTerm : Continuous (fun point ↦
        (change point).fiberFirst third
          (jet.firstDerivative ((change point).baseSecond first second))) :=
      hFiberFirstThird.clm_apply hJetFirstBaseSecondFirstSecond
    have hJetFirstBaseFirstThird : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst third)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseFirstThird
    have hTwelfthTerm : Continuous (fun point ↦
        (change point).fiberSecond first second
          (jet.firstDerivative ((change point).baseFirst third))) :=
      hFiberSecondFirstSecond.clm_apply hJetFirstBaseFirstThird
    have hJetFirstBaseFirstSecond : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst second)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseFirstSecond
    have hThirteenthTerm : Continuous (fun point ↦
        (change point).fiberSecond first third
          (jet.firstDerivative ((change point).baseFirst second))) :=
      hFiberSecondFirstThird.clm_apply hJetFirstBaseFirstSecond
    have hJetFirstBaseFirstFirst : Continuous (fun point ↦
        jet.firstDerivative ((change point).baseFirst first)) :=
      (continuous_const : Continuous
        (fun _ : Parameter ↦ jet.firstDerivative)).clm_apply hBaseFirstFirst
    have hFourteenthTerm : Continuous (fun point ↦
        (change point).fiberSecond second third
          (jet.firstDerivative ((change point).baseFirst first))) :=
      hFiberSecondSecondThird.clm_apply hJetFirstBaseFirstFirst
    have hFifteenthTerm : Continuous (fun point ↦
        (change point).fiberThird first second third jet.value) :=
      hFiberThirdFirstSecondThird.clm_apply
        (continuous_const : Continuous (fun _ : Parameter ↦ jet.value))
    change Continuous (fun point ↦
      (change point).fiberValue
          (jet.thirdDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst second)
            ((change point).baseFirst third)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond first second)
            ((change point).baseFirst third)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond first third)
            ((change point).baseFirst second)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond second third)
            ((change point).baseFirst first)) +
        (change point).fiberValue
          (jet.firstDerivative
            ((change point).baseThird first second third)) +
        (change point).fiberFirst first
          (jet.secondDerivative
            ((change point).baseFirst second)
            ((change point).baseFirst third)) +
        (change point).fiberFirst second
          (jet.secondDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst third)) +
        (change point).fiberFirst third
          (jet.secondDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst second)) +
        (change point).fiberFirst first
          (jet.firstDerivative
            ((change point).baseSecond second third)) +
        (change point).fiberFirst second
          (jet.firstDerivative
            ((change point).baseSecond first third)) +
        (change point).fiberFirst third
          (jet.firstDerivative
            ((change point).baseSecond first second)) +
        (change point).fiberSecond first second
          (jet.firstDerivative ((change point).baseFirst third)) +
        (change point).fiberSecond first third
          (jet.firstDerivative ((change point).baseFirst second)) +
        (change point).fiberSecond second third
          (jet.firstDerivative ((change point).baseFirst first)) +
        (change point).fiberThird first second third jet.value)
    exact ((((((((((((((hFirstTerm.add hSecondTerm).add hThirdTerm).add
      hFourthTerm).add hFifthTerm).add hSixthTerm).add hSeventhTerm).add
      hEighthTerm).add hNinthTerm).add hTenthTerm).add hEleventhTerm).add
      hTwelfthTerm).add hThirteenthTerm).add hFourteenthTerm).add
      hFifteenthTerm)
  let componentEquiv :=
    framedSecondOrderJetLinearIsometryEquivSymmetricSubmodule X V
  have hLowerSubtype : Continuous (fun point ↦
      componentEquiv
        ((change point).toContinuousLinearMap jet).toFramedSecondOrderJet) :=
    componentEquiv.continuous.comp hLowerJet
  have hLowerComponents : Continuous (fun point ↦
      (componentEquiv
        ((change point).toContinuousLinearMap jet).toFramedSecondOrderJet).1) :=
    continuous_subtype_val.comp hLowerSubtype
  have hValue : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).value) := by
    convert hLowerComponents.fst using 1
    funext point
    rfl
  have hFirstDerivative : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).firstDerivative) := by
    convert hLowerComponents.snd.fst using 1
    funext point
    rfl
  have hSecondDerivative : Continuous (fun point ↦
      ((change point).toContinuousLinearMap jet).secondDerivative) := by
    convert hLowerComponents.snd.snd using 1
    funext point
    rfl
  apply continuous_induced_rng.mpr
  change Continuous (fun point ↦
    (((change point).toContinuousLinearMap jet).value,
      ((change point).toContinuousLinearMap jet).firstDerivative,
      ((change point).toContinuousLinearMap jet).secondDerivative,
      ((change point).toContinuousLinearMap jet).thirdDerivative))
  exact hValue.prodMk
    (hFirstDerivative.prodMk (hSecondDerivative.prodMk hThirdDerivative))

end
end P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D
end JanusFormal
