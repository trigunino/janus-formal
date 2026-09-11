import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetLinearStructure4D

/-!
# Generic semidirect transport of framed third-order jets

A frozen third-order base-coordinate and fiber-frame change acts on a framed
third jet by the third-order chain and Leibniz rule.  Truncation is exactly the
existing second-order semidirect transport.  No geometric transition,
groupoid law, or quotient descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

variable
    (X V : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]

/-- Frozen third-order base and fiber transition coefficients. -/
structure FramedThirdOrderJetSemidirectChange
    extends FramedSecondOrderJetSemidirectChange X V where
  baseThird : X →L[Real] X →L[Real] X →L[Real] X
  baseThird_swap_first_second :
    ∀ first second third,
      baseThird first second third = baseThird second first third
  baseThird_swap_second_third :
    ∀ first second third,
      baseThird first second third = baseThird first third second
  fiberThird : X →L[Real] X →L[Real] X →L[Real] V →L[Real] V
  fiberThird_swap_first_second :
    ∀ first second third,
      fiberThird first second third = fiberThird second first third
  fiberThird_swap_second_third :
    ∀ first second third,
      fiberThird first second third = fiberThird first third second

namespace FramedThirdOrderJetSemidirectChange

variable
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]

private def transportThirdDerivativeFormula
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) : V :=
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
    change.fiberThird first second third jet.value

private def transportThirdDerivativeInnerLinearMap
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second : X) : X →ₗ[Real] V where
  toFun := change.transportThirdDerivativeFormula jet first second
  map_add' third fourth := by
    simp only [transportThirdDerivativeFormula, map_add, add_apply]
    abel
  map_smul' scalar third := by
    simp only [transportThirdDerivativeFormula, map_smul,
      RingHom.id_apply, smul_apply]
    module

private def transportThirdDerivativeMiddleLinearMap
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first : X) : X →ₗ[Real] X →L[Real] V where
  toFun second :=
    LinearMap.toContinuousLinearMap
      (change.transportThirdDerivativeInnerLinearMap jet first second)
  map_add' second third := by
    ext fourth
    change
      change.transportThirdDerivativeFormula jet first (second + third) fourth =
        change.transportThirdDerivativeFormula jet first second fourth +
          change.transportThirdDerivativeFormula jet first third fourth
    simp only [transportThirdDerivativeFormula, map_add, add_apply]
    abel
  map_smul' scalar second := by
    ext third
    change
      change.transportThirdDerivativeFormula jet first (scalar • second) third =
        scalar • change.transportThirdDerivativeFormula jet first second third
    simp only [transportThirdDerivativeFormula, map_smul, smul_apply]
    module

private def transportThirdDerivativeLinearMap
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    X →ₗ[Real] X →L[Real] X →L[Real] V where
  toFun first :=
    LinearMap.toContinuousLinearMap
      (change.transportThirdDerivativeMiddleLinearMap jet first)
  map_add' first second := by
    ext third fourth
    change
      change.transportThirdDerivativeFormula jet (first + second) third fourth =
        change.transportThirdDerivativeFormula jet first third fourth +
          change.transportThirdDerivativeFormula jet second third fourth
    simp only [transportThirdDerivativeFormula, map_add, add_apply]
    abel
  map_smul' scalar first := by
    ext second third
    change
      change.transportThirdDerivativeFormula jet (scalar • first) second third =
        scalar • change.transportThirdDerivativeFormula jet first second third
    simp only [transportThirdDerivativeFormula, map_smul, smul_apply]
    module

private theorem transportThirdDerivativeFormula_swap_first_second
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) :
    change.transportThirdDerivativeFormula jet first second third =
      change.transportThirdDerivativeFormula jet second first third := by
  simp only [transportThirdDerivativeFormula]
  rw [jet.thirdDerivative_swap_first_second
    (change.baseFirst first) (change.baseFirst second)
    (change.baseFirst third)]
  rw [change.baseSecond_symmetric first second]
  rw [change.baseThird_swap_first_second first second third]
  rw [jet.secondDerivative_symmetric
    (change.baseFirst first) (change.baseFirst second)]
  rw [change.fiberSecond_symmetric first second]
  rw [change.fiberThird_swap_first_second first second third]
  abel

private theorem transportThirdDerivativeFormula_swap_second_third
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) :
    change.transportThirdDerivativeFormula jet first second third =
      change.transportThirdDerivativeFormula jet first third second := by
  simp only [transportThirdDerivativeFormula]
  rw [jet.thirdDerivative_swap_second_third
    (change.baseFirst first) (change.baseFirst second)
    (change.baseFirst third)]
  rw [change.baseSecond_symmetric second third]
  rw [change.baseThird_swap_second_third first second third]
  rw [jet.secondDerivative_symmetric
    (change.baseFirst second) (change.baseFirst third)]
  rw [change.fiberSecond_symmetric second third]
  rw [change.fiberThird_swap_second_third first second third]
  abel

/-- Continuous symmetric third derivative of the transported jet. -/
def transportThirdDerivative
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    X →L[Real] X →L[Real] X →L[Real] V :=
  LinearMap.toContinuousLinearMap
    (change.transportThirdDerivativeLinearMap jet)

@[simp]
theorem transportThirdDerivative_apply
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) :
    change.transportThirdDerivative jet first second third =
      change.transportThirdDerivativeFormula jet first second third :=
  rfl

/-- Third-order semidirect transport with exact second-order truncation. -/
def transport
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) : FramedThirdOrderJet X V where
  toFramedSecondOrderJet :=
    change.toFramedSecondOrderJetSemidirectChange.transport
      jet.toFramedSecondOrderJet
  thirdDerivative := change.transportThirdDerivative jet
  thirdDerivative_swap_first_second first second third :=
    change.transportThirdDerivativeFormula_swap_first_second
      jet first second third
  thirdDerivative_swap_second_third first second third :=
    change.transportThirdDerivativeFormula_swap_second_third
      jet first second third

@[simp]
theorem transport_toFramedSecondOrderJet
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    (change.transport jet).toFramedSecondOrderJet =
      change.toFramedSecondOrderJetSemidirectChange.transport
        jet.toFramedSecondOrderJet :=
  rfl

/-- The third-order semidirect transport is linear in the source jet. -/
def toLinearMap
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V) :
    FramedThirdOrderJet X V →ₗ[Real] FramedThirdOrderJet X V where
  toFun := change.transport
  map_add' left right := by
    apply FramedThirdOrderJet.ext_components
    · simpa only [transport_toFramedSecondOrderJet,
        FramedThirdOrderJet.add_toFramedSecondOrderJet,
        FramedSecondOrderJetSemidirectChange.toLinearMap_apply] using
        change.toFramedSecondOrderJetSemidirectChange.toLinearMap.map_add
          left.toFramedSecondOrderJet right.toFramedSecondOrderJet
    · ext first second third
      simp only [transport, transportThirdDerivative_apply,
        transportThirdDerivativeFormula,
        FramedThirdOrderJet.add_value,
        FramedThirdOrderJet.add_firstDerivative,
        FramedThirdOrderJet.add_secondDerivative,
        FramedThirdOrderJet.add_thirdDerivative, add_apply, map_add]
      abel
  map_smul' scalar jet := by
    apply FramedThirdOrderJet.ext_components
    · simpa only [transport_toFramedSecondOrderJet,
        FramedThirdOrderJet.smul_toFramedSecondOrderJet,
        FramedSecondOrderJetSemidirectChange.toLinearMap_apply,
        RingHom.id_apply] using
        change.toFramedSecondOrderJetSemidirectChange.toLinearMap.map_smul
          scalar jet.toFramedSecondOrderJet
    · ext first second third
      simp only [transport, transportThirdDerivative_apply,
        transportThirdDerivativeFormula,
        FramedThirdOrderJet.smul_value,
        FramedThirdOrderJet.smul_firstDerivative,
        FramedThirdOrderJet.smul_secondDerivative,
        FramedThirdOrderJet.smul_thirdDerivative,
        smul_apply, map_smul, RingHom.id_apply]
      module

@[simp]
theorem toLinearMap_apply
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V) :
    change.toLinearMap jet = change.transport jet :=
  rfl

@[simp]
theorem transport_thirdDerivative_apply
    [FiniteDimensional Real X]
    (change : FramedThirdOrderJetSemidirectChange X V)
    (jet : FramedThirdOrderJet X V)
    (first second third : X) :
    (change.transport jet).thirdDerivative first second third =
      change.transportThirdDerivativeFormula jet first second third :=
  rfl

end FramedThirdOrderJetSemidirectChange

end
end P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
end JanusFormal
