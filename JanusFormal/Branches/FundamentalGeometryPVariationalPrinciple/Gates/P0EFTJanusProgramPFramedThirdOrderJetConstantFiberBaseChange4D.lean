import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D

/-!
# Constant-fiber base changes for framed third-order jets

This gate extends the framed second-jet carrier by one symmetric trilinear
derivative and transports it through a third-order base-coordinate change.
The fiber is fixed, so the third derivative is the five-term third-order chain
rule.  No physical third-jet realization or atlas-specific coefficient is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D

variable
    (Base Fiber : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- A framed third jet over the existing framed second-jet carrier.  The two
adjacent transpositions generate full symmetry of the third derivative. -/
structure FramedThirdOrderJet extends FramedSecondOrderJet Base Fiber where
  thirdDerivative : Base →L[Real] Base →L[Real] Base →L[Real] Fiber
  thirdDerivative_swap_first_second :
    ∀ first second third,
      thirdDerivative first second third =
        thirdDerivative second first third
  thirdDerivative_swap_second_third :
    ∀ first second third,
      thirdDerivative first second third =
        thirdDerivative first third second

@[ext]
theorem FramedThirdOrderJet.ext_components
    {first second : FramedThirdOrderJet Base Fiber}
    (hSecond :
      first.toFramedSecondOrderJet = second.toFramedSecondOrderJet)
    (hThird : first.thirdDerivative = second.thirdDerivative) :
    first = second := by
  cases first
  cases second
  simp_all

/-- The first three base-coordinate coefficients for a fixed fiber. -/
structure FramedThirdOrderJetConstantFiberBaseChange
    extends FramedSecondOrderJetConstantFiberBaseChange Base where
  baseThird : Base →L[Real] Base →L[Real] Base →L[Real] Base
  baseThird_swap_first_second :
    ∀ first second third,
      baseThird first second third = baseThird second first third
  baseThird_swap_second_third :
    ∀ first second third,
      baseThird first second third = baseThird first third second

namespace FramedThirdOrderJetConstantFiberBaseChange

variable
    {Base Fiber : Type*}
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private def transportThirdDerivativeFormula
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second third : Base) : Fiber :=
  jet.thirdDerivative
      (change.baseFirst first)
      (change.baseFirst second)
      (change.baseFirst third) +
    jet.secondDerivative
      (change.baseSecond first second)
      (change.baseFirst third) +
    jet.secondDerivative
      (change.baseSecond first third)
      (change.baseFirst second) +
    jet.secondDerivative
      (change.baseSecond second third)
      (change.baseFirst first) +
    jet.firstDerivative (change.baseThird first second third)

private def transportThirdDerivativeInnerLinearMap
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second : Base) : Base →ₗ[Real] Fiber where
  toFun := change.transportThirdDerivativeFormula jet first second
  map_add' third fourth := by
    simp only [transportThirdDerivativeFormula, map_add, add_apply]
    abel
  map_smul' scalar third := by
    simp only [transportThirdDerivativeFormula, map_smul,
      RingHom.id_apply, smul_apply]
    module

private def transportThirdDerivativeMiddleLinearMap
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first : Base) : Base →ₗ[Real] Base →L[Real] Fiber where
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
        scalar •
          change.transportThirdDerivativeFormula jet first second third
    simp only [transportThirdDerivativeFormula, map_smul, smul_apply]
    module

private def transportThirdDerivativeLinearMap
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) :
    Base →ₗ[Real] Base →L[Real] Base →L[Real] Fiber where
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
        scalar •
          change.transportThirdDerivativeFormula jet first second third
    simp only [transportThirdDerivativeFormula, map_smul, smul_apply]
    module

private theorem transportThirdDerivativeFormula_swap_first_second
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second third : Base) :
    change.transportThirdDerivativeFormula jet first second third =
      change.transportThirdDerivativeFormula jet second first third := by
  simp only [transportThirdDerivativeFormula]
  rw [jet.thirdDerivative_swap_first_second
    (change.baseFirst first) (change.baseFirst second)
    (change.baseFirst third)]
  rw [change.baseSecond_symmetric first second]
  rw [change.baseThird_swap_first_second first second third]
  abel

private theorem transportThirdDerivativeFormula_swap_second_third
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second third : Base) :
    change.transportThirdDerivativeFormula jet first second third =
      change.transportThirdDerivativeFormula jet first third second := by
  simp only [transportThirdDerivativeFormula]
  rw [jet.thirdDerivative_swap_second_third
    (change.baseFirst first) (change.baseFirst second)
    (change.baseFirst third)]
  rw [change.baseSecond_symmetric second third]
  rw [change.baseThird_swap_second_third first second third]
  abel

/-- Continuous symmetric third derivative after a fixed-fiber base change. -/
def transportThirdDerivative
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) :
    Base →L[Real] Base →L[Real] Base →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (change.transportThirdDerivativeLinearMap jet)

@[simp]
theorem transportThirdDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second third : Base) :
    change.transportThirdDerivative jet first second third =
      change.transportThirdDerivativeFormula jet first second third :=
  rfl

/-- Transport of a framed third jet through a constant-fiber base change. -/
def transport
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) :
    FramedThirdOrderJet Base Fiber where
  toFramedSecondOrderJet :=
    change.toFramedSecondOrderJetConstantFiberBaseChange.transport
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
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) :
    (change.transport jet).toFramedSecondOrderJet =
      change.toFramedSecondOrderJetConstantFiberBaseChange.transport
        jet.toFramedSecondOrderJet :=
  rfl

@[simp]
theorem transport_firstDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) (direction : Base) :
    (change.transport jet).firstDerivative direction =
      jet.firstDerivative (change.baseFirst direction) := by
  exact
    FramedSecondOrderJetConstantFiberBaseChange.transport_firstDerivative_apply
      change.toFramedSecondOrderJetConstantFiberBaseChange
      jet.toFramedSecondOrderJet direction

@[simp]
theorem transport_secondDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) (first second : Base) :
    (change.transport jet).secondDerivative first second =
      jet.secondDerivative
          (change.baseFirst first) (change.baseFirst second) +
        jet.firstDerivative (change.baseSecond first second) := by
  exact
    FramedSecondOrderJetConstantFiberBaseChange.transport_secondDerivative_apply
      change.toFramedSecondOrderJetConstantFiberBaseChange
      jet.toFramedSecondOrderJet first second

@[simp]
theorem transport_thirdDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber)
    (first second third : Base) :
    (change.transport jet).thirdDerivative first second third =
      jet.thirdDerivative
          (change.baseFirst first)
          (change.baseFirst second)
          (change.baseFirst third) +
        jet.secondDerivative
          (change.baseSecond first second)
          (change.baseFirst third) +
        jet.secondDerivative
          (change.baseSecond first third)
          (change.baseFirst second) +
        jet.secondDerivative
          (change.baseSecond second third)
          (change.baseFirst first) +
        jet.firstDerivative (change.baseThird first second third) :=
  rfl

/-- Identity third-order base change. -/
def identity : FramedThirdOrderJetConstantFiberBaseChange Base where
  toFramedSecondOrderJetConstantFiberBaseChange :=
    FramedSecondOrderJetConstantFiberBaseChange.identity
  baseThird := 0
  baseThird_swap_first_second := by
    intro first second third
    rfl
  baseThird_swap_second_third := by
    intro first second third
    rfl

@[simp]
theorem identity_transport
    [FiniteDimensional Real Base]
    (jet : FramedThirdOrderJet Base Fiber) :
    (identity (Base := Base)).transport jet = jet := by
  apply FramedThirdOrderJet.ext_components
  · exact
      FramedSecondOrderJetConstantFiberBaseChange.identity_transport
        jet.toFramedSecondOrderJet
  · ext first second third
    simp [identity, FramedSecondOrderJetConstantFiberBaseChange.identity]

/-- The third-order coefficient chain rule implies exact composition of the
constant-fiber transports. -/
theorem transport_comp_of_base_coefficients
    [FiniteDimensional Real Base]
    (first second composite :
      FramedThirdOrderJetConstantFiberBaseChange Base)
    (hFirst : composite.baseFirst =
      first.baseFirst.comp second.baseFirst)
    (hSecond : ∀ firstDirection secondDirection,
      composite.baseSecond firstDirection secondDirection =
        first.baseSecond
            (second.baseFirst firstDirection)
            (second.baseFirst secondDirection) +
          first.baseFirst
            (second.baseSecond firstDirection secondDirection))
    (hThird : ∀ firstDirection secondDirection thirdDirection,
      composite.baseThird
          firstDirection secondDirection thirdDirection =
        first.baseThird
            (second.baseFirst firstDirection)
            (second.baseFirst secondDirection)
            (second.baseFirst thirdDirection) +
          first.baseSecond
            (second.baseSecond firstDirection secondDirection)
            (second.baseFirst thirdDirection) +
          first.baseSecond
            (second.baseSecond firstDirection thirdDirection)
            (second.baseFirst secondDirection) +
          first.baseSecond
            (second.baseSecond secondDirection thirdDirection)
            (second.baseFirst firstDirection) +
          first.baseFirst
            (second.baseThird
              firstDirection secondDirection thirdDirection))
    (jet : FramedThirdOrderJet Base Fiber) :
    composite.transport jet =
      second.transport (first.transport jet) := by
  apply FramedThirdOrderJet.ext_components
  · exact
      FramedSecondOrderJetConstantFiberBaseChange.transport_comp_of_base_coefficients
        first.toFramedSecondOrderJetConstantFiberBaseChange
        second.toFramedSecondOrderJetConstantFiberBaseChange
        composite.toFramedSecondOrderJetConstantFiberBaseChange
        hFirst hSecond jet.toFramedSecondOrderJet
  · ext firstDirection secondDirection thirdDirection
    simp only [transport_thirdDerivative_apply]
    rw [hFirst, hThird]
    simp_rw [hSecond]
    simp only [ContinuousLinearMap.comp_apply, map_add, add_apply,
      transport_firstDerivative_apply, transport_secondDerivative_apply]
    abel

end FramedThirdOrderJetConstantFiberBaseChange

end
end P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
end JanusFormal
