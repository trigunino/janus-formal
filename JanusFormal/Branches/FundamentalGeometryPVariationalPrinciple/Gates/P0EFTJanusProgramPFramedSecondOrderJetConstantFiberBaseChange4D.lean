import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

/-!
# Constant-fiber base changes for framed second-order jets

A second-order change of base coordinates acts on jets of maps into a fixed
fiber.  The fiber action is the identity and its first and second derivatives
vanish.  This is the reusable specialization needed by globally trivial
field slots such as the three LL fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

variable
    (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base]

/-- The two base-coordinate coefficients needed to transport a second jet
whose fiber is globally fixed. -/
structure FramedSecondOrderJetConstantFiberBaseChange where
  baseFirst : Base →L[Real] Base
  baseSecond : Base →L[Real] Base →L[Real] Base
  baseSecond_symmetric :
    ∀ first second, baseSecond first second = baseSecond second first

namespace FramedSecondOrderJetConstantFiberBaseChange

variable
    {Base : Type*}
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- The constant-fiber specialization of the generic five-term semidirect
change. -/
def toSemidirectChange
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    FramedSecondOrderJetSemidirectChange Base Fiber where
  baseFirst := change.baseFirst
  baseSecond := change.baseSecond
  baseSecond_symmetric := change.baseSecond_symmetric
  fiberValue := ContinuousLinearMap.id Real Fiber
  fiberFirst := 0
  fiberSecond := 0
  fiberSecond_symmetric := by
    intro first second
    rfl

@[simp]
theorem toSemidirectChange_baseFirst
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    (change.toSemidirectChange (Fiber := Fiber)).baseFirst =
      change.baseFirst :=
  rfl

@[simp]
theorem toSemidirectChange_baseSecond
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    (change.toSemidirectChange (Fiber := Fiber)).baseSecond =
      change.baseSecond :=
  rfl

@[simp]
theorem toSemidirectChange_fiberValue
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    (change.toSemidirectChange (Fiber := Fiber)).fiberValue =
      ContinuousLinearMap.id Real Fiber :=
  rfl

@[simp]
theorem toSemidirectChange_fiberFirst
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    (change.toSemidirectChange (Fiber := Fiber)).fiberFirst = 0 :=
  rfl

@[simp]
theorem toSemidirectChange_fiberSecond
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    (change.toSemidirectChange (Fiber := Fiber)).fiberSecond = 0 :=
  rfl

/-- Transport of a framed second jet through a constant-fiber base change. -/
def transport
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) :
    FramedSecondOrderJet Base Fiber :=
  (change.toSemidirectChange (Fiber := Fiber)).transport jet

@[simp]
theorem transport_value
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) :
    (change.transport jet).value = jet.value := by
  simp only [transport,
    FramedSecondOrderJetSemidirectChange.transport_value,
    toSemidirectChange_fiberValue,
    ContinuousLinearMap.id_apply]

@[simp]
theorem transport_firstDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) (direction : Base) :
    (change.transport jet).firstDerivative direction =
      jet.firstDerivative (change.baseFirst direction) := by
  simp only [transport,
    FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
    toSemidirectChange_baseFirst, toSemidirectChange_fiberValue,
    toSemidirectChange_fiberFirst, ContinuousLinearMap.id_apply,
    zero_apply, add_zero]

@[simp]
theorem transport_secondDerivative_apply
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) (first second : Base) :
    (change.transport jet).secondDerivative first second =
      jet.secondDerivative
          (change.baseFirst first) (change.baseFirst second) +
        jet.firstDerivative (change.baseSecond first second) := by
  simp only [transport,
    FramedSecondOrderJetSemidirectChange.transport_secondDerivative_apply,
    toSemidirectChange_baseFirst, toSemidirectChange_baseSecond,
    toSemidirectChange_fiberValue, toSemidirectChange_fiberFirst,
    toSemidirectChange_fiberSecond, ContinuousLinearMap.id_apply,
    zero_apply, add_zero]

/-- Linear transport on the full constant-fiber jet carrier. -/
def toLinearMap
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    FramedSecondOrderJet Base Fiber →ₗ[Real]
      FramedSecondOrderJet Base Fiber :=
  (change.toSemidirectChange (Fiber := Fiber)).toLinearMap

@[simp]
theorem toLinearMap_apply
    [FiniteDimensional Real Base]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) :
    change.toLinearMap jet = change.transport jet :=
  rfl

/-- Continuous linear transport when both the base and fixed fiber are
finite-dimensional. -/
def toContinuousLinearMap
    [FiniteDimensional Real Base] [FiniteDimensional Real Fiber]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base) :
    FramedSecondOrderJet Base Fiber →L[Real]
      FramedSecondOrderJet Base Fiber :=
  (change.toSemidirectChange (Fiber := Fiber)).toContinuousLinearMap

@[simp]
theorem toContinuousLinearMap_apply
    [FiniteDimensional Real Base] [FiniteDimensional Real Fiber]
    (change : FramedSecondOrderJetConstantFiberBaseChange Base)
    (jet : FramedSecondOrderJet Base Fiber) :
    change.toContinuousLinearMap jet = change.transport jet :=
  rfl

/-- Identity base change. -/
def identity : FramedSecondOrderJetConstantFiberBaseChange Base where
  baseFirst := ContinuousLinearMap.id Real Base
  baseSecond := 0
  baseSecond_symmetric := by
    intro first second
    rfl

@[simp]
theorem identity_transport
    [FiniteDimensional Real Base]
    (jet : FramedSecondOrderJet Base Fiber) :
    (identity (Base := Base)).transport jet = jet := by
  apply FramedSecondOrderJet.ext_components
  · simp
  · ext direction
    simp [identity]
  · ext first second
    simp [identity]

/-- Composition law under the explicit first- and second-order chain-rule
hypotheses.  This avoids imposing an independent composition structure on
base changes. -/
theorem transport_comp_of_base_coefficients
    [FiniteDimensional Real Base]
    (first second composite :
      FramedSecondOrderJetConstantFiberBaseChange Base)
    (hFirst : composite.baseFirst =
      first.baseFirst.comp second.baseFirst)
    (hSecond : ∀ firstDirection secondDirection,
      composite.baseSecond firstDirection secondDirection =
        first.baseSecond
            (second.baseFirst firstDirection)
            (second.baseFirst secondDirection) +
          first.baseFirst
            (second.baseSecond firstDirection secondDirection))
    (jet : FramedSecondOrderJet Base Fiber) :
    composite.transport jet =
      second.transport (first.transport jet) := by
  apply FramedSecondOrderJet.ext_components
  · simp
  · ext direction
    simp only [transport_firstDerivative_apply]
    rw [hFirst]
    rfl
  · ext firstDirection secondDirection
    simp only [transport_secondDerivative_apply]
    rw [hFirst, hSecond]
    simp only [ContinuousLinearMap.comp_apply, map_add,
      transport_firstDerivative_apply]
    abel

end FramedSecondOrderJetConstantFiberBaseChange

end
end P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
end JanusFormal
