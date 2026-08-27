import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetNormedSpace4D

/-!
# Generic semidirect transport of framed second-order jets

A frozen change of base coordinates and fiber frame acts linearly on a
framed second jet.  The base coefficients pull target directions back to the
source coordinates; the fiber coefficients transport source values to the
target frame.  The five-term Hessian formula is the second-order chain and
Leibniz rule.

Continuity of the directionwise derivatives and of the full jet action is
obtained from finite dimensionality.  No geometric throat transition,
groupoid law or quotient descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

variable
    (X V : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]

/-- Frozen second-order base and fiber transition coefficients.  Both base
derivatives read target directions in source coordinates. -/
structure FramedSecondOrderJetSemidirectChange where
  baseFirst : X →L[Real] X
  baseSecond : X →L[Real] X →L[Real] X
  baseSecond_symmetric :
    ∀ first second, baseSecond first second = baseSecond second first
  fiberValue : V →L[Real] V
  fiberFirst : X →L[Real] V →L[Real] V
  fiberSecond : X →L[Real] X →L[Real] V →L[Real] V
  fiberSecond_symmetric :
    ∀ first second, fiberSecond first second = fiberSecond second first

variable {X V}

namespace FramedSecondOrderJetSemidirectChange

variable
    (change : FramedSecondOrderJetSemidirectChange X V)
    [FiniteDimensional Real X]

/-- The first derivative in the target presentation, before automatic
finite-dimensional continuity is attached. -/
private def transportFirstDerivativeLinearMap
    (jet : FramedSecondOrderJet X V) : X →ₗ[Real] V where
  toFun direction :=
    change.fiberValue
        (jet.firstDerivative (change.baseFirst direction)) +
      change.fiberFirst direction jet.value
  map_add' first second := by
    simp only [map_add, add_apply]
    abel
  map_smul' scalar direction := by
    simp only [map_smul, RingHom.id_apply, smul_apply]
    module

/-- Continuous first derivative of the transported jet. -/
def transportFirstDerivative
    (jet : FramedSecondOrderJet X V) : X →L[Real] V :=
  LinearMap.toContinuousLinearMap
    (change.transportFirstDerivativeLinearMap jet)

@[simp]
theorem transportFirstDerivative_apply
    (jet : FramedSecondOrderJet X V) (direction : X) :
    change.transportFirstDerivative jet direction =
      change.fiberValue
          (jet.firstDerivative (change.baseFirst direction)) +
        change.fiberFirst direction jet.value :=
  rfl

/-- For one first direction, the Hessian formula is linear in its second
direction. -/
private def transportSecondDerivativeInnerLinearMap
    (jet : FramedSecondOrderJet X V) (first : X) : X →ₗ[Real] V where
  toFun second :=
    change.fiberValue
        (jet.secondDerivative
          (change.baseFirst first) (change.baseFirst second)) +
      change.fiberValue
        (jet.firstDerivative (change.baseSecond first second)) +
      change.fiberFirst first
        (jet.firstDerivative (change.baseFirst second)) +
      change.fiberFirst second
        (jet.firstDerivative (change.baseFirst first)) +
      change.fiberSecond first second jet.value
  map_add' second third := by
    simp only [map_add, add_apply]
    abel
  map_smul' scalar second := by
    simp only [map_smul, RingHom.id_apply, smul_apply]
    module

omit [FiniteDimensional Real X] in
private theorem transportSecondDerivativeInnerLinearMap_symmetric
    (jet : FramedSecondOrderJet X V) (first second : X) :
    change.transportSecondDerivativeInnerLinearMap jet first second =
      change.transportSecondDerivativeInnerLinearMap jet second first := by
  change
    change.fiberValue
          (jet.secondDerivative
            (change.baseFirst first) (change.baseFirst second)) +
        change.fiberValue
          (jet.firstDerivative (change.baseSecond first second)) +
        change.fiberFirst first
          (jet.firstDerivative (change.baseFirst second)) +
        change.fiberFirst second
          (jet.firstDerivative (change.baseFirst first)) +
        change.fiberSecond first second jet.value =
      change.fiberValue
          (jet.secondDerivative
            (change.baseFirst second) (change.baseFirst first)) +
        change.fiberValue
          (jet.firstDerivative (change.baseSecond second first)) +
        change.fiberFirst second
          (jet.firstDerivative (change.baseFirst first)) +
        change.fiberFirst first
          (jet.firstDerivative (change.baseFirst second)) +
        change.fiberSecond second first jet.value
  rw [jet.secondDerivative_symmetric
    (change.baseFirst first) (change.baseFirst second)]
  rw [change.baseSecond_symmetric first second]
  rw [change.fiberSecond_symmetric first second]
  abel

/-- The Hessian formula is linear in its first direction as a map into
continuous linear maps in the second direction. -/
private def transportSecondDerivativeLinearMap
    (jet : FramedSecondOrderJet X V) : X →ₗ[Real] X →L[Real] V where
  toFun first :=
    LinearMap.toContinuousLinearMap
      (change.transportSecondDerivativeInnerLinearMap jet first)
  map_add' first second := by
    ext direction
    change
      change.transportSecondDerivativeInnerLinearMap jet
          (first + second) direction =
        change.transportSecondDerivativeInnerLinearMap jet first direction +
          change.transportSecondDerivativeInnerLinearMap jet second direction
    rw [change.transportSecondDerivativeInnerLinearMap_symmetric jet
      (first + second) direction]
    rw [map_add]
    rw [change.transportSecondDerivativeInnerLinearMap_symmetric jet
      direction first]
    rw [change.transportSecondDerivativeInnerLinearMap_symmetric jet
      direction second]
  map_smul' scalar first := by
    ext direction
    change
      change.transportSecondDerivativeInnerLinearMap jet
          (scalar • first) direction =
        scalar •
          change.transportSecondDerivativeInnerLinearMap jet first direction
    rw [change.transportSecondDerivativeInnerLinearMap_symmetric jet
      (scalar • first) direction]
    rw [map_smul]
    rw [change.transportSecondDerivativeInnerLinearMap_symmetric jet
      direction first]

/-- Continuous symmetric Hessian of the transported jet. -/
def transportSecondDerivative
    (jet : FramedSecondOrderJet X V) : X →L[Real] X →L[Real] V :=
  LinearMap.toContinuousLinearMap
    (change.transportSecondDerivativeLinearMap jet)

@[simp]
theorem transportSecondDerivative_apply
    (jet : FramedSecondOrderJet X V) (first second : X) :
    change.transportSecondDerivative jet first second =
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

/-- Generic five-term semidirect action on a framed second jet. -/
def transport
    (jet : FramedSecondOrderJet X V) : FramedSecondOrderJet X V where
  value := change.fiberValue jet.value
  firstDerivative := change.transportFirstDerivative jet
  secondDerivative := change.transportSecondDerivative jet
  secondDerivative_symmetric first second := by
    exact
      change.transportSecondDerivativeInnerLinearMap_symmetric jet first second

@[simp]
theorem transport_value (jet : FramedSecondOrderJet X V) :
    (change.transport jet).value = change.fiberValue jet.value :=
  rfl

@[simp]
theorem transport_firstDerivative (jet : FramedSecondOrderJet X V) :
    (change.transport jet).firstDerivative =
      change.transportFirstDerivative jet :=
  rfl

@[simp]
theorem transport_firstDerivative_apply
    (jet : FramedSecondOrderJet X V) (direction : X) :
    (change.transport jet).firstDerivative direction =
      change.fiberValue
          (jet.firstDerivative (change.baseFirst direction)) +
        change.fiberFirst direction jet.value :=
  rfl

@[simp]
theorem transport_secondDerivative (jet : FramedSecondOrderJet X V) :
    (change.transport jet).secondDerivative =
      change.transportSecondDerivative jet :=
  rfl

@[simp]
theorem transport_secondDerivative_apply
    (jet : FramedSecondOrderJet X V) (first second : X) :
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

/-- The semidirect transport is linear in the source jet. -/
def toLinearMap :
    FramedSecondOrderJet X V →ₗ[Real] FramedSecondOrderJet X V where
  toFun := change.transport
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components
    · simp
    · ext direction
      simp only [transport_firstDerivative_apply,
        FramedSecondOrderJet.add_value,
        FramedSecondOrderJet.add_firstDerivative, add_apply, map_add]
      abel
    · ext firstDirection secondDirection
      simp only [transport_secondDerivative_apply,
        FramedSecondOrderJet.add_value,
        FramedSecondOrderJet.add_firstDerivative,
        FramedSecondOrderJet.add_secondDerivative, add_apply, map_add]
      abel
  map_smul' scalar jet := by
    apply FramedSecondOrderJet.ext_components
    · simp
    · ext direction
      simp only [transport_firstDerivative_apply,
        FramedSecondOrderJet.smul_value,
        FramedSecondOrderJet.smul_firstDerivative,
        smul_apply, map_smul, RingHom.id_apply]
      module
    · ext firstDirection secondDirection
      simp only [transport_secondDerivative_apply,
        FramedSecondOrderJet.smul_value,
        FramedSecondOrderJet.smul_firstDerivative,
        FramedSecondOrderJet.smul_secondDerivative,
        smul_apply, map_smul, RingHom.id_apply]
      module

@[simp]
theorem toLinearMap_apply (jet : FramedSecondOrderJet X V) :
    change.toLinearMap jet = change.transport jet :=
  rfl

/-- In finite dimensions, the full linear jet action is automatically
continuous. -/
def toContinuousLinearMap
    [FiniteDimensional Real V] :
    FramedSecondOrderJet X V →L[Real] FramedSecondOrderJet X V :=
  LinearMap.toContinuousLinearMap change.toLinearMap

@[simp]
theorem toContinuousLinearMap_apply
    [FiniteDimensional Real V]
    (jet : FramedSecondOrderJet X V) :
    change.toContinuousLinearMap jet = change.transport jet :=
  rfl

end FramedSecondOrderJetSemidirectChange

end
end P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
end JanusFormal
