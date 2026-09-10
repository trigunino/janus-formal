import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetNormedSpace4D

/-!
# Spatial multi-index second jets on the throat

This gate supplies the three-dimensional, order-two coordinate jet used by
the local T06 calculation.  Zeroth, first and second coefficients are indexed
respectively by a point, a direction in `Fin 3`, and an unordered pair of
directions.  The unordered pair is the multi-index symmetry of mixed partials.

The resulting carrier is linearly equivalent to the genuine
`FramedSecondOrderJet ThroatCoverCoordinates Fiber` used in the T02 physical
second-jet product.  It is a jet of the underlying field-value fiber `Fiber`;
the construction never takes a jet of the already assembled T02 jet fiber.

This is only a carrier and coordinate bridge.  It does not yet construct the
degree-four polynomial horizontal complex, its Euler operator, or a T06
classification theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D

set_option autoImplicit false
noncomputable section

open Module
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

/-- Multi-indices of total order at most one in the three throat directions. -/
inductive ThroatSpatialMultiIndexUpToOne where
  | orderZero
  | orderOne (direction : Fin 3)

/-- Multi-indices of total order at most two in the three throat directions.
The order-two index is an unordered pair, so mixed partial symmetry is built
into the carrier. -/
inductive ThroatSpatialMultiIndexUpToTwo where
  | orderZero
  | orderOne (direction : Fin 3)
  | orderTwo (directions : Sym2 (Fin 3))

/-- Spatial throat jets through first order. -/
abbrev ThroatSpatialMultiindexFirstJet (Fiber : Type*) :=
  ThroatSpatialMultiIndexUpToOne → Fiber

/-- Spatial throat jets through second order. -/
abbrev ThroatSpatialMultiindexSecondJet (Fiber : Type*) :=
  ThroatSpatialMultiIndexUpToTwo → Fiber

/-- A chosen three-dimensional basis used to compare symmetric multi-index
coefficients with continuous derivative maps. -/
def programPT06ThroatSpatialBasis :
    Basis (Fin 3) Real ThroatCoverCoordinates := by
  let basis := Module.finBasis Real ThroatCoverCoordinates
  have hDimension : Module.finrank Real ThroatCoverCoordinates = 3 := by
    simp [ThroatCoverCoordinates]
  simpa [hDimension] using basis

/-- Restriction from order two to order one. -/
def programPT06TruncateThroatSpatialSecondJet
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber] :
    ThroatSpatialMultiindexSecondJet Fiber →ₗ[Real]
      ThroatSpatialMultiindexFirstJet Fiber where
  toFun jet index :=
    match index with
    | .orderZero => jet .orderZero
    | .orderOne direction => jet (.orderOne direction)
  map_add' first second := by
    funext index
    cases index <;> rfl
  map_smul' scalar jet := by
    funext index
    cases index <;> rfl

/-- Formal total derivative from second to first order in one throat
direction. -/
def programPT06ThroatSpatialTotalDerivative
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber]
    (direction : Fin 3) :
    ThroatSpatialMultiindexSecondJet Fiber →ₗ[Real]
      ThroatSpatialMultiindexFirstJet Fiber where
  toFun jet index :=
    match index with
    | .orderZero => jet (.orderOne direction)
    | .orderOne secondDirection =>
        jet (.orderTwo s(direction, secondDirection))
  map_add' first second := by
    funext index
    cases index <;> rfl
  map_smul' scalar jet := by
    funext index
    cases index <;> rfl

/-- Directional derivative of an order-one jet at order zero. -/
def programPT06ThroatSpatialFirstToZeroDerivative
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber]
    (direction : Fin 3) :
    ThroatSpatialMultiindexFirstJet Fiber →ₗ[Real] Fiber where
  toFun jet := jet (.orderOne direction)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem programPT06ThroatSpatialTotalDerivative_orderZero
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber]
    (direction : Fin 3) (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialTotalDerivative direction jet .orderZero =
      jet (.orderOne direction) :=
  rfl

@[simp] theorem programPT06ThroatSpatialTotalDerivative_orderOne
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber]
    (first second : Fin 3)
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialTotalDerivative first jet (.orderOne second) =
      jet (.orderTwo s(first, second)) :=
  rfl

/-- The two successive coefficient extractions agree on mixed second
coefficients because their order-two index is an unordered pair. -/
theorem programPT06ThroatSpatialTotalDerivative_comm
    {Fiber : Type*} [AddCommMonoid Fiber] [Module Real Fiber]
    (first second : Fin 3)
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialFirstToZeroDerivative first
        (programPT06ThroatSpatialTotalDerivative second jet) =
      programPT06ThroatSpatialFirstToZeroDerivative second
        (programPT06ThroatSpatialTotalDerivative first jet) := by
  change jet (.orderTwo s(second, first)) =
    jet (.orderTwo s(first, second))
  rw [Sym2.eq_swap]

variable {Fiber : Type*}
variable [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private theorem throatContinuousLinearMap_ext
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {first second : ThroatCoverCoordinates →L[Real] Target}
    (hBasis : ∀ direction : Fin 3,
      first (programPT06ThroatSpatialBasis direction) =
        second (programPT06ThroatSpatialBasis direction)) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [← programPT06ThroatSpatialBasis.sum_repr vector]
  simp only [map_sum, map_smul, hBasis]

/-- First derivative reconstructed from its three basis coefficients. -/
def programPT06ThroatFirstDerivativeFromSpatialCoordinates
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    ThroatCoverCoordinates →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun direction =>
      jet (.orderOne direction))

@[simp] theorem programPT06ThroatFirstDerivativeFromSpatialCoordinates_basis
    (jet : ThroatSpatialMultiindexSecondJet Fiber) (direction : Fin 3) :
    programPT06ThroatFirstDerivativeFromSpatialCoordinates jet
        (programPT06ThroatSpatialBasis direction) =
      jet (.orderOne direction) := by
  simp [programPT06ThroatFirstDerivativeFromSpatialCoordinates]

/-- Symmetric second derivative reconstructed from its unordered-pair
coefficients. -/
def programPT06ThroatSecondDerivativeFromSpatialCoordinates
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun first =>
      LinearMap.toContinuousLinearMap
        (programPT06ThroatSpatialBasis.constr Real fun second =>
          jet (.orderTwo s(first, second))))

@[simp] theorem programPT06ThroatSecondDerivativeFromSpatialCoordinates_basis
    (jet : ThroatSpatialMultiindexSecondJet Fiber) (first second : Fin 3) :
    programPT06ThroatSecondDerivativeFromSpatialCoordinates jet
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second) =
      jet (.orderTwo s(first, second)) := by
  simp [programPT06ThroatSecondDerivativeFromSpatialCoordinates]

theorem programPT06ThroatSecondDerivativeFromSpatialCoordinates_symmetric
    (jet : ThroatSpatialMultiindexSecondJet Fiber)
    (first second : ThroatCoverCoordinates) :
    programPT06ThroatSecondDerivativeFromSpatialCoordinates jet first second =
      programPT06ThroatSecondDerivativeFromSpatialCoordinates jet second first := by
  let derivative :=
    programPT06ThroatSecondDerivativeFromSpatialCoordinates jet
  have hFlip : derivative = derivative.flip := by
    apply throatContinuousLinearMap_ext
    intro firstDirection
    apply throatContinuousLinearMap_ext
    intro secondDirection
    simp [derivative, Sym2.eq_swap]
  have hAtVectors := congrArg (fun map => map first second) hFlip
  simpa [derivative] using hAtVectors

/-- Reconstruct the genuine framed second jet from spatial multi-index
coefficients. -/
def programPT06ThroatSpatialSecondJetToFramed
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber where
  value := jet .orderZero
  firstDerivative := programPT06ThroatFirstDerivativeFromSpatialCoordinates jet
  secondDerivative := programPT06ThroatSecondDerivativeFromSpatialCoordinates jet
  secondDerivative_symmetric :=
    programPT06ThroatSecondDerivativeFromSpatialCoordinates_symmetric jet

@[simp] theorem programPT06ThroatSpatialSecondJetToFramed_value
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    (programPT06ThroatSpatialSecondJetToFramed jet).value =
      jet .orderZero :=
  rfl

@[simp] theorem programPT06ThroatSpatialSecondJetToFramed_firstDerivative
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    (programPT06ThroatSpatialSecondJetToFramed jet).firstDerivative =
      programPT06ThroatFirstDerivativeFromSpatialCoordinates jet :=
  rfl

@[simp] theorem programPT06ThroatSpatialSecondJetToFramed_secondDerivative
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    (programPT06ThroatSpatialSecondJetToFramed jet).secondDerivative =
      programPT06ThroatSecondDerivativeFromSpatialCoordinates jet :=
  rfl

/-- Extract spatial multi-index coefficients from a genuine framed second
jet. -/
def programPT06FramedSecondJetToThroatSpatial
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber) :
    ThroatSpatialMultiindexSecondJet Fiber
  | .orderZero => jet.value
  | .orderOne direction =>
      jet.firstDerivative (programPT06ThroatSpatialBasis direction)
  | .orderTwo directions =>
      Sym2.lift
        ⟨fun first second =>
            jet.secondDerivative
              (programPT06ThroatSpatialBasis first)
              (programPT06ThroatSpatialBasis second),
          fun first second => jet.secondDerivative_symmetric _ _⟩
        directions

@[simp] theorem programPT06FramedSecondJetToThroatSpatial_orderZero
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber) :
    programPT06FramedSecondJetToThroatSpatial jet .orderZero = jet.value :=
  rfl

@[simp] theorem programPT06FramedSecondJetToThroatSpatial_orderOne
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber)
    (direction : Fin 3) :
    programPT06FramedSecondJetToThroatSpatial jet (.orderOne direction) =
      jet.firstDerivative (programPT06ThroatSpatialBasis direction) :=
  rfl

@[simp] theorem programPT06FramedSecondJetToThroatSpatial_orderTwo
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber)
    (first second : Fin 3) :
    programPT06FramedSecondJetToThroatSpatial jet
        (.orderTwo s(first, second)) =
      jet.secondDerivative
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second) :=
  rfl

theorem programPT06FramedSecondJetToThroatSpatial_toFramed
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06FramedSecondJetToThroatSpatial
        (programPT06ThroatSpatialSecondJetToFramed jet) = jet := by
  funext index
  cases index with
  | orderZero => rfl
  | orderOne direction =>
      exact programPT06ThroatFirstDerivativeFromSpatialCoordinates_basis
        jet direction
  | orderTwo directions =>
      refine Sym2.inductionOn directions ?_
      intro first second
      exact programPT06ThroatSecondDerivativeFromSpatialCoordinates_basis
        jet first second

theorem programPT06ThroatSpatialSecondJetToFramed_toSpatial
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber) :
    programPT06ThroatSpatialSecondJetToFramed
        (programPT06FramedSecondJetToThroatSpatial jet) = jet := by
  apply FramedSecondOrderJet.ext_components
  · rfl
  · apply throatContinuousLinearMap_ext
    intro direction
    simp
  · apply throatContinuousLinearMap_ext
    intro first
    apply throatContinuousLinearMap_ext
    intro second
    simp

private theorem programPT06ThroatSpatialSecondJetToFramed_add
    (first second : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialSecondJetToFramed (first + second) =
      programPT06ThroatSpatialSecondJetToFramed first +
        programPT06ThroatSpatialSecondJetToFramed second := by
  apply FramedSecondOrderJet.ext_components
  · rfl
  · apply throatContinuousLinearMap_ext
    intro direction
    simp
  · apply throatContinuousLinearMap_ext
    intro firstDirection
    apply throatContinuousLinearMap_ext
    intro secondDirection
    simp

private theorem programPT06ThroatSpatialSecondJetToFramed_smul
    (scalar : Real) (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialSecondJetToFramed (scalar • jet) =
      scalar • programPT06ThroatSpatialSecondJetToFramed jet := by
  apply FramedSecondOrderJet.ext_components
  · rfl
  · apply throatContinuousLinearMap_ext
    intro direction
    simp
  · apply throatContinuousLinearMap_ext
    intro firstDirection
    apply throatContinuousLinearMap_ext
    intro secondDirection
    simp

/-- Exact linear equivalence between spatial multi-index coefficients through
order two and the genuine framed second jet used componentwise by T02. -/
def programPT06ThroatSpatialSecondJetFramedLinearEquiv :
    ThroatSpatialMultiindexSecondJet Fiber ≃ₗ[Real]
      FramedSecondOrderJet ThroatCoverCoordinates Fiber where
  toFun := programPT06ThroatSpatialSecondJetToFramed
  invFun := programPT06FramedSecondJetToThroatSpatial
  left_inv := programPT06FramedSecondJetToThroatSpatial_toFramed
  right_inv := programPT06ThroatSpatialSecondJetToFramed_toSpatial
  map_add' := programPT06ThroatSpatialSecondJetToFramed_add
  map_smul' := programPT06ThroatSpatialSecondJetToFramed_smul

@[simp] theorem programPT06ThroatSpatialSecondJetFramedLinearEquiv_apply
    (jet : ThroatSpatialMultiindexSecondJet Fiber) :
    programPT06ThroatSpatialSecondJetFramedLinearEquiv jet =
      programPT06ThroatSpatialSecondJetToFramed jet :=
  rfl

@[simp] theorem programPT06ThroatSpatialSecondJetFramedLinearEquiv_symm_apply
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber) :
    programPT06ThroatSpatialSecondJetFramedLinearEquiv.symm jet =
      programPT06FramedSecondJetToThroatSpatial jet :=
  rfl

end
end P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
end JanusFormal
