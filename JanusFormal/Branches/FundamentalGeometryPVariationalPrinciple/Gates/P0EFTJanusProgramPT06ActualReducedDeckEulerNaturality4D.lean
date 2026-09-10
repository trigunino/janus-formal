import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Reduced deck naturality of the second-order Euler operator

The physical deck involution of Gate885 acts on the exact reduced `(II, F)`
carrier by `(II, F) \mapsto (-II, F)`.  This gate first records that carrier as
an exact real linear subspace and prolongs the involution coefficientwise as a
linear equivalence on every spatial jet order.

For the Frechet Euler operator, the arbitrary-function carrier of Gate885 has
no canonical norm.  We therefore pass to its honest finite fixed-frame
coefficient projection.  On this normed `(II, F)` coefficient fiber the deck
action is a continuous linear involution.  Every deck-invariant bounded linear
`J²` density then has an equivariant Gate880 Euler covector on `J⁴`.

The result is deliberately restricted to the reduced `(II, F)` sector and to
bounded linear local densities.  It does not assert a deck action on the full
eleven-component physical carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualReducedDeckEulerNaturality4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualReducedDeckJetProlongation4D

/-! ## Exact algebraic reduced carrier -/

/-- Raw functional coefficients of the exact reduced `(II, F)` carrier. -/
abbrev ActualOrientedGaussReducedRawPair :=
  (EuclideanR3 → EuclideanR3 → Real) ×
    (EuclideanR3 → EuclideanR3 → Real)

/-- The exact algebraic `(II, F)` model.  The second component retains the
alternating identity carried by `LowOrderReducedData`. -/
def actualOrientedGaussReducedAlgebraicSubmodule :
    Submodule Real ActualOrientedGaussReducedRawPair where
  carrier := fun data ↦
    ∀ first second, data.2 second first = -data.2 first second
  zero_mem' := by
    intro first second
    simp
  add_mem' := by
    intro firstData secondData hFirst hSecond first second
    simp only [Prod.snd_add, Pi.add_apply]
    rw [hFirst first second, hSecond first second]
    ring
  smul_mem' := by
    intro scalar data hData first second
    change scalar * data.2 second first =
      -(scalar * data.2 first second)
    rw [hData first second]
    ring

/-- Exact real linear model of the Gate885 reduced carrier. -/
abbrev ActualOrientedGaussReducedAlgebraicFiber :=
  actualOrientedGaussReducedAlgebraicSubmodule

/-- No information is lost in replacing `LowOrderReducedData` by its exact
algebraic `(II, F)` subspace. -/
def programPT06ActualOrientedGaussReducedAlgebraicEquiv :
    ActualOrientedGaussReducedFiber ≃
      ActualOrientedGaussReducedAlgebraicFiber where
  toFun data :=
    ⟨(data.secondFundamental, data.gaugeCurvature),
      data.gaugeCurvature_alternating⟩
  invFun data :=
    { secondFundamental := data.1.1
      gaugeCurvature := data.1.2
      gaugeCurvature_alternating := data.2 }
  left_inv data := by
    apply LowOrderReducedData.ext <;> rfl
  right_inv data := by
    apply Subtype.ext
    rfl

/-- On the exact algebraic carrier, the physical deck action is the linear
involution `(II, F) \mapsto (-II, F)`. -/
def programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv :
    ActualOrientedGaussReducedAlgebraicFiber ≃ₗ[Real]
      ActualOrientedGaussReducedAlgebraicFiber where
  toFun data := ⟨(-data.1.1, data.1.2), data.2⟩
  invFun data := ⟨(-data.1.1, data.1.2), data.2⟩
  left_inv data := by
    apply Subtype.ext
    ext <;> simp
  right_inv data := by
    apply Subtype.ext
    ext <;> simp
  map_add' first second := by
    apply Subtype.ext
    ext <;> simp [add_comm]
  map_smul' scalar data := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv_apply
    (data : ActualOrientedGaussReducedAlgebraicFiber) :
    programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv data =
      ⟨(-data.1.1, data.1.2), data.2⟩ :=
  rfl

/-- Exact coefficientwise linear deck involution on every algebraic spatial
jet order, including `J²` and `J⁴`. -/
def programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv
    (order : Nat) :
    TruncatedThroatSpatialMultiindexJet
        ActualOrientedGaussReducedAlgebraicFiber order ≃ₗ[Real]
      TruncatedThroatSpatialMultiindexJet
        ActualOrientedGaussReducedAlgebraicFiber order :=
  LinearEquiv.piCongrRight fun _ ↦
    programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv

@[simp] theorem
    programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv_apply
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedAlgebraicFiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv
        order jet index =
      programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv
        (jet index) :=
  rfl

@[simp] theorem
    programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv_involutive
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedAlgebraicFiber order) :
    programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv order
        (programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv
          order jet) = jet := by
  funext index
  apply Subtype.ext
  apply Prod.ext
  · funext first second
    simp
  · rfl

@[simp] theorem programPT06ActualOrientedGaussReducedDeckAction_secondFundamental
    (data : ActualOrientedGaussReducedFiber) (first second : EuclideanR3) :
    (programPT06ActualOrientedGaussReducedDeckAction data).secondFundamental
        first second =
      -data.secondFundamental first second := by
  change
    (LinearIsometryEquiv.neg Real)
        (data.secondFundamental first second) =
      -data.secondFundamental first second
  rfl

@[simp] theorem programPT06ActualOrientedGaussReducedDeckAction_gaugeCurvature
    (data : ActualOrientedGaussReducedFiber) (first second : EuclideanR3) :
    (programPT06ActualOrientedGaussReducedDeckAction data).gaugeCurvature
        first second =
      data.gaugeCurvature first second := by
  change data.gaugeCurvature first second = data.gaugeCurvature first second
  rfl

/-- The exact algebraic equivalence intertwines the physical Gate885 deck
action with the linear involution. -/
theorem programPT06ActualOrientedGaussReducedAlgebraicEquiv_deck
    (data : ActualOrientedGaussReducedFiber) :
    programPT06ActualOrientedGaussReducedAlgebraicEquiv
        (programPT06ActualOrientedGaussReducedDeckAction data) =
      programPT06ActualOrientedGaussReducedAlgebraicDeckLinearEquiv
        (programPT06ActualOrientedGaussReducedAlgebraicEquiv data) := by
  apply Subtype.ext
  apply Prod.ext
  · funext first second
    exact
      programPT06ActualOrientedGaussReducedDeckAction_secondFundamental
        data first second
  · funext first second
    exact
      programPT06ActualOrientedGaussReducedDeckAction_gaugeCurvature
        data first second

/-- Pointwise passage from an actual Gate885 jet to its exact algebraic
model. -/
def programPT06ActualOrientedGaussReducedAlgebraicJet
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedAlgebraicFiber order :=
  fun index ↦ programPT06ActualOrientedGaussReducedAlgebraicEquiv (jet index)

/-- The actual Gate885 coefficientwise action is exactly conjugate to the
linear jet involution. -/
theorem programPT06ActualOrientedGaussReducedAlgebraicJet_deck
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order) :
    programPT06ActualOrientedGaussReducedAlgebraicJet order
        (programPT06ActualOrientedGaussReducedJetDeckAction order jet) =
      programPT06ActualOrientedGaussReducedAlgebraicJetDeckLinearEquiv order
        (programPT06ActualOrientedGaussReducedAlgebraicJet order jet) := by
  funext index
  exact programPT06ActualOrientedGaussReducedAlgebraicEquiv_deck (jet index)

/-! ## Finite fixed-frame coefficient carrier -/

/-- One fixed-frame coefficient table for a reduced two-tensor. -/
abbrev ActualOrientedGaussReducedCoefficientTensor :=
  Fin 3 → Fin 3 → Real

/-- Pairs of fixed-frame `(II, F)` coefficient tables. -/
abbrev ActualOrientedGaussReducedCoefficientPair :=
  ActualOrientedGaussReducedCoefficientTensor ×
    ActualOrientedGaussReducedCoefficientTensor

/-- The finite fixed-frame reduced carrier, retaining the alternating identity
of the curvature coefficients. -/
def actualOrientedGaussReducedCoefficientSubmodule :
    Submodule Real ActualOrientedGaussReducedCoefficientPair where
  carrier := fun data ↦
    ∀ first second, data.2 second first = -data.2 first second
  zero_mem' := by
    intro first second
    simp
  add_mem' := by
    intro firstData secondData hFirst hSecond first second
    simp only [Prod.snd_add, Pi.add_apply]
    rw [hFirst first second, hSecond first second]
    ring
  smul_mem' := by
    intro scalar data hData first second
    change scalar * data.2 second first =
      -(scalar * data.2 first second)
    rw [hData first second]
    ring

/-- Finite normed fixed-frame `(II, F)` coefficient fiber. -/
abbrev ActualOrientedGaussReducedCoefficientFiber :=
  actualOrientedGaussReducedCoefficientSubmodule

/-- Fixed-frame coefficient projection of the exact reduced data. -/
def programPT06ActualOrientedGaussReducedCoordinates
    (data : ActualOrientedGaussReducedFiber) :
    ActualOrientedGaussReducedCoefficientFiber :=
  ⟨(fun first second ↦
      data.secondFundamental
        (EuclideanSpace.basisFun (Fin 3) Real first)
        (EuclideanSpace.basisFun (Fin 3) Real second),
    fun first second ↦
      data.gaugeCurvature
        (EuclideanSpace.basisFun (Fin 3) Real first)
        (EuclideanSpace.basisFun (Fin 3) Real second)),
    fun first second ↦
      data.gaugeCurvature_alternating
        (EuclideanSpace.basisFun (Fin 3) Real first)
        (EuclideanSpace.basisFun (Fin 3) Real second)⟩

/-- Linear deck involution on the finite reduced coefficient fiber. -/
def programPT06ActualOrientedGaussReducedCoefficientDeckLinearEquiv :
    ActualOrientedGaussReducedCoefficientFiber ≃ₗ[Real]
      ActualOrientedGaussReducedCoefficientFiber where
  toFun data := ⟨(-data.1.1, data.1.2), data.2⟩
  invFun data := ⟨(-data.1.1, data.1.2), data.2⟩
  left_inv data := by
    apply Subtype.ext
    ext <;> simp
  right_inv data := by
    apply Subtype.ext
    ext <;> simp
  map_add' first second := by
    apply Subtype.ext
    ext <;> simp [add_comm]
  map_smul' scalar data := by
    apply Subtype.ext
    ext <;> simp

/-- Continuous realization of the finite-dimensional deck involution. -/
def programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv :
    ActualOrientedGaussReducedCoefficientFiber ≃L[Real]
      ActualOrientedGaussReducedCoefficientFiber :=
  programPT06ActualOrientedGaussReducedCoefficientDeckLinearEquiv
    |>.toContinuousLinearEquiv

@[simp] theorem
    programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv_apply
    (data : ActualOrientedGaussReducedCoefficientFiber) :
    programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
        data =
      ⟨(-data.1.1, data.1.2), data.2⟩ :=
  rfl

@[simp] theorem
    programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv_involutive
    (data : ActualOrientedGaussReducedCoefficientFiber) :
    programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          data) = data := by
  apply Subtype.ext
  ext <;> simp

/-- The finite coordinate projection still intertwines the physical Gate885
deck action exactly. -/
theorem programPT06ActualOrientedGaussReducedCoordinates_deck
    (data : ActualOrientedGaussReducedFiber) :
    programPT06ActualOrientedGaussReducedCoordinates
        (programPT06ActualOrientedGaussReducedDeckAction data) =
      programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
        (programPT06ActualOrientedGaussReducedCoordinates data) := by
  apply Subtype.ext
  apply Prod.ext
  · funext first second
    exact
      programPT06ActualOrientedGaussReducedDeckAction_secondFundamental data
        (EuclideanSpace.basisFun (Fin 3) Real first)
        (EuclideanSpace.basisFun (Fin 3) Real second)
  · funext first second
    exact
      programPT06ActualOrientedGaussReducedDeckAction_gaugeCurvature data
        (EuclideanSpace.basisFun (Fin 3) Real first)
        (EuclideanSpace.basisFun (Fin 3) Real second)

/-- Continuous coefficientwise deck involution on every finite reduced jet
order. -/
def programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
    (order : Nat) :
    TruncatedThroatSpatialMultiindexJet
        ActualOrientedGaussReducedCoefficientFiber order ≃L[Real]
      TruncatedThroatSpatialMultiindexJet
        ActualOrientedGaussReducedCoefficientFiber order :=
  ContinuousLinearEquiv.piCongrRight fun _ ↦
    programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv

@[simp] theorem
    programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv_apply
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedCoefficientFiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        order jet index =
      programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
        (jet index) :=
  rfl

@[simp] theorem
    programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv_involutive
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedCoefficientFiber order) :
    programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        order
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          order jet) = jet := by
  funext index
  apply Subtype.ext
  apply Prod.ext
  · funext first second
    simp
  · rfl

/-- The continuous jet involution commutes with truncation. -/
theorem
    programPT06ActualOrientedGaussReducedCoefficientJetDeck_commutes_truncation
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedCoefficientFiber higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          higher jet) =
      programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        lower (truncateThroatSpatialMultiindexJet hOrder jet) := by
  rfl

/-- The continuous jet involution commutes with formal total derivatives. -/
theorem
    programPT06ActualOrientedGaussReducedCoefficientJetDeck_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedCoefficientFiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          (order + 1) jet) =
      programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        order (throatSpatialTotalDerivative direction jet) := by
  rfl

/-- Applying the deck action to a one-slot jet variation is the same as
applying it to the inserted reduced coefficient. -/
@[simp] theorem
    programPT06ActualOrientedGaussReducedCoefficientJetDeck_coordinateInjection
    {order : Nat} (index : ThroatSpatialTruncatedIndex order)
    (variation : ActualOrientedGaussReducedCoefficientFiber) :
    programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        order
        (programPT06ThroatSpatialJetCoordinateInjection index variation) =
      programPT06ThroatSpatialJetCoordinateInjection index
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          variation) := by
  classical
  funext coordinate
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    rw [programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv_apply,
      programPT06ThroatSpatialJetCoordinateInjection_same,
      programPT06ThroatSpatialJetCoordinateInjection_same]
  · rw [programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv_apply,
      programPT06ThroatSpatialJetCoordinateInjection_of_ne index coordinate
        hCoordinate variation,
      map_zero,
      programPT06ThroatSpatialJetCoordinateInjection_of_ne index coordinate
        hCoordinate]

/-- Coefficientwise projection of an actual Gate885 jet. -/
def programPT06ActualOrientedGaussReducedCoordinateJet
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ActualOrientedGaussReducedCoefficientFiber order :=
  fun index ↦ programPT06ActualOrientedGaussReducedCoordinates (jet index)

/-- The actual Gate885 `J²` action projects to the continuous linear reduced
coefficient action. -/
theorem programPT06ActualOrientedGaussReducedCoordinateJet2_deck
    (jet : ThroatSpatialMultiindexJet2 ActualOrientedGaussReducedFiber) :
    programPT06ActualOrientedGaussReducedCoordinateJet 2
        (programPT06ActualOrientedGaussReducedJetDeckAction 2 jet) =
      programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        2 (programPT06ActualOrientedGaussReducedCoordinateJet 2 jet) := by
  funext index
  exact programPT06ActualOrientedGaussReducedCoordinates_deck (jet index)

/-- The actual Gate885 `J⁴` action projects to the continuous linear reduced
coefficient action. -/
theorem programPT06ActualOrientedGaussReducedCoordinateJet4_deck
    (jet : ThroatSpatialMultiindexJet4 ActualOrientedGaussReducedFiber) :
    programPT06ActualOrientedGaussReducedCoordinateJet 4
        (programPT06ActualOrientedGaussReducedJetDeckAction 4 jet) =
      programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
        4 (programPT06ActualOrientedGaussReducedCoordinateJet 4 jet) := by
  funext index
  exact programPT06ActualOrientedGaussReducedCoordinates_deck (jet index)

/-! ## Euler equivariance for invariant bounded linear densities -/

/-- A bounded linear reduced `J²` density is deck invariant when it is fixed
by pullback along the continuous coefficientwise deck involution. -/
def IsProgramPT06ActualOrientedGaussReducedDeckInvariantLinearDensity
    (density :
      ThroatSpatialMultiindexJet2
          ActualOrientedGaussReducedCoefficientFiber →L[Real] Real) : Prop :=
  ∀ jet,
    density
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          2 jet) =
      density jet

/-- Pointwise deck equivariance of the genuine Gate880 second-order Euler
operator for invariant bounded linear reduced densities. -/
theorem programPT06ActualOrientedGaussReducedDeckEuler_equivariant
    (density :
      ThroatSpatialMultiindexJet2
          ActualOrientedGaussReducedCoefficientFiber →L[Real] Real)
    (hInvariant :
      IsProgramPT06ActualOrientedGaussReducedDeckInvariantLinearDensity density)
    (jet : ThroatSpatialMultiindexJet4
      ActualOrientedGaussReducedCoefficientFiber)
    (variation : ActualOrientedGaussReducedCoefficientFiber) :
    programPT06SecondOrderLocalEuler density
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          4 jet)
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          variation) =
      programPT06SecondOrderLocalEuler density jet variation := by
  simpa only [programPT06SecondOrderLocalEuler_linear,
      ContinuousLinearMap.comp_apply,
      programPT06ActualOrientedGaussReducedCoefficientJetDeck_coordinateInjection]
    using hInvariant
      (programPT06ThroatSpatialJetCoordinateInjection
        (Fiber := ActualOrientedGaussReducedCoefficientFiber)
        programPT06SecondOrderZeroMultiIndex variation)

/-- Covector form of deck naturality:
`E(L)(deck · j) = deck⁺ E(L)(j)`. -/
theorem programPT06ActualOrientedGaussReducedDeckEuler_covector_natural
    (density :
      ThroatSpatialMultiindexJet2
          ActualOrientedGaussReducedCoefficientFiber →L[Real] Real)
    (hInvariant :
      IsProgramPT06ActualOrientedGaussReducedDeckInvariantLinearDensity density)
    (jet : ThroatSpatialMultiindexJet4
      ActualOrientedGaussReducedCoefficientFiber) :
    programPT06SecondOrderLocalEuler density
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          4 jet) =
      (programPT06SecondOrderLocalEuler density jet).comp
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    programPT06SecondOrderLocalEuler density
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          4 jet) variation =
      programPT06SecondOrderLocalEuler density jet
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          variation)
  simpa using
    programPT06ActualOrientedGaussReducedDeckEuler_equivariant density hInvariant
      jet
      (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
        variation)

/-- The Euler-zero locus of an invariant bounded linear reduced density is
preserved and reflected by the physical reduced deck involution. -/
theorem programPT06ActualOrientedGaussReducedDeckEuler_zero_iff
    (density :
      ThroatSpatialMultiindexJet2
          ActualOrientedGaussReducedCoefficientFiber →L[Real] Real)
    (hInvariant :
      IsProgramPT06ActualOrientedGaussReducedDeckInvariantLinearDensity density)
    (jet : ThroatSpatialMultiindexJet4
      ActualOrientedGaussReducedCoefficientFiber) :
    programPT06SecondOrderLocalEuler density
        (programPT06ActualOrientedGaussReducedCoefficientJetDeckContinuousLinearEquiv
          4 jet) = 0 ↔
      programPT06SecondOrderLocalEuler density jet = 0 := by
  constructor
  · intro hDeck
    apply ContinuousLinearMap.ext
    intro variation
    have hEquivariant :=
      programPT06ActualOrientedGaussReducedDeckEuler_equivariant density
        hInvariant jet variation
    rw [hDeck] at hEquivariant
    simpa using hEquivariant.symm
  · intro hEuler
    apply ContinuousLinearMap.ext
    intro variation
    have hEquivariant :=
      programPT06ActualOrientedGaussReducedDeckEuler_equivariant density
        hInvariant jet
        (programPT06ActualOrientedGaussReducedCoefficientDeckContinuousLinearEquiv
          variation)
    rw [hEuler] at hEquivariant
    simpa using hEquivariant

end
end P0EFTJanusProgramPT06ActualReducedDeckEulerNaturality4D
end JanusFormal
