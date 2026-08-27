import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

/-!
# Normed vector-space structure on framed second-order jets

The symmetry condition on the second derivative is linear.  Hence a framed
second-order jet is identified with a submodule of the product of its value,
first derivative and second derivative.  This transports the real module and
normed-space structures without changing the original carrier.

When the domain and fiber are finite-dimensional, the carrier is also
finite-dimensional and therefore complete.  No generic dimension or rank is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

set_option autoImplicit false
noncomputable section

variable
    (Domain Fiber : Type*)
    [NormedAddCommGroup Domain] [NormedSpace Real Domain]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Ambient product containing the three components of a framed second jet. -/
abbrev FramedSecondOrderJetAmbient :=
  Fiber × (Domain →L[Real] Fiber) ×
    (Domain →L[Real] Domain →L[Real] Fiber)

/-- The linear subspace cut out by symmetry of the second derivative. -/
def framedSecondOrderJetSymmetricSubmodule :
    Submodule Real (FramedSecondOrderJetAmbient Domain Fiber) where
  carrier := {components |
    ∀ first second,
      components.2.2 first second = components.2.2 second first}
  zero_mem' := by
    intro first second
    simp
  add_mem' := by
    intro firstJet secondJet hFirst hSecond first second
    simp only [Prod.snd_add, add_apply]
    rw [hFirst first second, hSecond first second]
  smul_mem' := by
    intro scalar jet hJet first second
    simp only [Prod.smul_snd, smul_apply]
    rw [hJet first second]

/-- Exact componentwise equivalence with the symmetric submodule. -/
def framedSecondOrderJetEquivSymmetricSubmodule :
    FramedSecondOrderJet Domain Fiber ≃
      framedSecondOrderJetSymmetricSubmodule Domain Fiber where
  toFun jet :=
    ⟨(jet.value, jet.firstDerivative, jet.secondDerivative),
      jet.secondDerivative_symmetric⟩
  invFun components :=
    { value := components.1.1
      firstDerivative := components.1.2.1
      secondDerivative := components.1.2.2
      secondDerivative_symmetric := components.2 }
  left_inv jet := by
    cases jet
    rfl
  right_inv components := by
    cases components
    rfl

/-- Componentwise additive commutative group on framed second jets. -/
instance framedSecondOrderJetAddCommGroup :
    AddCommGroup (FramedSecondOrderJet Domain Fiber) :=
  (framedSecondOrderJetEquivSymmetricSubmodule Domain Fiber).addCommGroup

/-- Componentwise real module on framed second jets. -/
instance framedSecondOrderJetModule :
    Module Real (FramedSecondOrderJet Domain Fiber) :=
  Equiv.module Real
    (framedSecondOrderJetEquivSymmetricSubmodule Domain Fiber)

/-- The transported equivalence is real-linear. -/
def framedSecondOrderJetLinearEquivSymmetricSubmodule :
    FramedSecondOrderJet Domain Fiber ≃ₗ[Real]
      framedSecondOrderJetSymmetricSubmodule Domain Fiber :=
  Equiv.linearEquiv Real
    (framedSecondOrderJetEquivSymmetricSubmodule Domain Fiber)

/-- Linear inclusion of a framed second jet into its ambient component
product. -/
def framedSecondOrderJetComponentLinearMap :
    FramedSecondOrderJet Domain Fiber →ₗ[Real]
      FramedSecondOrderJetAmbient Domain Fiber :=
  (framedSecondOrderJetSymmetricSubmodule Domain Fiber).subtype.comp
    (framedSecondOrderJetLinearEquivSymmetricSubmodule
      Domain Fiber).toLinearMap

theorem framedSecondOrderJetComponentLinearMap_injective :
    Function.Injective
      (framedSecondOrderJetComponentLinearMap Domain Fiber) := by
  intro first second hComponents
  apply
    (framedSecondOrderJetLinearEquivSymmetricSubmodule
      Domain Fiber).injective
  exact Subtype.ext hComponents

/-- Explicit scalar norm compatibility on the symmetric submodule. -/
instance framedSecondOrderJetSymmetricSubmoduleNormedSpace :
    NormedSpace Real
      (framedSecondOrderJetSymmetricSubmodule Domain Fiber) :=
  Submodule.normedSpace
    (𝕜 := Real) (R := Real)
    (E := FramedSecondOrderJetAmbient Domain Fiber)
    (framedSecondOrderJetSymmetricSubmodule Domain Fiber)

/-- Product-subspace norm on framed second jets. -/
instance framedSecondOrderJetNormedAddCommGroup :
    NormedAddCommGroup (FramedSecondOrderJet Domain Fiber) :=
  NormedAddCommGroup.induced
    (FramedSecondOrderJet Domain Fiber)
    (framedSecondOrderJetSymmetricSubmodule Domain Fiber)
    (framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber)
    (framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber).injective

/-- The product-subspace norm makes framed second jets a real normed space. -/
instance framedSecondOrderJetNormedSpace :
    NormedSpace Real (FramedSecondOrderJet Domain Fiber) :=
  NormedSpace.induced Real
    (FramedSecondOrderJet Domain Fiber)
    (framedSecondOrderJetSymmetricSubmodule Domain Fiber)
    (framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber)

/-- The transported norm makes the component equivalence an isometry. -/
def framedSecondOrderJetLinearIsometryEquivSymmetricSubmodule :
    FramedSecondOrderJet Domain Fiber ≃ₗᵢ[Real]
      framedSecondOrderJetSymmetricSubmodule Domain Fiber where
  toLinearEquiv :=
    framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber
  norm_map' _ := rfl

/-- Finite-dimensional domain and fiber give a finite-dimensional jet
carrier; no numerical rank is fixed here. -/
instance framedSecondOrderJetFiniteDimensional
    [FiniteDimensional Real Domain]
    [FiniteDimensional Real Fiber] :
    FiniteDimensional Real (FramedSecondOrderJet Domain Fiber) :=
  FiniteDimensional.of_injective
    (framedSecondOrderJetComponentLinearMap Domain Fiber)
    (framedSecondOrderJetComponentLinearMap_injective Domain Fiber)

/-- Finite-dimensional framed second jets are complete. -/
instance framedSecondOrderJetCompleteSpace
    [FiniteDimensional Real Domain]
    [FiniteDimensional Real Fiber] :
    CompleteSpace (FramedSecondOrderJet Domain Fiber) :=
  FiniteDimensional.complete Real (FramedSecondOrderJet Domain Fiber)

@[ext]
theorem FramedSecondOrderJet.ext_components
    {first second : FramedSecondOrderJet Domain Fiber}
    (hValue : first.value = second.value)
    (hFirst : first.firstDerivative = second.firstDerivative)
    (hSecond : first.secondDerivative = second.secondDerivative) :
    first = second := by
  cases first
  cases second
  simp_all

@[simp]
theorem FramedSecondOrderJet.zero_value :
    (0 : FramedSecondOrderJet Domain Fiber).value = 0 :=
  rfl

@[simp]
theorem FramedSecondOrderJet.zero_firstDerivative :
    (0 : FramedSecondOrderJet Domain Fiber).firstDerivative = 0 :=
  rfl

@[simp]
theorem FramedSecondOrderJet.zero_secondDerivative :
    (0 : FramedSecondOrderJet Domain Fiber).secondDerivative = 0 :=
  rfl

@[simp]
theorem FramedSecondOrderJet.add_value
    (first second : FramedSecondOrderJet Domain Fiber) :
    (first + second).value = first.value + second.value :=
  rfl

@[simp]
theorem FramedSecondOrderJet.add_firstDerivative
    (first second : FramedSecondOrderJet Domain Fiber) :
    (first + second).firstDerivative =
      first.firstDerivative + second.firstDerivative :=
  rfl

@[simp]
theorem FramedSecondOrderJet.add_secondDerivative
    (first second : FramedSecondOrderJet Domain Fiber) :
    (first + second).secondDerivative =
      first.secondDerivative + second.secondDerivative :=
  rfl

@[simp]
theorem FramedSecondOrderJet.neg_value
    (jet : FramedSecondOrderJet Domain Fiber) :
    (-jet).value = -jet.value :=
  rfl

@[simp]
theorem FramedSecondOrderJet.neg_firstDerivative
    (jet : FramedSecondOrderJet Domain Fiber) :
    (-jet).firstDerivative = -jet.firstDerivative :=
  rfl

@[simp]
theorem FramedSecondOrderJet.neg_secondDerivative
    (jet : FramedSecondOrderJet Domain Fiber) :
    (-jet).secondDerivative = -jet.secondDerivative :=
  rfl

@[simp]
theorem FramedSecondOrderJet.smul_value
    (scalar : Real) (jet : FramedSecondOrderJet Domain Fiber) :
    (scalar • jet).value = scalar • jet.value :=
  rfl

@[simp]
theorem FramedSecondOrderJet.smul_firstDerivative
    (scalar : Real) (jet : FramedSecondOrderJet Domain Fiber) :
    (scalar • jet).firstDerivative = scalar • jet.firstDerivative :=
  rfl

@[simp]
theorem FramedSecondOrderJet.smul_secondDerivative
    (scalar : Real) (jet : FramedSecondOrderJet Domain Fiber) :
    (scalar • jet).secondDerivative = scalar • jet.secondDerivative :=
  rfl

@[simp]
theorem framedSecondOrderJetLinearEquivSymmetricSubmodule_apply
    (jet : FramedSecondOrderJet Domain Fiber) :
    framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber jet =
      ⟨(jet.value, jet.firstDerivative, jet.secondDerivative),
        jet.secondDerivative_symmetric⟩ :=
  rfl

@[simp]
theorem framedSecondOrderJet_norm_eq
    (jet : FramedSecondOrderJet Domain Fiber) :
    ‖jet‖ =
      ‖framedSecondOrderJetLinearEquivSymmetricSubmodule Domain Fiber jet‖ :=
  rfl

end
end P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
end JanusFormal
