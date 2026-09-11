import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

/-!
# Linear structure on framed third-order jets

The algebraic operations are defined componentwise.  The map to the product
of the four raw components is injective, so it transports the additive-group
and module laws without introducing a second submodule instance.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
noncomputable section

open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

variable
    (Base Fiber : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Ambient product containing the four components of a framed third jet. -/
abbrev FramedThirdOrderJetAmbient :=
  Fiber × (Base →L[Real] Fiber) ×
    (Base →L[Real] Base →L[Real] Fiber) ×
    (Base →L[Real] Base →L[Real] Base →L[Real] Fiber)

instance framedThirdOrderJetZero : Zero (FramedThirdOrderJet Base Fiber) where
  zero :=
    { toFramedSecondOrderJet :=
        { value := 0
          firstDerivative := 0
          secondDerivative := 0
          secondDerivative_symmetric := by
            intro first second
            simp }
      thirdDerivative := 0
      thirdDerivative_swap_first_second := by
        intro first second third
        simp
      thirdDerivative_swap_second_third := by
        intro first second third
        simp }

instance framedThirdOrderJetAdd : Add (FramedThirdOrderJet Base Fiber) where
  add left right :=
    { toFramedSecondOrderJet :=
        { value := left.value + right.value
          firstDerivative := left.firstDerivative + right.firstDerivative
          secondDerivative := left.secondDerivative + right.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [add_apply]
            rw [left.secondDerivative_symmetric first second,
              right.secondDerivative_symmetric first second] }
      thirdDerivative := left.thirdDerivative + right.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [add_apply]
        rw [left.thirdDerivative_swap_first_second first second third,
          right.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [add_apply]
        rw [left.thirdDerivative_swap_second_third first second third,
          right.thirdDerivative_swap_second_third first second third] }

instance framedThirdOrderJetNeg : Neg (FramedThirdOrderJet Base Fiber) where
  neg jet :=
    { toFramedSecondOrderJet :=
        { value := -jet.value
          firstDerivative := -jet.firstDerivative
          secondDerivative := -jet.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [neg_apply]
            rw [jet.secondDerivative_symmetric first second] }
      thirdDerivative := -jet.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [neg_apply]
        rw [jet.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [neg_apply]
        rw [jet.thirdDerivative_swap_second_third first second third] }

instance framedThirdOrderJetSub : Sub (FramedThirdOrderJet Base Fiber) where
  sub left right :=
    { toFramedSecondOrderJet :=
        { value := left.value - right.value
          firstDerivative := left.firstDerivative - right.firstDerivative
          secondDerivative := left.secondDerivative - right.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [sub_apply]
            rw [left.secondDerivative_symmetric first second,
              right.secondDerivative_symmetric first second] }
      thirdDerivative := left.thirdDerivative - right.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [sub_apply]
        rw [left.thirdDerivative_swap_first_second first second third,
          right.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [sub_apply]
        rw [left.thirdDerivative_swap_second_third first second third,
          right.thirdDerivative_swap_second_third first second third] }

instance framedThirdOrderJetNSMul : SMul Nat (FramedThirdOrderJet Base Fiber) where
  smul scalar jet :=
    { toFramedSecondOrderJet :=
        { value := scalar • jet.value
          firstDerivative := scalar • jet.firstDerivative
          secondDerivative := scalar • jet.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [smul_apply]
            rw [jet.secondDerivative_symmetric first second] }
      thirdDerivative := scalar • jet.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_second_third first second third] }

instance framedThirdOrderJetZSMul : SMul Int (FramedThirdOrderJet Base Fiber) where
  smul scalar jet :=
    { toFramedSecondOrderJet :=
        { value := scalar • jet.value
          firstDerivative := scalar • jet.firstDerivative
          secondDerivative := scalar • jet.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [smul_apply]
            rw [jet.secondDerivative_symmetric first second] }
      thirdDerivative := scalar • jet.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_second_third first second third] }

instance framedThirdOrderJetSMul : SMul Real (FramedThirdOrderJet Base Fiber) where
  smul scalar jet :=
    { toFramedSecondOrderJet :=
        { value := scalar • jet.value
          firstDerivative := scalar • jet.firstDerivative
          secondDerivative := scalar • jet.secondDerivative
          secondDerivative_symmetric := by
            intro first second
            simp only [smul_apply]
            rw [jet.secondDerivative_symmetric first second] }
      thirdDerivative := scalar • jet.thirdDerivative
      thirdDerivative_swap_first_second := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_first_second first second third]
      thirdDerivative_swap_second_third := by
        intro first second third
        simp only [smul_apply]
        rw [jet.thirdDerivative_swap_second_third first second third] }

/-- The four raw components of a framed third jet. -/
def framedThirdOrderJetComponents
    (jet : FramedThirdOrderJet Base Fiber) :
    FramedThirdOrderJetAmbient Base Fiber :=
  (jet.value, jet.firstDerivative, jet.secondDerivative, jet.thirdDerivative)

theorem framedThirdOrderJetComponents_injective :
    Function.Injective (framedThirdOrderJetComponents Base Fiber) := by
  intro first second hComponents
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · exact congrArg (fun components => components.1) hComponents
    · exact congrArg (fun components => components.2.1) hComponents
    · exact congrArg (fun components => components.2.2.1) hComponents
  · exact congrArg (fun components => components.2.2.2) hComponents

instance framedThirdOrderJetAddCommGroup :
    AddCommGroup (FramedThirdOrderJet Base Fiber) :=
  Function.Injective.addCommGroup
    (framedThirdOrderJetComponents Base Fiber)
    (framedThirdOrderJetComponents_injective Base Fiber)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The component inclusion as an additive homomorphism. -/
def framedThirdOrderJetComponentAddMonoidHom :
    FramedThirdOrderJet Base Fiber →+
      FramedThirdOrderJetAmbient Base Fiber where
  toFun := framedThirdOrderJetComponents Base Fiber
  map_zero' := rfl
  map_add' _ _ := rfl

instance framedThirdOrderJetModule :
    Module Real (FramedThirdOrderJet Base Fiber) :=
  Function.Injective.module Real
    (M := FramedThirdOrderJetAmbient Base Fiber)
    (M₂ := FramedThirdOrderJet Base Fiber)
    (framedThirdOrderJetComponentAddMonoidHom Base Fiber)
    (framedThirdOrderJetComponents_injective Base Fiber)
    (fun scalar jet => by
      rfl)

/-- Linear inclusion of a framed third jet into its ambient component
product. -/
def framedThirdOrderJetComponentLinearMap :
    FramedThirdOrderJet Base Fiber →ₗ[Real]
      FramedThirdOrderJetAmbient Base Fiber where
  toFun := framedThirdOrderJetComponents Base Fiber
  map_add' _ _ := rfl
  map_smul' scalar jet := by
    change
      (scalar • jet.value, scalar • jet.firstDerivative,
        scalar • jet.secondDerivative, scalar • jet.thirdDerivative) =
      (scalar • jet.value, scalar • jet.firstDerivative,
        scalar • jet.secondDerivative, scalar • jet.thirdDerivative)
    rfl

@[simp]
theorem FramedThirdOrderJet.zero_value :
    (0 : FramedThirdOrderJet Base Fiber).value = 0 :=
  rfl

@[simp]
theorem FramedThirdOrderJet.zero_firstDerivative :
    (0 : FramedThirdOrderJet Base Fiber).firstDerivative = 0 :=
  rfl

@[simp]
theorem FramedThirdOrderJet.zero_secondDerivative :
    (0 : FramedThirdOrderJet Base Fiber).secondDerivative = 0 :=
  rfl

@[simp]
theorem FramedThirdOrderJet.zero_thirdDerivative :
    (0 : FramedThirdOrderJet Base Fiber).thirdDerivative = 0 :=
  rfl

@[simp]
theorem FramedThirdOrderJet.add_value
    (first second : FramedThirdOrderJet Base Fiber) :
    (first + second).value = first.value + second.value :=
  rfl

@[simp]
theorem FramedThirdOrderJet.add_firstDerivative
    (first second : FramedThirdOrderJet Base Fiber) :
    (first + second).firstDerivative =
      first.firstDerivative + second.firstDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.add_secondDerivative
    (first second : FramedThirdOrderJet Base Fiber) :
    (first + second).secondDerivative =
      first.secondDerivative + second.secondDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.add_thirdDerivative
    (first second : FramedThirdOrderJet Base Fiber) :
    (first + second).thirdDerivative =
      first.thirdDerivative + second.thirdDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.smul_value
    (scalar : Real) (jet : FramedThirdOrderJet Base Fiber) :
    (scalar • jet).value = scalar • jet.value :=
  rfl

@[simp]
theorem FramedThirdOrderJet.smul_firstDerivative
    (scalar : Real) (jet : FramedThirdOrderJet Base Fiber) :
    (scalar • jet).firstDerivative = scalar • jet.firstDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.smul_secondDerivative
    (scalar : Real) (jet : FramedThirdOrderJet Base Fiber) :
    (scalar • jet).secondDerivative = scalar • jet.secondDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.smul_thirdDerivative
    (scalar : Real) (jet : FramedThirdOrderJet Base Fiber) :
    (scalar • jet).thirdDerivative = scalar • jet.thirdDerivative :=
  rfl

@[simp]
theorem FramedThirdOrderJet.add_toFramedSecondOrderJet
    (first second : FramedThirdOrderJet Base Fiber) :
    (first + second).toFramedSecondOrderJet =
      first.toFramedSecondOrderJet + second.toFramedSecondOrderJet := by
  apply FramedSecondOrderJet.ext_components <;> rfl

@[simp]
theorem FramedThirdOrderJet.smul_toFramedSecondOrderJet
    (scalar : Real) (jet : FramedThirdOrderJet Base Fiber) :
    (scalar • jet).toFramedSecondOrderJet =
      scalar • jet.toFramedSecondOrderJet := by
  apply FramedSecondOrderJet.ext_components <;> rfl

end
end P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
end JanusFormal
