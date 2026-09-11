import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetLinearStructure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetNormedSpace4D

/-!
# Normed vector-space structure on framed third-order jets

The component inclusion induces the product norm on framed third jets.  In
finite dimensions this also gives finite dimensionality and completeness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

set_option autoImplicit false
noncomputable section

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable
    (Base Fiber : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev FramedThirdJetFirstDerivative :=
  Base →L[Real] Fiber

local instance framedThirdJetFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FramedThirdJetFirstDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance framedThirdJetFirstDerivativeNormedSpace :
    NormedSpace Real (FramedThirdJetFirstDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FramedThirdJetSecondDerivative :=
  Base →L[Real] FramedThirdJetFirstDerivative Base Fiber

local instance framedThirdJetSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FramedThirdJetSecondDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance framedThirdJetSecondDerivativeNormedSpace :
    NormedSpace Real (FramedThirdJetSecondDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FramedThirdJetThirdDerivative :=
  Base →L[Real] FramedThirdJetSecondDerivative Base Fiber

local instance framedThirdJetThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FramedThirdJetThirdDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance framedThirdJetThirdDerivativeNormedSpace :
    NormedSpace Real (FramedThirdJetThirdDerivative Base Fiber) :=
  ContinuousLinearMap.toNormedSpace

theorem framedThirdOrderJetComponentLinearMap_injective :
    Function.Injective
      (framedThirdOrderJetComponentLinearMap Base Fiber) :=
  framedThirdOrderJetComponents_injective Base Fiber

/-- Product norm induced by the four jet components. -/
instance framedThirdOrderJetNormedAddCommGroup :
    NormedAddCommGroup (FramedThirdOrderJet Base Fiber) :=
  NormedAddCommGroup.induced
    (FramedThirdOrderJet Base Fiber)
    (FramedThirdOrderJetAmbient Base Fiber)
    (framedThirdOrderJetComponentAddMonoidHom Base Fiber)
    (framedThirdOrderJetComponents_injective Base Fiber)

/-- The component norm makes framed third jets a real normed space. -/
instance framedThirdOrderJetNormedSpace :
    NormedSpace Real (FramedThirdOrderJet Base Fiber) :=
  NormedSpace.induced Real
    (FramedThirdOrderJet Base Fiber)
    (FramedThirdOrderJetAmbient Base Fiber)
    (framedThirdOrderJetComponentLinearMap Base Fiber)

/-- The component inclusion is an isometry for the induced norm. -/
def framedThirdOrderJetComponentLinearIsometry :
    FramedThirdOrderJet Base Fiber →ₗᵢ[Real]
      FramedThirdOrderJetAmbient Base Fiber where
  toLinearMap := framedThirdOrderJetComponentLinearMap Base Fiber
  norm_map' _ := rfl

/-- Finite-dimensional base and fiber give a finite-dimensional third-jet
carrier. -/
instance framedThirdOrderJetFiniteDimensional
    [FiniteDimensional Real Base]
    [FiniteDimensional Real Fiber] :
    FiniteDimensional Real (FramedThirdOrderJet Base Fiber) :=
  FiniteDimensional.of_injective
    (framedThirdOrderJetComponentLinearMap Base Fiber)
    (framedThirdOrderJetComponentLinearMap_injective Base Fiber)

/-- Finite-dimensional framed third jets are complete. -/
instance framedThirdOrderJetCompleteSpace
    [FiniteDimensional Real Base]
    [FiniteDimensional Real Fiber] :
    CompleteSpace (FramedThirdOrderJet Base Fiber) :=
  FiniteDimensional.complete Real (FramedThirdOrderJet Base Fiber)

@[simp]
theorem framedThirdOrderJet_norm_eq
    (jet : FramedThirdOrderJet Base Fiber) :
    ‖jet‖ =
      ‖framedThirdOrderJetComponentLinearMap Base Fiber jet‖ :=
  rfl

end
end P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
end JanusFormal
