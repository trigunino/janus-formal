import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTSpinlessMomentsSlipTarget

namespace JanusFormal
namespace P0EFTSlipJumpDerivation

set_option autoImplicit false

structure SlipJumpDerivation where
  perturbedJumpStructureEncoded : Prop
  stfAnisotropicSourceIdentified : Prop
  run1SourceSubstituted : Prop
  derivativeJumpSlipSourceClosed : Prop
  boundaryGreenFunctionKnown : Prop
  algebraicValueSlipDerived : Prop
  lensingGrowthSourcesClosed : Prop

def derivativeSlipClosed (s : SlipJumpDerivation) : Prop :=
  s.perturbedJumpStructureEncoded /\
  s.stfAnisotropicSourceIdentified /\
  s.run1SourceSubstituted /\
  s.derivativeJumpSlipSourceClosed

def valueSlipClosed (s : SlipJumpDerivation) : Prop :=
  derivativeSlipClosed s /\
  s.boundaryGreenFunctionKnown /\
  s.algebraicValueSlipDerived

def observableSlipClosed (s : SlipJumpDerivation) : Prop :=
  valueSlipClosed s /\ s.lensingGrowthSourcesClosed

theorem jump_equations_close_derivative_slip
    (s : SlipJumpDerivation)
    (hJump : s.perturbedJumpStructureEncoded)
    (hSTF : s.stfAnisotropicSourceIdentified)
    (hRun1 : s.run1SourceSubstituted)
    (hDeriv : s.derivativeJumpSlipSourceClosed) :
    derivativeSlipClosed s := by
  exact And.intro hJump (And.intro hSTF (And.intro hRun1 hDeriv))

theorem missing_green_function_blocks_value_slip
    (s : SlipJumpDerivation)
    (hMissing : Not s.boundaryGreenFunctionKnown) :
    Not (valueSlipClosed s) := by
  intro h
  exact hMissing h.right.left

theorem green_function_closes_value_slip
    (s : SlipJumpDerivation)
    (hDeriv : derivativeSlipClosed s)
    (hGreen : s.boundaryGreenFunctionKnown)
    (hValue : s.algebraicValueSlipDerived) :
    valueSlipClosed s := by
  exact And.intro hDeriv (And.intro hGreen hValue)

end P0EFTSlipJumpDerivation
end JanusFormal
