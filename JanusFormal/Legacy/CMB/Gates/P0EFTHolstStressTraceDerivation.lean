namespace JanusFormal
namespace P0EFTHolstStressTraceDerivation

set_option autoImplicit false

structure HolstStressTraceDerivation where
  radiationEquationOfState : Prop
  transverseShearTraceFree : Prop
  holstStressTraceFree : Prop
  signConventionChecked : Prop

def traceDerivationReady (h : HolstStressTraceDerivation) : Prop :=
  h.radiationEquationOfState /\
  h.transverseShearTraceFree /\
  h.holstStressTraceFree

def cambPatchReady (h : HolstStressTraceDerivation) : Prop :=
  traceDerivationReady h /\
  h.signConventionChecked

theorem radiation_transverse_stress_closes_trace
    (h : HolstStressTraceDerivation)
    (hRad : h.radiationEquationOfState)
    (hShear : h.transverseShearTraceFree)
    (hTrace : h.holstStressTraceFree) :
    traceDerivationReady h := by
  exact And.intro hRad (And.intro hShear hTrace)

theorem missing_sign_check_blocks_camb_patch
    (h : HolstStressTraceDerivation)
    (_hTrace : traceDerivationReady h)
    (hMissing : Not h.signConventionChecked) :
    Not (cambPatchReady h) := by
  intro ready
  exact hMissing ready.right

end P0EFTHolstStressTraceDerivation
end JanusFormal
