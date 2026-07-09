namespace JanusFormal
namespace P0EFTJanusSigmaBoundaryActionSupportGate

set_option autoImplicit false

structure SigmaBoundaryActionSupportGate where
  throatSigmaDefined : Prop
  boundaryTermsLocalizedOnSigma : Prop
  antipodalFixedPointBoundaryForbidden : Prop
  tunnelJunctionDataDeclared : Prop
  nonlinearBoundaryVariationOnSigmaClosed : Prop
  fullBoundaryActionClosedOnSigma : Prop

def sigmaBoundarySupportDeclared
    (g : SigmaBoundaryActionSupportGate) : Prop :=
  g.throatSigmaDefined /\
  g.boundaryTermsLocalizedOnSigma /\
  g.antipodalFixedPointBoundaryForbidden /\
  g.tunnelJunctionDataDeclared

def sigmaBoundaryActionClosed
    (g : SigmaBoundaryActionSupportGate) : Prop :=
  sigmaBoundarySupportDeclared g /\
  g.nonlinearBoundaryVariationOnSigmaClosed /\
  g.fullBoundaryActionClosedOnSigma

theorem missing_sigma_nonlinear_variation_blocks_boundary_action
    (g : SigmaBoundaryActionSupportGate)
    (hMissing : Not g.nonlinearBoundaryVariationOnSigmaClosed) :
    Not (sigmaBoundaryActionClosed g) := by
  intro h
  exact hMissing h.2.1

end P0EFTJanusSigmaBoundaryActionSupportGate
end JanusFormal
