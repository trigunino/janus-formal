namespace JanusFormal
namespace P0EFTDeltaNeffResidualClosure

set_option autoImplicit false

structure DeltaNeffResidualClosure where
  baseHolstPlasmaCandidateFound : Prop
  residualCorrectionTargetEncoded : Prop
  residualCorrectionDerived : Prop

def residualClosureDiagnosticReady (d : DeltaNeffResidualClosure) : Prop :=
  d.baseHolstPlasmaCandidateFound /\
  d.residualCorrectionTargetEncoded

def residualClosureNoFitReady (d : DeltaNeffResidualClosure) : Prop :=
  residualClosureDiagnosticReady d /\
  d.residualCorrectionDerived

theorem residual_correction_target_opens_final_derivation
    (d : DeltaNeffResidualClosure)
    (hBase : d.baseHolstPlasmaCandidateFound)
    (hTarget : d.residualCorrectionTargetEncoded) :
    residualClosureDiagnosticReady d := by
  exact And.intro hBase hTarget

theorem missing_residual_correction_derivation_blocks_no_fit
    (d : DeltaNeffResidualClosure)
    (hMissing : Not d.residualCorrectionDerived) :
    Not (residualClosureNoFitReady d) := by
  intro h
  exact hMissing h.right

end P0EFTDeltaNeffResidualClosure
end JanusFormal
