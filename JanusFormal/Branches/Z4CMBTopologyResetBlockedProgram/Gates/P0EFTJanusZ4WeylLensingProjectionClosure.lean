import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4LensingAmplitudeDiagnostic
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLensingSourceTarget

namespace JanusFormal
namespace P0EFTJanusZ4WeylLensingProjectionClosure

set_option autoImplicit false

structure WeylLensingProjectionClosure where
  geodesicKernelResidualDeclared : Prop
  weylSourceResidualDeclared : Prop
  determinantLeakageResidualDeclared : Prop
  crossSectorLeakageResidualDeclared : Prop
  uniqueAlgebraicSolution : Prop
  substitutedResidualsVanish : Prop
  geodesicProjectionDerived : Prop
  weylSourceDerived : Prop

def lensingProjectionScaffoldReady (w : WeylLensingProjectionClosure) : Prop :=
  w.geodesicKernelResidualDeclared /\
  w.weylSourceResidualDeclared /\
  w.determinantLeakageResidualDeclared /\
  w.crossSectorLeakageResidualDeclared

def lensingProjectionAlgebraicallyClosed (w : WeylLensingProjectionClosure) : Prop :=
  lensingProjectionScaffoldReady w /\
  w.uniqueAlgebraicSolution /\
  w.substitutedResidualsVanish

def lensingProjectionPhysicalReady (w : WeylLensingProjectionClosure) : Prop :=
  lensingProjectionAlgebraicallyClosed w /\ w.geodesicProjectionDerived /\ w.weylSourceDerived

theorem lensing_projection_scaffold_does_not_close_physics
    (w : WeylLensingProjectionClosure)
    (_h : lensingProjectionScaffoldReady w)
    (hMissing : Not (w.geodesicProjectionDerived /\ w.weylSourceDerived)) :
    Not (lensingProjectionPhysicalReady w) := by
  intro h
  exact hMissing h.right

theorem weyl_source_target_feeds_projection_lock
    (w : WeylLensingProjectionClosure)
    (t : P0EFTJanusZ4WeylLensingSourceTarget.WeylLensingSourceTarget)
    (hAlg : lensingProjectionAlgebraicallyClosed w)
    (hSource : t.sourceCoefficientsDerived)
    (hTransport :
      t.sourceCoefficientsDerived -> w.geodesicProjectionDerived /\ w.weylSourceDerived) :
    lensingProjectionPhysicalReady w := by
  exact And.intro hAlg (hTransport hSource)

end P0EFTJanusZ4WeylLensingProjectionClosure
end JanusFormal
