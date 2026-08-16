import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianQuillenMellinFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D

/-!
# Public zeta/Quillen frontier after the reduced global Hessian

The preferred terminal route now starts with an honest parameter-uniform
Mellin continuation of the intrinsic relative heat trace.  It constructs the
zeta family, its finite-part metric comparison and its unitary phase before
assembling the circle bridge and the general determinant-line atlas.

The older scalar-only zeta determinant and abstract coherent-frontier gates
remain exported as compatibility checkpoints.  The public gate, however, no
longer accepts an unrelated complex germ merely having the desired derivative
at zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedIntrinsicRelativeTrace4D
open P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
open P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D
open P0EFTJanusProgramPGlobalHessianQuillenMellinFrontier4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaComparison4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- Intrinsic positive-time relative trace input. -/
def GlobalHessianIntrinsicRelativeTraceInput :=
  GlobalCandidateAAugmentedReducedIntrinsicRelativeTraceData4D

/-- Pointwise short-time finite-part input. -/
def GlobalHessianFinitePartRenormalizationInput :=
  RelativeHeatFinitePartData

/-- Honest pointwise heat-Mellin continuation. -/
def GlobalHessianMellinZetaContinuationInput :=
  RelativeHeatMellinZetaContinuationData

/-- Parameter-uniform Mellin continuation, finite-part metric and zeta phase. -/
def GlobalHessianMellinZetaFamilyInput :=
  RelativeHeatMellinZetaFamilyData

/-- General-cover local zeta atlas anchored at the Candidate-A determinant. -/
def GlobalHessianZetaAtlasInput :=
  GlobalCandidateAHessianZetaDeterminantAtlasData4D

/-- Preferred terminal input: one Mellin family, one circle bridge and one
atlas whose selected chart is that family. -/
def GlobalHessianQuillenMellinInput :=
  GlobalCandidateAHessianQuillenMellinFrontierData4D

/-- Compatibility input for callers already holding the abstract coherent
circle/atlas/metric packet. -/
def GlobalHessianQuillenFinalInput :=
  GlobalCandidateAHessianQuillenFinalFrontierData4D

/-- Preferred public terminal gate generated from the heat Mellin family. -/
def global_candidateA_hessian_zeta_quillen_frontier_gate :=
  @global_candidateA_hessian_quillen_mellin_frontier_gate

/-- Compatibility checkpoint for the abstract coherent final packet. -/
def global_candidateA_hessian_zeta_quillen_coherent_gate :=
  @global_candidateA_hessian_quillen_final_frontier_gate

/-- Compatibility checkpoint returning only the complex determinant. -/
def global_candidateA_hessian_zeta_determinant_only_gate :=
  @global_candidateA_hessian_zeta_determinant_gate

/-- The finite-part value is independent of equivalent subtraction schemes. -/
def global_candidateA_hessian_finitePart_scheme_independence_gate :=
  @relative_heat_finite_part_scheme_independence_gate

/-- Four genuinely analytic constructions remain beyond the concrete H10--H14
operator: intrinsic trace uniqueness, uniform heat renormalization, Mellin
continuation in the family, and the Bismut--Freed/circle-atlas coherence data. -/
theorem global_candidateA_hessian_zeta_quillen_frontier_four_inputs :
    Nonempty (Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D
end JanusFormal
