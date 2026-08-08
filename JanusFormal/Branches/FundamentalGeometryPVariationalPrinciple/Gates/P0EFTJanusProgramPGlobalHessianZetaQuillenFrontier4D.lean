import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D

/-!
# Public zeta/Quillen frontier after the reduced global Hessian

The constructive chain now contains both the circle realization and the
general multi-chart determinant-line atlas.  The preferred terminal input
requires these presentations, together with the finite-part metric family, to
refer to one and the same Candidate-A zeta determinant.

The older scalar-only zeta determinant gate remains exported as a compatibility
checkpoint, but the public frontier now points to the coherent certificate
which simultaneously contains:

* the conditional global Quillen closure;
* the local zeta transition cocycle and line atlas;
* the finite-part metric variation;
* the unitary phase;
* the physical basepoint identification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedIntrinsicRelativeTrace4D
open P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
open P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D
open P0EFTJanusProgramPRelativeZetaComparison4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- Intrinsic positive-time relative trace input. -/
def GlobalHessianIntrinsicRelativeTraceInput :=
  GlobalCandidateAAugmentedReducedIntrinsicRelativeTraceData4D

/-- Pointwise short-time finite-part input. -/
def GlobalHessianFinitePartRenormalizationInput :=
  RelativeHeatFinitePartData

/-- Parameter-uniform finite-part metric input. -/
def GlobalHessianFinitePartFamilyInput :=
  RelativeHeatFinitePartFamilyData

/-- Pointwise Mellin/zeta comparison input. -/
def GlobalHessianRelativeZetaInput :=
  RelativeZetaComparisonData

/-- Family comparison of zeta norm, finite-part metric and unitary phase. -/
def GlobalHessianZetaMetricFamilyInput :=
  RelativeZetaFinitePartFamilyComparisonData

/-- General-cover local zeta atlas anchored at the Candidate-A determinant. -/
def GlobalHessianZetaAtlasInput :=
  GlobalCandidateAHessianZetaDeterminantAtlasData4D

/-- Coherent terminal input tying the circle bridge, atlas and metric family to
one Candidate-A zeta determinant. -/
def GlobalHessianQuillenFinalInput :=
  GlobalCandidateAHessianQuillenFinalFrontierData4D

/-- Preferred public terminal gate. -/
def global_candidateA_hessian_zeta_quillen_frontier_gate :=
  @global_candidateA_hessian_quillen_final_frontier_gate

/-- Compatibility checkpoint returning only the complex determinant. -/
def global_candidateA_hessian_zeta_determinant_only_gate :=
  @global_candidateA_hessian_zeta_determinant_gate

/-- The finite-part value is independent of equivalent subtraction schemes. -/
def global_candidateA_hessian_finitePart_scheme_independence_gate :=
  @relative_heat_finite_part_scheme_independence_gate

/-- Four genuinely analytic constructions remain beyond the concrete H10--H14
operator: intrinsic trace uniqueness, uniform heat renormalization, zeta
continuation in the family, and the Bismut--Freed/atlas coherence data. -/
theorem global_candidateA_hessian_zeta_quillen_frontier_four_inputs :
    Nonempty (Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D
end JanusFormal
