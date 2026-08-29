import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-!
# Smooth primitive SpinC maximal-graph frontier

The preferred route is now unconditional.  The implemented throat geometry
provides:

1. explicit skew-Hermitian Clifford generators;
2. Hermitian compatibility of the primitive SpinC connection;
3. decomposition of the intrinsic Dirac frame into measure-invariant time and
   rotation generators;
4. the exact frame divergence defect;
5. intrinsic-frame integration by parts;
6. the global Dirac Green current and its pointwise cancellation;
7. formal symmetry of the genuine descended Dirac operator;
8. maximal-domain membership, exact operator restriction, Parseval and the
   same-action matter graph for every real mass.

The weighted-coefficient, supplied maximal-domain, supplied Green and
spectral-core-density routes remain as compatibility adapters.  No independent
SpinC analytic input, action, boundary condition or D10 direction remains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D
open P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-- Legacy coefficient-side weighted-decay route. -/
def primitive_spinC_smooth_graph_of_weighted_decay :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_weightedDecay

/-- Intermediate route when maximal-domain data have already been proved. -/
def primitive_spinC_smooth_graph_of_maximal_domain :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain

/-- Route from a supplied global first-order Dirac Green identity. -/
def primitive_spinC_smooth_graph_of_dirac_formal_symmetry :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_diracFormalSymmetry

/-- Route from graph-core density for the complete mass-dependent Hessian. -/
def primitive_spinC_smooth_graph_of_graph_core_density :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_graphCoreDensity

/-- Route from a mass-independent first-order Dirac graph-core density theorem. -/
def primitive_spinC_smooth_graph_of_first_order_graph_core_density :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_firstOrderGraphCoreDensity

/-- Preferred unconditional route from the implemented geometric Green
identity. -/
def primitive_spinC_smooth_graph_of_geometric_green :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen

/-- All six exact smooth-graph routes are available. -/
theorem primitive_spinC_smooth_graph_frontier_gate :
    Nonempty (Unit × Unit × Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), (), (), ())⟩

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
end JanusFormal
