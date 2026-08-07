import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D

/-!
# Smooth primitive SpinC maximal-graph frontier

This façade records all exact reductions of the smooth matter graph problem.
The preferred route is now mass-independent:

1. finite signed Fourier packets are an exact Green core;
2. the packets are dense simultaneously for `ψ` and the first-order `Dψ`;
3. bounded linear combination gives graph-core density for every `2D + m²`;
4. the finite Green identity extends to the full smooth core;
5. coefficient intertwining, maximal-domain membership, operator restriction,
   Parseval and same-action compatibility follow canonically.

The older weighted-coefficient, supplied maximal-domain and supplied Green
routes remain as compatibility adapters.  No independent coefficient choice,
action, boundary condition or D10 direction is introduced.
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

/-- Preferred route from one mass-independent first-order Dirac graph-core
density theorem. -/
def primitive_spinC_smooth_graph_of_first_order_graph_core_density :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_firstOrderGraphCoreDensity

/-- All five exact smooth-graph routes are available. -/
theorem primitive_spinC_smooth_graph_frontier_gate :
    Nonempty (Unit × Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), (), ())⟩

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
end JanusFormal
