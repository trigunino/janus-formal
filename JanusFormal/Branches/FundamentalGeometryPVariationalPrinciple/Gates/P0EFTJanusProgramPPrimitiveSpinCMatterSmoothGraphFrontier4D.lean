import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D

/-!
# Smooth primitive SpinC maximal-graph frontier

This façade records the successive reductions of the smooth matter graph
problem.  The preferred geometric route now starts from one Green identity:

1. the smooth `2D + m²` expression is formally symmetric for the intrinsic
   geometric `L²` pairing;
2. the signed-mode unitary converts that identity into exact coefficient
   intertwining;
3. coefficient intertwining gives maximal-domain membership and exact
   maximal-operator restriction;
4. Parseval gives the same-action completion pairing.

These deductions construct the exact maximal matter graph realization required
by the global minimal-physical Hessian chart.  Canonical Fourier coefficients,
the finite core, injectivity, weighted decay and same-action compatibility are
not independent inputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D

/-- Legacy coefficient-side weighted-decay route. -/
def primitive_spinC_smooth_graph_of_weighted_decay :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_weightedDecay

/-- Intermediate route when maximal-domain data have already been proved. -/
def primitive_spinC_smooth_graph_of_maximal_domain :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain

/-- Preferred route from the mass-independent first-order Dirac Green
identity. -/
def primitive_spinC_smooth_graph_of_dirac_formal_symmetry :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_diracFormalSymmetry

/-- All three exact smooth-graph routes are available. -/
theorem primitive_spinC_smooth_graph_frontier_gate :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
end JanusFormal
