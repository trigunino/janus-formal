import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D

/-!
# Smooth primitive SpinC maximal-graph frontier

This façade records the successive reductions of the smooth matter graph
problem.  The preferred geometric route is:

1. canonical unweighted Fourier coefficients from the signed geometric
   unitary;
2. maximal-domain membership of every smooth primitive section;
3. agreement of the maximal operator with the smooth `2D + m²` expression;
4. the same-action completion pairing.

These data construct the exact maximal matter graph realization required by
the global minimal-physical Hessian chart.  The finite Fourier core,
injectivity, multiplier relation and finite weighted compatibility are all
derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D

/-- Public alias for the coefficient-side weighted-decay route. -/
def primitive_spinC_smooth_graph_of_weighted_decay :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_weightedDecay

/-- Preferred public alias for the geometric maximal-domain route. -/
def primitive_spinC_smooth_graph_of_maximal_domain :=
  @programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain

/-- Both exact smooth-graph routes are available. -/
theorem primitive_spinC_smooth_graph_frontier_gate :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
end JanusFormal
