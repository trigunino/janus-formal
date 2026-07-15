import Mathlib

namespace JanusFormal.P0EFTJanusSexticLoopOrder

set_option autoImplicit false

/-- Combinatorial data for a connected scalar graph built only from sextic
vertices: `6V = 2I + E` and `L = I - V + 1`. -/
structure SexticGraphCount where
  vertices : ℤ
  internalEdges : ℤ
  externalEdges : ℤ
  loops : ℤ
  halfEdgeCount : 6 * vertices = 2 * internalEdges + externalEdges
  connectedLoopCount : loops = internalEdges - vertices + 1

/-- The first six-point graph quadratic in `lambda6` has two loops. -/
theorem two_sextic_vertices_six_point_is_two_loop
    (g : SexticGraphCount)
    (hVertices : g.vertices = 2)
    (hExternal : g.externalEdges = 6) :
    g.internalEdges = 3 ∧ g.loops = 2 := by
  have hHalf := g.halfEdgeCount
  have hLoop := g.connectedLoopCount
  constructor <;> omega

/-- A single sextic vertex with six external legs is the tree vertex, not a
one-loop renormalization of its own coupling. -/
theorem one_sextic_vertex_six_point_is_tree
    (g : SexticGraphCount)
    (hVertices : g.vertices = 1)
    (hExternal : g.externalEdges = 6) :
    g.internalEdges = 0 ∧ g.loops = 0 := by
  have hHalf := g.halfEdgeCount
  have hLoop := g.connectedLoopCount
  constructor <;> omega

/-- This counting only fixes the pure-sextic `lambda6^2` contribution. Gauge,
LL and mixed diagrams must be counted from their own derived vertices. -/
structure SexticBetaLoopCoverageStatus where
  pureSexticTwoLoopGraphsIncluded : Prop
  gaugeOneLoopGraphsIncluded : Prop
  mixedGaugeScalarGraphsIncluded : Prop
  llMeasureGraphsIncluded : Prop
  countertermInsertionsIncluded : Prop

def sexticBetaLoopCoverageClosed
    (s : SexticBetaLoopCoverageStatus) : Prop :=
  s.pureSexticTwoLoopGraphsIncluded ∧
  s.gaugeOneLoopGraphsIncluded ∧
  s.mixedGaugeScalarGraphsIncluded ∧
  s.llMeasureGraphsIncluded ∧
  s.countertermInsertionsIncluded

end JanusFormal.P0EFTJanusSexticLoopOrder
