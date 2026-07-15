import Mathlib

namespace JanusFormal.P0EFTJanusCompositeAnomalousLoopOrder

set_option autoImplicit false

/-!
Graph-counting gate for a two-point function with one insertion of the
composite operator `sigma = phi^2` and sextic interaction vertices.
-/

structure CompositeInsertionGraph where
  sexticVertices : ℕ
  insertionVertices : ℕ
  externalLegs : ℕ
  internalLines : ℕ
  loops : ℕ
  halfEdgeCount : 6 * sexticVertices + 2 * insertionVertices =
    2 * internalLines + externalLegs
  connectedLoopCount : loops + sexticVertices + insertionVertices =
    internalLines + 1

/-- One sextic vertex, one `phi^2` insertion and two external legs force three
internal lines and two loops.  This is only a superficial loop-order test. -/
theorem leading_composite_insertion_is_two_loop
    (g : CompositeInsertionGraph)
    (hSix : g.sexticVertices = 1)
    (hInsertion : g.insertionVertices = 1)
    (hExternal : g.externalLegs = 2) :
    g.internalLines = 3 ∧ g.loops = 2 := by
  have hHalf := g.halfEdgeCount
  have hLoop := g.connectedLoopCount
  simp [hSix, hInsertion, hExternal] at hHalf hLoop
  omega

/- Variables resolving the two-vertex topology.  `externalAtInsertion` is the
number of external legs on the composite insertion, `bridgeLines` joins the
insertion to the sextic vertex, and the final two fields count self-loops. -/
structure OneSexticInsertionTopology where
  externalAtInsertion : ℕ
  bridgeLines : ℕ
  insertionSelfLoops : ℕ
  sexticSelfLoops : ℕ
  externalBound : externalAtInsertion ≤ 2
  connected : 0 < bridgeLines
  insertionValence :
    2 = externalAtInsertion + bridgeLines + 2 * insertionSelfLoops
  sexticValence :
    6 = (2 - externalAtInsertion) + bridgeLines + 2 * sexticSelfLoops

/-- Every connected one-sextic contribution to the two-leg `phi^2` insertion
contains a self-loop.  In massless dimensional regularization these scaleless
tadpoles vanish, so no order-`lambda6` MS anomalous dimension follows. -/
theorem one_sextic_composite_insertion_contains_tadpole
    (g : OneSexticInsertionTopology) :
    0 < g.insertionSelfLoops + g.sexticSelfLoops := by
  have hBound := g.externalBound
  have hConnected := g.connected
  have hInsertion := g.insertionValence
  have hSextic := g.sexticValence
  omega

/-- If the first nonzero scalar contribution is
`gamma_sigma = c_sigma * lambda6^2`, it is subleading to the positive
order-`lambda6^2` beta term at sufficiently weak positive coupling. -/
theorem weak_coupling_pure_scalar_stability
    (lambda6 gammaSigma cSigma : ℝ)
    (hLambda : 0 < lambda6)
    (hCoefficient : 0 < cSigma)
    (hWeak : lambda6 < 25 / (6 * Real.pi ^ 2 * cSigma))
    (hGamma : gammaSigma = cSigma * lambda6 ^ 2) :
    3 * gammaSigma * lambda6 <
      (25 / (2 * Real.pi ^ 2)) * lambda6 ^ 2 := by
  rw [hGamma]
  have hPi : 0 < Real.pi := Real.pi_pos
  have hSquare : 0 < lambda6 ^ 2 := sq_pos_of_pos hLambda
  field_simp at hWeak ⊢
  nlinarith

end JanusFormal.P0EFTJanusCompositeAnomalousLoopOrder
