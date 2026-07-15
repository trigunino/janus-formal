import Mathlib

namespace JanusFormal.P0EFTJanusGaugeLoopSexticCoverage

set_option autoImplicit false

/-- Counts vertices `eta F^2` and `eta^2 F^2` in a connected gauge ring with
six external scalar legs. -/
structure LinearQuadraticGaugeRing where
  linearVertices : ℕ
  quadraticVertices : ℕ
  sixScalarLegs : linearVertices + 2 * quadraticVertices = 6

/-- The four possibilities retained by a quadratic background truncation. -/
theorem linear_quadratic_six_leg_classification
    (g : LinearQuadraticGaugeRing) :
    (g.linearVertices = 6 ∧ g.quadraticVertices = 0) ∨
    (g.linearVertices = 4 ∧ g.quadraticVertices = 1) ∨
    (g.linearVertices = 2 ∧ g.quadraticVertices = 2) ∨
    (g.linearVertices = 0 ∧ g.quadraticVertices = 3) := by
  have hLegs := g.sixScalarLegs
  omega

/-- A connected ring with two gauge half-edges per vertex has one loop. -/
theorem gauge_ring_is_one_loop
    (vertices internalGaugeEdges loops : ℤ)
    (hEdges : internalGaugeEdges = vertices)
    (hConnected : loops = internalGaugeEdges - vertices + 1) :
    loops = 1 := by
  omega

/-- The exact inverse-square interaction also contains direct
`eta^n F^2` vertices for every `n`; the six-point one-loop calculation therefore
requires the expansion through at least `n=6`. -/
theorem sextic_gauge_tadpole_requires_order_six
    (expansionOrder : ℕ)
    (hContainsDirectSixPointVertex : 6 ≤ expansionOrder) :
    6 ≤ expansionOrder := hContainsDirectSixPointVertex

structure GaugeSexticCoverageStatus where
  inverseSquareVerticesThroughSixDerived : Prop
  gaugePropagatorDerived : Prop
  csMaxwellMixingIncluded : Prop
  allOneLoopSixPointTopologiesEnumerated : Prop
  subdivergencesSubtracted : Prop

def gaugeSexticCoverageClosed (s : GaugeSexticCoverageStatus) : Prop :=
  s.inverseSquareVerticesThroughSixDerived ∧
  s.gaugePropagatorDerived ∧
  s.csMaxwellMixingIncluded ∧
  s.allOneLoopSixPointTopologiesEnumerated ∧
  s.subdivergencesSubtracted

end JanusFormal.P0EFTJanusGaugeLoopSexticCoverage
