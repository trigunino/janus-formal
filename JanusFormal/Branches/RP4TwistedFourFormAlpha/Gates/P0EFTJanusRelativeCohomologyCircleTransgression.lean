import Mathlib
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusRP4TwistedFluxPrimitiveSelector

namespace JanusFormal
namespace P0EFTJanusRelativeCohomologyCircleTransgression

set_option autoImplicit false

/--
Arithmetic interface for the only degree-compatible direct route presently
visible:

1. a relative bulk degree-four class induces a degree-three boundary class;
2. a compact oriented circle in the Euclideanized world-volume permits fiber
   integration from degree three to degree two;
3. the resulting degree-two class is the auxiliary spatial flux class.

The integer transport is `n_aux = w * n_bulk`, where `w` is the circle winding.
-/
structure CircleFiberTransgression where
  bulkFluxInteger : ℤ
  circleWinding : ℤ
  auxiliaryFluxInteger : ℤ
  relativeBulkClassDerived : Prop
  boundaryThreeClassDerived : Prop
  compactOrientedCircleDerived : Prop
  fiberIntegrationDerived : Prop
  integerTransportLaw :
    auxiliaryFluxInteger = circleWinding * bulkFluxInteger
  primitiveCircleWinding :
    circleWinding = 1 \/ circleWinding = -1

/-- Primitive circle winding preserves the magnitude of the flux integer. -/
theorem primitive_circle_transport_preserves_magnitude
    (t : CircleFiberTransgression) :
    t.auxiliaryFluxInteger.natAbs = t.bulkFluxInteger.natAbs := by
  rcases t.primitiveCircleWinding with hPositive | hNegative
  · rw [t.integerTransportLaw, hPositive]
    simp
  · rw [t.integerTransportLaw, hNegative]
    simp

/-- Primitive bulk flux transports to primitive auxiliary flux. -/
theorem primitive_bulk_flux_transports_to_auxiliary_flux
    (t : CircleFiberTransgression)
    (hBulk : t.bulkFluxInteger.natAbs = 1) :
    t.auxiliaryFluxInteger.natAbs = 1 := by
  rw [primitive_circle_transport_preserves_magnitude t]
  exact hBulk

/--
Interface from the previously proved twisted flux selector to the circle
transgression.
-/
structure SelectedTwistedFluxTransgression where
  selectedBulkSector :
    P0EFTJanusRP4TwistedFluxPrimitiveSelector.TwistedFluxSector
  transgression : CircleFiberTransgression
  sameBulkInteger :
    transgression.bulkFluxInteger = selectedBulkSector.flux

/-- The selected odd minimal sector yields primitive LL auxiliary flux. -/
theorem selected_twisted_flux_yields_primitive_auxiliary_flux
    (t : SelectedTwistedFluxTransgression) :
    t.transgression.auxiliaryFluxInteger.natAbs = 1 := by
  apply primitive_bulk_flux_transports_to_auxiliary_flux t.transgression
  rw [t.sameBulkInteger]
  exact
    P0EFTJanusRP4TwistedFluxPrimitiveSelector.minimal_odd_flux_is_primitive
      t.selectedBulkSector

/--
Lorentzian `R x S2` alone does not provide the compact circle required by this
fiber-integration route.  One must derive a Euclidean thermal/instanton circle,
an internal compact circle, or a different transgression mechanism.
-/
structure CircleExistenceStatus where
  lorentzianWorldvolumeRxS2Tracked : Prop
  euclideanOrInternalCircleDerived : Prop
  circleOrientationDerived : Prop
  primitiveWindingSelected : Prop
  relativeBoundaryMapDerived : Prop
  fiberIntegrationMapDerived : Prop


def circleTransgressionGeometryClosed
    (s : CircleExistenceStatus) : Prop :=
  s.lorentzianWorldvolumeRxS2Tracked /\
  s.euclideanOrInternalCircleDerived /\
  s.circleOrientationDerived /\
  s.primitiveWindingSelected /\
  s.relativeBoundaryMapDerived /\
  s.fiberIntegrationMapDerived


theorem missing_compact_circle_blocks_direct_degree_four_to_two_transport
    (s : CircleExistenceStatus)
    (hMissing : Not s.euclideanOrInternalCircleDerived) :
    Not (circleTransgressionGeometryClosed s) := by
  intro h
  exact hMissing h.2.1

end P0EFTJanusRelativeCohomologyCircleTransgression
end JanusFormal
