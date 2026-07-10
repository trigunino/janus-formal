namespace JanusFormal
namespace P0EFTJanusBulkWorldvolumeFluxSeparation

set_option autoImplicit false

/--
The bulk orientation-twisted four-form and the auxiliary LL-brane two-form are
mathematically distinct fields.

* The bulk object is the field strength of a three-form potential and couples
  electrically to the three-dimensional LL world-volume.
* The auxiliary object is a two-form intrinsic to the world-volume and enters
  the lightlike constraints.

An equality of their integer sectors is therefore an additional transgression
or anomaly-inflow theorem, not a consequence of degree counting alone.
-/
structure FluxSeparationAudit where
  bulkTwistedFourFormDefined : Prop
  bulkThreeFormPotentialDefined : Prop
  bulkKalbRamondChargeDefined : Prop
  worldvolumeAuxiliaryTwoFormDefined : Prop
  worldvolumeAuxiliaryFluxCycleDefined : Prop
  bulkAndAuxiliaryFieldsDistinguished : Prop
  transgressionMapDerived : Prop
  integerSectorCompatibilityDerived : Prop


def fieldContentAudited (s : FluxSeparationAudit) : Prop :=
  s.bulkTwistedFourFormDefined /\
  s.bulkThreeFormPotentialDefined /\
  s.bulkKalbRamondChargeDefined /\
  s.worldvolumeAuxiliaryTwoFormDefined /\
  s.worldvolumeAuxiliaryFluxCycleDefined /\
  s.bulkAndAuxiliaryFieldsDistinguished


def bulkToWorldvolumeFluxClosed (s : FluxSeparationAudit) : Prop :=
  fieldContentAudited s /\
  s.transgressionMapDerived /\
  s.integerSectorCompatibilityDerived


theorem missing_transgression_blocks_flux_identification
    (s : FluxSeparationAudit)
    (hMissing : Not s.transgressionMapDerived) :
    Not (bulkToWorldvolumeFluxClosed s) := by
  intro h
  exact hMissing h.2.1

/--
A direct identification of the bulk primitive integer with the LL auxiliary
integer may only be used downstream through an explicit compatibility witness.
-/
structure ExplicitFluxIntegerTransport where
  bulkFluxInteger : Int
  auxiliaryFluxInteger : Int
  transportDerived : Prop
  transportedIntegerEquality : auxiliaryFluxInteger = bulkFluxInteger

end P0EFTJanusBulkWorldvolumeFluxSeparation
end JanusFormal
