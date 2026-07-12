namespace JanusFormal
namespace P0EFTJanusLLAuxiliaryBundleCompactnessGate

set_option autoImplicit false

/--
A nonzero integral of the LL auxiliary two-form over the closed spatial `S2`
requires more than a globally defined one-form `A` with `F=dA`: it requires
patching data for a nontrivial compact gauge bundle (or an equivalent gerbe
statement) and a normalized integral class.
-/
structure LLAuxiliaryBundleCompactness where
  spatialWorldvolumeS2Defined : Prop
  auxiliaryGaugeFieldDefinedLocally : Prop
  compactU1StructureDerived : Prop
  nontrivialBundlePatchingDerived : Prop
  firstChernClassDefined : Prop
  fluxIntegralityDerived : Prop
  chargeUnitNormalizationDerived : Prop


def nonzeroQuantizedFluxReady
    (s : LLAuxiliaryBundleCompactness) : Prop :=
  s.spatialWorldvolumeS2Defined /\
  s.auxiliaryGaugeFieldDefinedLocally /\
  s.compactU1StructureDerived /\
  s.nontrivialBundlePatchingDerived /\
  s.firstChernClassDefined /\
  s.fluxIntegralityDerived /\
  s.chargeUnitNormalizationDerived


theorem missing_compact_bundle_blocks_primitive_flux
    (s : LLAuxiliaryBundleCompactness)
    (hMissing : Not s.compactU1StructureDerived) :
    Not (nonzeroQuantizedFluxReady s) := by
  intro h
  exact hMissing h.2.2.1


theorem missing_charge_normalization_blocks_absolute_flux_scale
    (s : LLAuxiliaryBundleCompactness)
    (hMissing : Not s.chargeUnitNormalizationDerived) :
    Not (nonzeroQuantizedFluxReady s) := by
  intro h
  exact hMissing h.2.2.2.2.2.2

end P0EFTJanusLLAuxiliaryBundleCompactnessGate
end JanusFormal
