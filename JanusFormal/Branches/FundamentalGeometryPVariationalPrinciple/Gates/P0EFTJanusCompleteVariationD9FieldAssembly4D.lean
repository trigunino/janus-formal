import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D

/-!
# D9 field assembled from the complete Program-P variation

This gate constructs the `actionTangentD9Field`-shaped datum occurring in
`RemainingProgramPD7D9D10DomainAgreement4D` directly from a genuine
`ProgramPCompleteVariation4D`.  Every D9 component is read from that same
complete tangent; no remaining agreement contract is assumed.

This does not construct the D10 mode-coordinate equivalence or identify a
Fredholm domain with the Program-P boundary domain.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationD9FieldAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The exact D9 local field carried by one complete Program-P tangent. -/
def completeVariationD9Field
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) : CompleteLocalField Spinor where
  bosonic :=
    { normalMode := variation.normalModeAt period hPeriod sector point
      gaugeOneForm :=
        d9GaugeOneForm period hPeriod variation.independent sector column point
      metricPerturbation :=
        variation.metricPerturbationAt period hPeriod sector point }
  ghosts :=
    { u1Ghost :=
        d9U1Ghost period hPeriod variation.independent sector column point
      diffeomorphismGhost :=
        variation.diffeomorphismGhostAt period hPeriod sector point }
  spinor := matterSpinorIdentification
    (d9MatterCoefficient period hPeriod variation.independent sector point)

@[simp]
theorem completeVariationD9Field_normalMode
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).bosonic.normalMode =
      variation.normalModeAt period hPeriod sector point :=
  rfl

@[simp]
theorem completeVariationD9Field_gaugeOneForm
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).bosonic.gaugeOneForm =
      d9GaugeOneForm period hPeriod variation.independent sector column point :=
  rfl

@[simp]
theorem completeVariationD9Field_metricPerturbation
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).bosonic.metricPerturbation =
      variation.metricPerturbationAt period hPeriod sector point :=
  rfl

@[simp]
theorem completeVariationD9Field_u1Ghost
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).ghosts.u1Ghost =
      d9U1Ghost period hPeriod variation.independent sector column point :=
  rfl

@[simp]
theorem completeVariationD9Field_diffeomorphismGhost
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).ghosts.diffeomorphismGhost =
      variation.diffeomorphismGhostAt period hPeriod sector point :=
  rfl

@[simp]
theorem completeVariationD9Field_spinor
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationD9Field period hPeriod matterSpinorIdentification
      variation sector column point).spinor =
      matterSpinorIdentification
        (d9MatterCoefficient period hPeriod variation.independent sector point) :=
  rfl

end


end P0EFTJanusCompleteVariationD9FieldAssembly4D
end JanusFormal
