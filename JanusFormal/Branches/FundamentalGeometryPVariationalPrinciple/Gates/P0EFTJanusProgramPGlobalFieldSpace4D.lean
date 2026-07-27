import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D

/-!
# Unified global field and tangent space for Program P

The configuration owns one intrinsic Candidate-A geometry, all non-metric
fields, genuine doubled throat SpinC matter and the D10 spectral data.  Boundary
values and D9 fields are derived from this same object.  The tangent is the
existing spinorial complete variation paired with the full D10 Hilbert mode
coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalFieldSpace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPD9MatterSpinorCoefficientMigration4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

/-- One configuration for every present Program-P field sector.

The legacy real matter coefficient is forced to zero.  The two SpinC fields
are the chosen-root and opposite-root halves of one doubled Clifford module.
The equality field prevents the coefficient packet from carrying a second,
unrelated metric pair.
-/
structure GlobalFieldConfiguration where
  geometry : GlobalCandidateAGeometry period hPeriod
  coefficientFields : GeneralLorentzIndependentFields period hPeriod
  metrics_eq :
    coefficientFields.metrics =
      (geometry.plusMetric, geometry.minusMetric)
  legacyMatter_eq_zero : coefficientFields.matter = 0
  normalRootChoice : NormalRootChoice
  spinorialMatter :
    D9SpinorialMatterVariation period hPeriod normalRootChoice
  spinorialMatterOpposite :
    D9SpinorialMatterVariation period hPeriod
      (oppositeRoot normalRootChoice)
  d10Completion : D10SpectralCompletion

/-- Boundary values are outputs of the unique configuration, not new fields. -/
structure GlobalBoundaryData
    (choice : NormalRootChoice) where
  coefficientBoundary :
    GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod
  spinorialMatter : D9SpinorialMatterVariation period hPeriod choice
  spinorialMatterOpposite :
    D9SpinorialMatterVariation period hPeriod (oppositeRoot choice)

def GlobalFieldConfiguration.boundaryTrace
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalBoundaryData period hPeriod configuration.normalRootChoice where
  coefficientBoundary :=
    generalLorentzIndependentBoundaryTraceWithMetric period hPeriod
      configuration.coefficientFields
  spinorialMatter := configuration.spinorialMatter
  spinorialMatterOpposite := configuration.spinorialMatterOpposite

@[simp]
theorem GlobalFieldConfiguration.boundaryTrace_metrics
    (configuration : GlobalFieldConfiguration period hPeriod) :
    (GlobalFieldConfiguration.boundaryTrace period hPeriod
      configuration).coefficientBoundary.metrics =
      (generalLorentzMetricThroatTrace period hPeriod
          configuration.geometry.plusMetric,
        generalLorentzMetricThroatTrace period hPeriod
          configuration.geometry.minusMetric) := by
  rw [GlobalFieldConfiguration.boundaryTrace]
  simp only [generalLorentzIndependentBoundaryTraceWithMetric_metrics,
    configuration.metrics_eq]

@[simp]
theorem GlobalFieldConfiguration.boundaryTrace_spinorialMatter
    (configuration : GlobalFieldConfiguration period hPeriod) :
    (GlobalFieldConfiguration.boundaryTrace period hPeriod
      configuration).spinorialMatter =
      configuration.spinorialMatter :=
  rfl

@[simp]
theorem GlobalFieldConfiguration.boundaryTrace_spinorialMatterOpposite
    (configuration : GlobalFieldConfiguration period hPeriod) :
    (GlobalFieldConfiguration.boundaryTrace period hPeriod
      configuration).spinorialMatterOpposite =
      configuration.spinorialMatterOpposite :=
  rfl

/-- Projection onto the obsolete diagonal metric tangent. -/
def spinorialLegacyMetricProjection
    (choice : NormalRootChoice) :
    SpinorialCompleteVariation period hPeriod choice →ₗ[Real]
      SmoothDiagonalMetricVariation period hPeriod where
  toFun variation := variation.legacy.independent.metrics
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Spinorial tangent with the obsolete diagonal metric direction removed.
The unique metric variation is now `fullMetricPerturbation`. -/
abbrev GeneralMetricSpinorialVariation (choice : NormalRootChoice) :=
  LinearMap.ker (spinorialLegacyMetricProjection period hPeriod choice)

/-- The single complete tangent: all smooth geometric/BV/BRST slots, both
halves of the doubled spinorial matter module, and multiplicity-aware D10
Hilbert coordinates. -/
abbrev GlobalFieldTangent
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  GeneralMetricSpinorialVariation period hPeriod
      configuration.normalRootChoice ×
    (D9SpinorialMatterVariation period hPeriod
        (oppositeRoot configuration.normalRootChoice) ×
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion))

def GlobalFieldTangent.completeVariation
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    SpinorialCompleteVariation period hPeriod
      configuration.normalRootChoice :=
  variation.1.1

@[simp]
theorem GlobalFieldTangent.legacyMetric_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    variation.completeVariation.legacy.independent.metrics = 0 :=
  variation.1.2

def GlobalFieldTangent.d10Coordinates
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion) :=
  variation.2.2

/-- Tangent in the opposite-root half of the doubled SpinC module. -/
def GlobalFieldTangent.oppositeSpinorialMatter
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    D9SpinorialMatterVariation period hPeriod
      (oppositeRoot configuration.normalRootChoice) :=
  variation.2.1

/-- D9 is a projection of the same global tangent, including true spinors. -/
def GlobalFieldTangent.d9Field
    {configuration : GlobalFieldConfiguration period hPeriod}
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : GlobalFieldTangent period hPeriod configuration)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) : CompleteLocalField Spinor :=
  spinorialCompleteVariationD9Field period hPeriod
    configuration.normalRootChoice matterSpinorIdentification variation.1.1
    sector column anchor

@[simp]
theorem GlobalFieldTangent.d9Field_spinor
    {configuration : GlobalFieldConfiguration period hPeriod}
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : GlobalFieldTangent period hPeriod configuration)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod) :
    (GlobalFieldTangent.d9Field period hPeriod matterSpinorIdentification
      variation sector column anchor).spinor =
      matterSpinorIdentification
        (d9SpinorialMatterCoefficient period hPeriod
          configuration.normalRootChoice variation.1.1.matter sector anchor) :=
  rfl

/-- Canonical zero configuration over any admissible global geometry. -/
def zeroGlobalFieldConfiguration
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    GlobalFieldConfiguration period hPeriod where
  geometry := geometry
  coefficientFields :=
    { metrics := (geometry.plusMetric, geometry.minusMetric)
      matter := 0
      gauge := 0
      ghosts := 0
      auxiliaries := 0
      llAuxMetric := 0
      llMeasure := constantSmoothThroatField period hPeriod Real 1
      llField := 0 }
  metrics_eq := rfl
  legacyMatter_eq_zero := rfl
  normalRootChoice := .positiveQuarter
  spinorialMatter := 0
  spinorialMatterOpposite := 0
  d10Completion :=
    { sphereRadius := 1
      sphereRadiusPositive := by norm_num
      monopoleCharge := 0 }

theorem globalFieldConfiguration_nonempty
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    Nonempty (GlobalFieldConfiguration period hPeriod) :=
  ⟨zeroGlobalFieldConfiguration period hPeriod geometry⟩

theorem globalFieldTangent_nonempty
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Nonempty (GlobalFieldTangent period hPeriod configuration) :=
  ⟨0⟩

end
end P0EFTJanusProgramPGlobalFieldSpace4D
end JanusFormal
