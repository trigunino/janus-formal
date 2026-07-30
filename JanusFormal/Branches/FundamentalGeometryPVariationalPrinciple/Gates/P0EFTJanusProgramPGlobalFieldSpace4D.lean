import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinorialCompleteVariationD9FieldAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

/-!
# Unified global field and tangent space for Program P

The configuration owns one intrinsic Candidate-A geometry, all non-metric
fields, two genuine primitive monopole SpinC sections and the D10 spectral
background data.  D10 is not an action-field direction.  The physical tangent
therefore excludes it, while a compatibility extension retains its Hilbert
coordinates for regulator constructions.
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
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
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

The legacy real matter coefficient is forced to zero.  Matter is represented
directly by two sections of the primitive monopole SpinC bundle used by the
signed Dirac operator.  Normal-root labels belong to its spectral modes and
are not duplicated as configuration data.  The equality field prevents the
coefficient packet from carrying a second, unrelated metric pair.
-/
structure GlobalFieldConfiguration where
  geometry : GlobalCandidateAGeometry period hPeriod
  coefficientFields : GeneralLorentzIndependentFields period hPeriod
  metrics_eq :
    coefficientFields.metrics =
      (geometry.plusMetric, geometry.minusMetric)
  legacyMatter_eq_zero : coefficientFields.matter = 0
  spinCMatter :
    Sector →
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter
  d10Completion : D10SpectralCompletion

/-- Boundary values are outputs of the unique configuration, not new fields. -/
structure GlobalBoundaryData where
  coefficientBoundary :
    GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod
  spinCMatter :
    Sector →
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter

def GlobalFieldConfiguration.boundaryTrace
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalBoundaryData period hPeriod where
  coefficientBoundary :=
    generalLorentzIndependentBoundaryTraceWithMetric period hPeriod
      configuration.coefficientFields
  spinCMatter := configuration.spinCMatter

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
theorem GlobalFieldConfiguration.boundaryTrace_spinCMatter
    (configuration : GlobalFieldConfiguration period hPeriod) :
    (GlobalFieldConfiguration.boundaryTrace period hPeriod
      configuration).spinCMatter =
      configuration.spinCMatter :=
  rfl

/-- Projection onto the obsolete diagonal metric tangent. -/
def matterFreeLegacyMetricProjection :
    MatterFreeCompleteVariation period hPeriod →ₗ[Real]
      SmoothDiagonalMetricVariation period hPeriod where
  toFun variation := variation.1.independent.metrics
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Matter-free tangent with the obsolete diagonal metric direction removed.
The unique metric variation is now `fullMetricPerturbation`. -/
abbrev GeneralMetricMatterFreeVariation :=
  LinearMap.ker (matterFreeLegacyMetricProjection period hPeriod)

/-- The physical tangent: all currently installed smooth geometric and legacy
gauge/auxiliary slots plus the two primitive monopole SpinC matter sectors,
with no D10 field direction.  The separately typed nonminimal extension is
installed by `P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D`. -/
abbrev GlobalPhysicalFieldTangent
    (_configuration : GlobalFieldConfiguration period hPeriod) :=
  GeneralMetricMatterFreeVariation period hPeriod ×
    (Sector →
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter)

/-- The extended tangent retains the multiplicity-aware D10 Hilbert
coordinate used by the spectral and regulator packages. -/
abbrev GlobalExtendedFieldTangent
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  GeneralMetricMatterFreeVariation period hPeriod ×
    ((Sector →
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) ×
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion))

/-- Legacy compatibility alias for the former D10-extended tangent. -/
abbrev GlobalFieldTangent :=
  GlobalExtendedFieldTangent period hPeriod

/-- Underlying complete geometric variation of a D10-free physical tangent. -/
def GlobalPhysicalFieldTangent.completeVariation
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation :
      GlobalPhysicalFieldTangent period hPeriod configuration) :
    ProgramPCompleteVariation4D period hPeriod :=
  variation.1.1.1

/-- Genuine normal-line displacement already present in the physical
tangent, before any chart-to-action identification. -/
def GlobalPhysicalFieldTangent.normalDisplacement
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation :
      GlobalPhysicalFieldTangent period hPeriod configuration) :=
  variation.completeVariation.normalDisplacement

/-- Forget the D10 coordinate of the legacy extended tangent. -/
def globalFieldTangentPhysicalProjectionLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod} :
    GlobalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration where
  toFun := fun variation => (variation.1, variation.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Include a physical tangent with zero D10 coordinate. -/
def globalPhysicalFieldTangentZeroD10InclusionLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod} :
    GlobalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration where
  toFun := fun variation => (variation.1, (variation.2, 0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem globalFieldTangentPhysicalProjection_zeroD10Inclusion
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalPhysicalFieldTangent period hPeriod configuration) :
    globalFieldTangentPhysicalProjectionLinearMap period hPeriod
        (globalPhysicalFieldTangentZeroD10InclusionLinearMap
          period hPeriod variation) =
      variation :=
  rfl

theorem globalFieldTangentPhysicalProjection_surjective
    {configuration : GlobalFieldConfiguration period hPeriod} :
    Function.Surjective
      (globalFieldTangentPhysicalProjectionLinearMap
        period hPeriod (configuration := configuration)) := by
  intro variation
  exact
    ⟨globalPhysicalFieldTangentZeroD10InclusionLinearMap
        period hPeriod variation, by simp⟩

theorem globalPhysicalFieldTangentZeroD10Inclusion_injective
    {configuration : GlobalFieldConfiguration period hPeriod} :
    Function.Injective
      (globalPhysicalFieldTangentZeroD10InclusionLinearMap
        period hPeriod (configuration := configuration)) := by
  intro first second h
  have hProjection :=
    congrArg
      (globalFieldTangentPhysicalProjectionLinearMap
        period hPeriod (configuration := configuration)) h
  simpa using hProjection

def GlobalFieldTangent.completeVariation
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    ProgramPCompleteVariation4D period hPeriod :=
  variation.1.1.1

@[simp]
theorem GlobalFieldTangent.legacyMetric_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    variation.completeVariation.independent.metrics = 0 :=
  variation.1.2

def GlobalFieldTangent.d10Coordinates
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion) :=
  variation.2.2

/-- Primitive SpinC matter tangent in one physical outer sector. -/
def GlobalFieldTangent.spinCMatter
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    Sector →
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter :=
  variation.2.1

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
  spinCMatter := 0
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
