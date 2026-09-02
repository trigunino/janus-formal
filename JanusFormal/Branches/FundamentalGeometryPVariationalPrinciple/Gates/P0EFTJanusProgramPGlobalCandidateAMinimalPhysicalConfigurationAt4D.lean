import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryH10ChartDataReduction4D

/-! # Configuration along the minimal physical tangent -/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Install a supplied admissible geometry and translate every genuine
non-metric field by the corresponding minimal physical tangent component. -/
def globalMinimalPhysicalConfigurationAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (variation : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    GlobalFieldConfiguration period hPeriod where
  geometry := geometry
  coefficientFields :=
    { metrics := (geometry.plusMetric, geometry.minusMetric)
      matter := configuration.coefficientFields.matter
      gauge := configuration.coefficientFields.gauge +
        variation.1.completeVariation.independent.gauge
      ghosts := configuration.coefficientFields.ghosts +
        variation.1.completeVariation.independent.ghosts
      auxiliaries := configuration.coefficientFields.auxiliaries +
        variation.1.completeVariation.independent.auxiliaries
      llAuxMetric := configuration.coefficientFields.llAuxMetric +
        variation.1.completeVariation.independent.llAuxMetric
      llMeasure := configuration.coefficientFields.llMeasure +
        variation.1.completeVariation.independent.llMeasure
      llField := configuration.coefficientFields.llField +
        variation.1.completeVariation.independent.llField }
  metrics_eq := rfl
  legacyMatter_eq_zero := configuration.legacyMatter_eq_zero
  spinCMatter := configuration.spinCMatter + variation.1.2
  d10Completion := configuration.d10Completion

@[simp] theorem globalMinimalPhysicalConfigurationAt_geometry
    (configuration : GlobalFieldConfiguration period hPeriod)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (variation : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalConfigurationAt period hPeriod configuration geometry
      variation).geometry = geometry :=
  rfl

@[simp] theorem globalMinimalPhysicalConfigurationAt_metrics
    (configuration : GlobalFieldConfiguration period hPeriod)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (variation : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalConfigurationAt period hPeriod configuration geometry
      variation).coefficientFields.metrics =
      (geometry.plusMetric, geometry.minusMetric) :=
  rfl

@[simp] theorem globalMinimalPhysicalConfigurationAt_nonmetricFields
    (configuration : GlobalFieldConfiguration period hPeriod)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (variation : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    let result := globalMinimalPhysicalConfigurationAt period hPeriod
      configuration geometry variation
    result.coefficientFields.matter = configuration.coefficientFields.matter ∧
    result.coefficientFields.gauge = configuration.coefficientFields.gauge +
      variation.1.completeVariation.independent.gauge ∧
    result.coefficientFields.ghosts = configuration.coefficientFields.ghosts ∧
    result.coefficientFields.auxiliaries =
      configuration.coefficientFields.auxiliaries ∧
    result.coefficientFields.llAuxMetric =
      configuration.coefficientFields.llAuxMetric +
        variation.1.completeVariation.independent.llAuxMetric ∧
    result.coefficientFields.llMeasure =
      configuration.coefficientFields.llMeasure +
        variation.1.completeVariation.independent.llMeasure ∧
    result.coefficientFields.llField = configuration.coefficientFields.llField +
      variation.1.completeVariation.independent.llField ∧
    result.spinCMatter = configuration.spinCMatter + variation.1.2 ∧
    result.d10Completion = configuration.d10Completion := by
  simp [globalMinimalPhysicalConfigurationAt]

@[simp] theorem globalMinimalPhysicalConfigurationAt_zero
    (configuration : GlobalFieldConfiguration period hPeriod) :
    globalMinimalPhysicalConfigurationAt period hPeriod configuration
      configuration.geometry 0 = configuration := by
  cases configuration with
  | mk geometry fields hMetrics hMatter spin completion =>
      cases fields with
      | mk metrics matter gauge ghosts auxiliaries llAuxMetric llMeasure llField =>
          dsimp at hMetrics
          subst metrics
          simp [globalMinimalPhysicalConfigurationAt,
            GlobalPhysicalFieldTangent.completeVariation]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Gate 325: a supplied admissible geometry determines the corresponding
configuration along every minimal physical direction. -/
theorem global_candidateA_minimal_physical_configurationAt_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (variation : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalConfigurationAt period hPeriod configuration geometry
        variation).geometry = geometry ∧
      (globalMinimalPhysicalConfigurationAt period hPeriod configuration geometry
        variation).coefficientFields.metrics =
          (geometry.plusMetric, geometry.minusMetric) ∧
      globalMinimalPhysicalConfigurationAt period hPeriod configuration
        configuration.geometry 0 = configuration :=
  ⟨rfl, rfl, globalMinimalPhysicalConfigurationAt_zero period hPeriod
    configuration⟩

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
end JanusFormal
