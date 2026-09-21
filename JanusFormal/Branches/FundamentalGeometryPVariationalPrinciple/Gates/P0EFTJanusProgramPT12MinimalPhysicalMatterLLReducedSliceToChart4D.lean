import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D

/-!
# Matter--LL slice in the minimal physical reduced chart

The finite matter packet and the reduced smooth LL field define a canonical
slice of the diagonal smooth core by setting every other coordinate, including
the auxiliary/measure LL coordinates, to zero.  The corrected minimal tangent
recovers both coordinates, so this slice survives the physical kernel quotient
and embeds injectively in the minimal local chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

/-- Finite matter coefficients paired with a reduced smooth LL direction. -/
abbrev ProgramPT12MinimalPhysicalMatterLLReducedSlice :=
  ProgramPGlobalGaugeFixedMatterLLSmoothSlice period hPeriod analysis

/-- Insert the matter--LL slice in the diagonal core, with zero gauge,
diffeomorphism and auxiliary/measure coordinates. -/
def programPT12MinimalPhysicalMatterLLReducedSliceCore :
    ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
      configuration analysis
      →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis where
  toFun direction := (0, (0, (direction.1, (0, direction.2))))
  map_add' first second := by
    simp
  map_smul' scalar direction := by
    simp

@[simp]
theorem programPT12MinimalPhysicalMatterLLReducedSliceCore_matter
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    (programPT12MinimalPhysicalMatterLLReducedSliceCore
      period hPeriod configuration analysis direction).2.2.1 = direction.1 :=
  rfl

@[simp]
theorem programPT12MinimalPhysicalMatterLLReducedSliceCore_fullLL
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    (programPT12MinimalPhysicalMatterLLReducedSliceCore
      period hPeriod configuration analysis direction).2.2.2 =
      ((0, direction.2) : GlobalFullLLSmooth period hPeriod analysis) :=
  rfl

/-- The corrected minimal tangent recovers the finite matter coordinate. -/
theorem programPT12MinimalPhysicalMatterLLReducedSlice_tangent_matter
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis direction)).1.2 =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        direction.1 := by
  simpa only [programPT12MinimalPhysicalMatterLLReducedSliceCore_matter] using
    diagonalExtendedBulkMinimalPhysicalTangent_matter period hPeriod
      configuration data analysis
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis direction)

/-- The corrected minimal tangent recovers the reduced LL coordinate, with
zero auxiliary/measure component. -/
theorem programPT12MinimalPhysicalMatterLLReducedSlice_tangent_fullLL
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis
            (programPT12MinimalPhysicalMatterLLReducedSliceCore
              period hPeriod configuration analysis direction)) =
      ((0, direction.2) : GlobalFullLLSmooth period hPeriod analysis) := by
  simpa only [programPT12MinimalPhysicalMatterLLReducedSliceCore_fullLL] using
    diagonalExtendedBulkMinimalPhysicalTangent_fullLL period hPeriod
      configuration data analysis
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis direction)

/-- Quotient the slice by the exact kernel of the corrected minimal physical
tangent. -/
def programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore :
    ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
      configuration analysis
      →ₗ[Real]
    GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
      configuration data analysis :=
  (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
      configuration data analysis).mkQ.comp
    (programPT12MinimalPhysicalMatterLLReducedSliceCore
      period hPeriod configuration analysis)

@[simp]
theorem programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore_mk
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore period hPeriod
        configuration data analysis direction =
      Submodule.Quotient.mk
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis direction) :=
  rfl

/-- No matter or reduced LL coordinate is lost in the minimal physical
quotient. -/
theorem programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore_injective :
    Function.Injective
      (programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore period
        hPeriod configuration data analysis) := by
  intro first second hEqual
  change
    Submodule.Quotient.mk
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis first) =
      Submodule.Quotient.mk
        (programPT12MinimalPhysicalMatterLLReducedSliceCore
          period hPeriod configuration analysis second) at hEqual
  have hKernel :
      programPT12MinimalPhysicalMatterLLReducedSliceCore
            period hPeriod configuration analysis first -
          programPT12MinimalPhysicalMatterLLReducedSliceCore
            period hPeriod configuration analysis second ∈
        globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
          configuration data analysis :=
    (Submodule.Quotient.eq
      (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis)).mp hEqual
  have hZero :
      diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore
                period hPeriod configuration analysis first -
            programPT12MinimalPhysicalMatterLLReducedSliceCore
              period hPeriod configuration analysis second) = 0 :=
    LinearMap.mem_ker.mp hKernel
  have hTangent :
      diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore
            period hPeriod configuration analysis first) =
        diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore
            period hPeriod configuration analysis second) := by
    rw [map_sub, sub_eq_zero] at hZero
    exact hZero
  apply Prod.ext
  · apply programPPrimitiveSpinCMatterSmoothFiniteSynthesis_injective
      period hPeriod
    have hMatter := congrArg (fun tangent => tangent.1.2) hTangent
    simpa only [programPT12MinimalPhysicalMatterLLReducedSlice_tangent_matter]
      using hMatter
  · have hLL := congrArg
        (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod
          configuration analysis) hTangent
    simpa only [programPT12MinimalPhysicalMatterLLReducedSlice_tangent_fullLL]
      using congrArg
        (fun value : GlobalFullLLSmooth period hPeriod analysis => value.2) hLL

/-- The matter--LL slice mapped into the concrete minimal local chart. -/
def programPT12MinimalPhysicalMatterLLReducedSliceToChart :
    ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
      configuration analysis
      →ₗ[Real]
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
      configuration data analysis chartData).comp
    (programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore period hPeriod
      configuration data analysis)

@[simp]
theorem programPT12MinimalPhysicalMatterLLReducedSliceToChart_mk
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice
      period hPeriod configuration analysis) :
    programPT12MinimalPhysicalMatterLLReducedSliceToChart period hPeriod
        configuration data analysis chartData direction =
      globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData
        (Submodule.Quotient.mk
          (programPT12MinimalPhysicalMatterLLReducedSliceCore
            period hPeriod configuration analysis direction)) :=
  rfl

/-- The concrete minimal local chart sees the full matter--LL slice
faithfully. -/
theorem programPT12MinimalPhysicalMatterLLReducedSliceToChart_injective :
    Function.Injective
      (programPT12MinimalPhysicalMatterLLReducedSliceToChart period hPeriod
        configuration data analysis chartData) :=
  (globalCandidateAMinimalPhysicalReducedCoreToChart_injective period hPeriod
    configuration data analysis chartData).comp
      (programPT12MinimalPhysicalMatterLLReducedSliceToReducedCore_injective
        period hPeriod configuration data analysis)

end
end
end P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
end JanusFormal
