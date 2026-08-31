import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D

/-!
# Candidate-A natural graph Riesz identification

Any bounded Riesz realization on the existing Candidate-A graph Hilbert space
is uniquely determined by its pairing on the dense typed smooth core.  Thus a
natural elliptic realization agrees with the faithful augmented Hessian once
its genuine differential pairing is identified on that core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANaturalGraphRieszIdentification4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000
set_option maxRecDepth 3000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalHessianClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Two continuous endomorphisms with equal pairings on a dense family are
equal. -/
private theorem continuousLinearMap_eq_of_dense_inner_pairing
    {𝕜 E Core : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    (embedding : Core → E)
    (hDense : DenseRange embedding)
    (first second : E →L[𝕜] E)
    (hPair : ∀ x y,
      inner 𝕜 (first (embedding x)) (embedding y) =
        inner 𝕜 (second (embedding x)) (embedding y)) :
    first = second := by
  have hCore : ∀ core,
      first (embedding core) = second (embedding core) := by
    intro core
    exact hDense.eq_of_inner_left 𝕜 (hPair core)
  apply ContinuousLinearMap.ext
  intro value
  have hFunctions :
      (fun input => first input) = fun input => second input :=
    hDense.equalizer first.continuous second.continuous (by
      funext core
      exact hCore core)
  exact congrFun hFunctions value

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev NaturalGraphHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) naturalGraphNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (NaturalGraphHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) naturalGraphInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (NaturalGraphHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) naturalGraphNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (NaturalGraphHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) naturalGraphModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (NaturalGraphHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- A bounded natural graph Riesz realization that has the genuine
Candidate-A Hessian pairing on the typed smooth core. -/
structure GlobalCandidateANaturalGraphRieszRealization4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart) where
  operator :
    NaturalGraphHilbert period hPeriod configuration data analysis →L[Real]
      NaturalGraphHilbert period hPeriod configuration data analysis
  core_pairing : ∀ first second :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis,
    inner Real
        (operator
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second

/-- Dense-core pairing agreement identifies the natural graph Riesz operator
with the faithful augmented Candidate-A Hessian. -/
theorem GlobalCandidateANaturalGraphRieszRealization4D.operator_eq_candidateA
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (natural : GlobalCandidateANaturalGraphRieszRealization4D period hPeriod
      configuration data analysis chart sameAction) :
    natural.operator =
      globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical := by
  let embedding :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
        →ₗ[Real]
      NaturalGraphHilbert period hPeriod configuration data analysis :=
    diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  have hDense : DenseRange embedding :=
    diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  apply @continuousLinearMap_eq_of_dense_inner_pairing Real
    (NaturalGraphHilbert period hPeriod configuration data analysis) _
    inferInstance
    (naturalGraphNormedAddCommGroup period hPeriod configuration data analysis)
    (naturalGraphInnerProductSpace period hPeriod configuration data analysis)
    embedding hDense natural.operator
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical)
  intro core test
  exact (natural.core_pairing core test).trans
    (globalCandidateAFaithfulAugmentedRieszOperator_smooth_pairing period
      hPeriod configuration data analysis chart sameAction physical core
        test).symm

/-- The natural graph realization inherits the complete Fredholm triple:
closed range, finite kernel and finite cokernel. -/
theorem GlobalCandidateANaturalGraphRieszRealization4D.fredholm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {einsteinScale : Real}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical}
    (certificate : GlobalCandidateAHessianClosureCertificate4D period hPeriod
      configuration data analysis chart einsteinScale sameAction physical
        estimates)
    (natural : GlobalCandidateANaturalGraphRieszRealization4D period hPeriod
      configuration data analysis chart sameAction) :
    IsClosed
        (natural.operator.range :
          Set (NaturalGraphHilbert period hPeriod configuration data analysis)) ∧
      FiniteDimensional Real natural.operator.ker ∧
      FiniteDimensional Real
        ((NaturalGraphHilbert period hPeriod configuration data analysis) ⧸
          natural.operator.range) := by
  rw [natural.operator_eq_candidateA period hPeriod physical]
  exact certificate.faithful_fredholm_h12.fredholm

/-- The natural graph realization inherits index zero from any terminal
Candidate-A Hessian closure certificate. -/
theorem GlobalCandidateANaturalGraphRieszRealization4D.index_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {einsteinScale : Real}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical}
    (certificate : GlobalCandidateAHessianClosureCertificate4D period hPeriod
      configuration data analysis chart einsteinScale sameAction physical
        estimates)
    (natural : GlobalCandidateANaturalGraphRieszRealization4D period hPeriod
      configuration data analysis chart sameAction) :
    natural.operator.toLinearMap.index = 0 := by
  rw [natural.operator_eq_candidateA period hPeriod physical]
  exact certificate.index_zero

end
end P0EFTJanusProgramPGlobalCandidateANaturalGraphRieszIdentification4D
end JanusFormal
