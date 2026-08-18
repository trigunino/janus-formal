import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D

/-!
# Local Candidate-A chart on the D10-free minimal physical tangent

The H13 quadratic-chart bridge can be made substantially more concrete by
choosing its model to be the corrected minimal physical tangent itself.  The
chart-core map is then the identity, hence automatically injective and dense.
Only the genuine analytic data remain: an open local action family, continuous
matter and LL graph projections, and the two exact action identities.

This construction does not identify an arbitrary smooth matter section with a
maximal graph vector by fiat.  That bounded graph projection remains an
explicit field of the analytic chart data.  Likewise the LL projection must be
the existing full three-slot graph realization on the diagonal core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

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

private abbrev MinimalPhysicalModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- Algebraic projection to the genuine two-sector primitive SpinC smooth
matter direction. -/
def globalMinimalPhysicalSpinCMatterLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    MinimalPhysicalModel period hPeriod configuration →ₗ[Real]
      ProgramPPrimitiveSpinCMatterSmoothField period hPeriod where
  toFun direction := direction.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Algebraic projection to the three smooth LL slots selected by the current
positive H1 datum.  Every smooth LL test defines an `LLH1Smooth` vector. -/
def globalMinimalPhysicalFullLLSmoothLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    MinimalPhysicalModel period hPeriod configuration →ₗ[Real]
      GlobalFullLLSmooth period hPeriod analysis where
  toFun direction :=
    ((direction.1.completeVariation.independent.llAuxMetric,
        direction.1.completeVariation.independent.llMeasure),
      LLH1Smooth.ofTest period hPeriod (analysis.llH1Data period hPeriod)
        direction.1.completeVariation.independent.llField)
  map_add' first second := by
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply LLH1Smooth.ext
      rfl
  map_smul' scalar direction := by
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply LLH1Smooth.ext
      rfl

/-- Concrete chart data on the exact corrected physical tangent.  The two
continuous graph projections are the only analytic maps not determined by the
field-space definitions. -/
structure ProgramPGlobalMinimalPhysicalActionChartData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  [normedAddCommGroup :
    NormedAddCommGroup (MinimalPhysicalModel period hPeriod configuration)]
  [normedSpace :
    NormedSpace Real (MinimalPhysicalModel period hPeriod configuration)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (MinimalPhysicalModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (MinimalPhysicalModel period hPeriod configuration)
  domain : Set (MinimalPhysicalModel period hPeriod configuration)
  isOpen_domain : IsOpen domain
  zero_mem_domain :
    letI := normedAddCommGroup
    (0 : MinimalPhysicalModel period hPeriod configuration) ∈ domain
  datumAt : ∀ point : MinimalPhysicalModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    letI := normedAddCommGroup
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  blocksC2Within : ∀ point (hPoint : point ∈ domain),
    letI := normedAddCommGroup
    letI := normedSpace
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (MinimalPhysicalModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    FullCoupledC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point
  matterProjection :
    letI := normedAddCommGroup
    letI := normedSpace
    MinimalPhysicalModel period hPeriod configuration →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared
  llProjection :
    letI := normedAddCommGroup
    letI := normedSpace
    MinimalPhysicalModel period hPeriod configuration →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    letI := normedAddCommGroup
    letI := normedSpace
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (MinimalPhysicalModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared (matterProjection state)
  llAction_eq :
    letI := normedAddCommGroup
    letI := normedSpace
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (MinimalPhysicalModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (llProjection state)
  matterProjection_diagonalCore :
    letI := normedAddCommGroup
    letI := normedSpace
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      matterProjection
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core) =
        programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          couplings.matterMassSquared core.2.2.1
  llProjection_diagonalCore :
    letI := normedAddCommGroup
    letI := normedSpace
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      llProjection
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core) =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          core.2.2.2

/-- The local action family on the minimal physical tangent. -/
def globalCandidateAMinimalPhysicalLocalActionFamily
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateALocalActionFamily period hPeriod
      (MinimalPhysicalModel period hPeriod configuration) couplings
        NonNullFace NullFace where
  domain := chartData.domain
  datumAt := chartData.datumAt

/-- The genuine local chart whose ambient model is exactly the corrected
D10-free physical tangent. -/
def globalCandidateAMinimalPhysicalLocalVariationalChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure := by
  letI : NormedAddCommGroup
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedAddCommGroup
  letI : NormedSpace Real
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedSpace
  have hZero :
      @Zero.zero _ chartData.normedAddCommGroup.toAddCommGroup.toZero =
        @Zero.zero _
          (Submodule.addCommGroup
            (MinimalPhysicalModel period hPeriod configuration)).toZero :=
    congrArg
      (fun group : AddCommGroup
          (MinimalPhysicalModel period hPeriod configuration) =>
        @Zero.zero _ group.toZero)
      chartData.toAddCommGroup_eq
  refine
    { Model := MinimalPhysicalModel period hPeriod configuration
      normedAddCommGroup := chartData.normedAddCommGroup
      normedSpace := chartData.normedSpace
      family := globalCandidateAMinimalPhysicalLocalActionFamily period hPeriod
        configuration data analysis chartData
      isOpen_domain := chartData.isOpen_domain
      zero_mem_domain := ?_
      blocksC2Within := ?_ }
  · change
      @Zero.zero _ chartData.normedAddCommGroup.toAddCommGroup.toZero ∈
        chartData.domain
    exact hZero.symm ▸ chartData.zero_mem_domain
  · intro point hPoint
    change point ∈ chartData.domain at hPoint
    convert chartData.blocksC2Within point hPoint using 1
    · congr 1
      simp only [globalCandidateAMinimalPhysicalLocalActionFamily]
      congr
      exact congrArg
        (fun group : AddCommGroup
            (MinimalPhysicalModel period hPeriod configuration) => group.toZero)
        chartData.toAddCommGroup_eq
    · rfl

/-- Identity dense-core bridge for the minimal physical chart. -/
def globalCandidateAMinimalPhysicalLocalChartBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D period hPeriod
      configuration.physical
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) := by
  letI : NormedAddCommGroup
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedAddCommGroup
  letI : NormedSpace Real
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedSpace
  have hZero :
      @Zero.zero _ chartData.normedAddCommGroup.toAddCommGroup.toZero =
        @Zero.zero _
          (Submodule.addCommGroup
            (MinimalPhysicalModel period hPeriod configuration)).toZero :=
    congrArg
      (fun group : AddCommGroup
          (MinimalPhysicalModel period hPeriod configuration) =>
        @Zero.zero _ group.toZero)
      chartData.toAddCommGroup_eq
  refine
    { basePoint := (0 : MinimalPhysicalModel period hPeriod configuration)
      basePoint_mem := ?_
      baseConfiguration_fields := ?_
      tangentAnalysis :=
        { toFun := id
          map_add' := by
            intro first second
            change
              @Add.add _
                  (Submodule.addCommGroup
                    (MinimalPhysicalModel period hPeriod configuration)).toAdd
                  first second =
                @Add.add _ chartData.normedAddCommGroup.toAdd first second
            rw [chartData.toAddCommGroup_eq]
          map_smul' := by
            intro scalar direction
            change
              @SMul.smul Real _
                  (Submodule.smul
                    (MinimalPhysicalModel period hPeriod configuration))
                  scalar direction =
                @SMul.smul Real _ chartData.normedSpace.toModule.toSMul
                  scalar direction
            rw [chartData.toSMul_eq] }
      tangentAnalysis_injective := by
        change Function.Injective id
        exact Function.injective_id
      tangentAnalysis_denseRange := by
        apply Function.Surjective.denseRange
        intro point
        exact ⟨point, rfl⟩ }
  · simp only [globalCandidateAMinimalPhysicalLocalVariationalChart,
      globalCandidateAMinimalPhysicalLocalActionFamily]
    exact chartData.zero_mem_domain
  · simpa only [globalCandidateAMinimalPhysicalLocalVariationalChart,
      globalCandidateAMinimalPhysicalLocalActionFamily, hZero] using
        chartData.datumAt_zero_configuration

/-- The action-level quadratic H13 bridge obtained from the concrete minimal
physical chart. -/
def globalCandidateAMinimalPhysicalQuadraticChartBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D period
      hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) := by
  letI : NormedAddCommGroup
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedAddCommGroup
  letI : NormedSpace Real
      (MinimalPhysicalModel period hPeriod configuration) :=
    chartData.normedSpace
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  have hBlocks :
      globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod (0 : chart.Model)
            chart.zero_mem_domain) measure =
        globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalActionFamily period hPeriod
              configuration data analysis chartData).toActionFamily period hPeriod
            (0 : MinimalPhysicalModel period hPeriod configuration)
            chartData.zero_mem_domain) measure := by
    congr 1
    simp only [chart, globalCandidateAMinimalPhysicalLocalVariationalChart,
      globalCandidateAMinimalPhysicalLocalActionFamily]
    congr
    exact congrArg
      (fun group : AddCommGroup
          (MinimalPhysicalModel period hPeriod configuration) => group.toZero)
      chartData.toAddCommGroup_eq
  let matterProjection : chart.Model →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared :=
    { toFun := chartData.matterProjection
      map_add' := by
        intro first second
        change MinimalPhysicalModel period hPeriod configuration at first second
        change chartData.matterProjection
            (@Add.add _ chartData.normedAddCommGroup.toAdd first second) =
          chartData.matterProjection first + chartData.matterProjection second
        rw [chartData.toAddCommGroup_eq]
        exact chartData.matterProjection.map_add first second
      map_smul' := by
        intro scalar direction
        change MinimalPhysicalModel period hPeriod configuration at direction
        change chartData.matterProjection
            (@SMul.smul Real _ chartData.normedSpace.toModule.toSMul
              scalar direction) =
          (RingHom.id Real) scalar • chartData.matterProjection direction
        rw [chartData.toSMul_eq]
        have hMap := chartData.matterProjection.map_smul scalar direction
        change chartData.matterProjection
            (@SMul.smul Real _
              (Submodule.smul
                (MinimalPhysicalModel period hPeriod configuration))
              scalar direction) =
          scalar • chartData.matterProjection direction at hMap
        simpa only [RingHom.id_apply] using hMap
      cont := chartData.matterProjection.continuous }
  let llProjection : chart.Model →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
    { toFun := chartData.llProjection
      map_add' := by
        intro first second
        change MinimalPhysicalModel period hPeriod configuration at first second
        change chartData.llProjection
            (@Add.add _ chartData.normedAddCommGroup.toAdd first second) =
          chartData.llProjection first + chartData.llProjection second
        rw [chartData.toAddCommGroup_eq]
        exact chartData.llProjection.map_add first second
      map_smul' := by
        intro scalar direction
        change MinimalPhysicalModel period hPeriod configuration at direction
        change chartData.llProjection
            (@SMul.smul Real _ chartData.normedSpace.toModule.toSMul
              scalar direction) =
          (RingHom.id Real) scalar • chartData.llProjection direction
        rw [chartData.toSMul_eq]
        have hMap := chartData.llProjection.map_smul scalar direction
        change chartData.llProjection
            (@SMul.smul Real _
              (Submodule.smul
                (MinimalPhysicalModel period hPeriod configuration))
              scalar direction) =
          scalar • chartData.llProjection direction at hMap
        simpa only [RingHom.id_apply] using hMap
      cont := chartData.llProjection.continuous }
  refine
    { chartBridge := globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
        configuration data analysis chartData
      matterProjection := matterProjection
      llProjection := llProjection
      matterConstant := chartData.matterConstant
      llConstant := chartData.llConstant
      matterAction_eq := ?_
      llAction_eq := ?_
      matterProjection_core := ?_
      llProjection_core := ?_ }
  · change
      (globalCandidateAActionBlocks period hPeriod
        (chart.family.toActionFamily period hPeriod (0 : chart.Model)
          chart.zero_mem_domain) measure).matter =
        fun state => chartData.matterConstant +
          programPPrimitiveSpinCMatterGraphAction period hPeriod
            couplings.matterMassSquared (matterProjection state)
    rw [hBlocks]
    funext state
    change MinimalPhysicalModel period hPeriod configuration at state
    calc
      _ = chartData.matterConstant +
          programPPrimitiveSpinCMatterGraphAction period hPeriod
            couplings.matterMassSquared (chartData.matterProjection state) := by
        simpa only [globalCandidateAMinimalPhysicalLocalActionFamily] using
          congrFun chartData.matterAction_eq state
      _ = _ := by rfl
  · change
      (globalCandidateAActionBlocks period hPeriod
        (chart.family.toActionFamily period hPeriod (0 : chart.Model)
          chart.zero_mem_domain) measure).ll =
        fun state => chartData.llConstant +
          globalCandidateAFullLLGraphAction period hPeriod data analysis
            (llProjection state)
    rw [hBlocks]
    funext state
    change MinimalPhysicalModel period hPeriod configuration at state
    calc
      _ = chartData.llConstant +
          globalCandidateAFullLLGraphAction period hPeriod data analysis
            (chartData.llProjection state) := by
        simpa only [globalCandidateAMinimalPhysicalLocalActionFamily] using
          congrFun chartData.llAction_eq state
      _ = _ := by rfl
  · intro core
    exact chartData.matterProjection_diagonalCore core
  · intro core
    exact chartData.llProjection_diagonalCore core

/-- The concrete minimal-physical chart data constructs the original H13
same-action bridge. -/
def globalCandidateAMinimalPhysicalMatterLLSameActionBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :=
  programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
    period hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData)

/-- Direct H13 certificate from a local action family on the corrected tangent. -/
theorem global_candidateA_h13_minimalPhysical_actionChart_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) :=
  global_candidateA_h13_matter_ll_same_action_gate period hPeriod configuration
    data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
end JanusFormal
