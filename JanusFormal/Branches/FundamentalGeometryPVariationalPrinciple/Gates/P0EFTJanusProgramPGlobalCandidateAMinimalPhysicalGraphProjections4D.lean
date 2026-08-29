import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

/-!
# Canonical graph projections from the minimal physical tangent

The minimal-physical chart still exposed arbitrary continuous projections to
the primitive matter graph and the full LL graph.  The LL projection is already
algebraically determined by the three LL slots and the existing smooth graph
embedding.  The matter projection is determined once smooth primitive SpinC
sections are realized in the maximal graph domain.

This file names that sole matter-domain realization and turns both algebraic
projections into bounded maps from one explicit pair of graph-norm estimates.
No new action or graph completion is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MinimalProjectionModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- Analytic realization of every genuine smooth two-sector primitive SpinC
field in the exact maximal graph domain.  Agreement on the finite Fourier core
prevents an unrelated extension, while action agreement records that this is
the same primitive matter action. -/
structure ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    (massSquared : Real) where
  toGraph :
    ProgramPPrimitiveSpinCMatterSmoothField period hPeriod →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared
  finite_compatibility :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      toGraph
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            coefficients) =
        programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
          coefficients
  action_agreement :
    ∀ field : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod,
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (toGraph field) =
        programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared
          field
  injective : Function.Injective toGraph

/-- Algebraic primitive-matter graph projection of a minimal physical tangent. -/
def globalMinimalPhysicalMatterGraphLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (massSquared : Real)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod massSquared) :
    MinimalProjectionModel period hPeriod configuration →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  realization.toGraph.comp
    (globalMinimalPhysicalSpinCMatterLinearMap period hPeriod configuration)

/-- Algebraic full-LL graph projection, using exactly the three LL slots of the
minimal physical tangent and the existing faithful smooth embedding. -/
def globalMinimalPhysicalLLGraphLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    MinimalProjectionModel period hPeriod configuration →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis).comp
    (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
      analysis)

/-- The two graph-norm estimates required to make the canonical algebraic
projections continuous for the selected norm on the minimal physical chart. -/
structure GlobalMinimalPhysicalMatterLLGraphBounds4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (MinimalProjectionModel period hPeriod configuration)] where
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (MinimalProjectionModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (MinimalProjectionModel period hPeriod configuration)
  matterBound : Real
  matter_le : ∀ direction,
    ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization direction‖ ≤
      matterBound * ‖direction‖
  llBound : Real
  ll_le : ∀ direction,
    ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis direction‖ ≤ llBound * ‖direction‖

/-- Continuous primitive-matter graph projection obtained from its graph-norm
estimate. -/
def globalMinimalPhysicalMatterGraphCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      couplings NonNullFace NullFace _ _ configuration data analysis realization
        normedAddCommGroup normedSpace) :
    @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
      (MinimalProjectionModel period hPeriod configuration)
      normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Submodule.addCommGroup
        (MinimalProjectionModel period hPeriod configuration)).toAddCommMonoid
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      inferInstance inferInstance
      (Submodule.module (MinimalProjectionModel period hPeriod configuration))
      inferInstance := by
  letI : NormedAddCommGroup
      (MinimalProjectionModel period hPeriod configuration) :=
    normedAddCommGroup
  letI : NormedSpace Real
      (MinimalProjectionModel period hPeriod configuration) :=
    normedSpace
  let adapted :
      @LinearMap Real Real _ _ (RingHom.id Real)
        (MinimalProjectionModel period hPeriod configuration)
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
        normedSpace.toModule inferInstance :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real)
      (MinimalProjectionModel period hPeriod configuration)
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
      normedSpace.toModule inferInstance
      (@AddHom.mk
        (MinimalProjectionModel period hPeriod configuration)
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd inferInstance
        (fun direction =>
          globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction)
        (by
          intro first second
          change
            globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization
                (@Add.add _
                  normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                  first second) =
              globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                  configuration couplings.matterMassSquared realization first +
                globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                  configuration couplings.matterMassSquared realization second
          rw [bounds.toAddCommGroup_eq]
          exact (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
            configuration couplings.matterMassSquared realization).map_add
              first second))
      (by
        intro scalar direction
        change
          globalMinimalPhysicalMatterGraphLinearMap period hPeriod
              configuration couplings.matterMassSquared realization
              (@SMul.smul Real _ normedSpace.toModule.toSMul scalar direction) =
            (RingHom.id Real) scalar •
              globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction
        rw [bounds.toSMul_eq]
        have hMap :=
          (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
            configuration couplings.matterMassSquared realization).map_smul
              scalar direction
        change
          globalMinimalPhysicalMatterGraphLinearMap period hPeriod
              configuration couplings.matterMassSquared realization
              (@SMul.smul Real _
                (Submodule.smul
                  (MinimalProjectionModel period hPeriod configuration))
                scalar direction) =
            scalar •
              globalMinimalPhysicalMatterGraphLinearMap period hPeriod
                configuration couplings.matterMassSquared realization direction
          at hMap
        simpa only [RingHom.id_apply] using hMap)
  let bounded := adapted.mkContinuous bounds.matterBound (by
    intro direction
    change
      ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction‖ ≤
        bounds.matterBound * ‖direction‖
    exact bounds.matter_le direction)
  exact
    { toFun := fun direction =>
        globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction
      map_add' := (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
        configuration couplings.matterMassSquared realization).map_add
      map_smul' := by
        intro scalar direction
        simpa only [RingHom.id_apply] using
          (globalMinimalPhysicalMatterGraphLinearMap period hPeriod
            configuration couplings.matterMassSquared realization).map_smul
              scalar direction
      cont := by
        change Continuous (fun direction =>
          globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction)
        exact @ContinuousLinearMap.cont Real Real _ _ (RingHom.id Real)
          (MinimalProjectionModel period hPeriod configuration)
          normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          normedAddCommGroup.toSeminormedAddCommGroup.toAddCommMonoid
          (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
            couplings.matterMassSquared)
          inferInstance inferInstance normedSpace.toModule inferInstance bounded }

/-- Continuous full-LL graph projection obtained from its graph-norm estimate. -/
def globalMinimalPhysicalLLGraphCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      couplings NonNullFace NullFace _ _ configuration data analysis realization
        normedAddCommGroup normedSpace) :
    @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
      (MinimalProjectionModel period hPeriod configuration)
      normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Submodule.addCommGroup
        (MinimalProjectionModel period hPeriod configuration)).toAddCommMonoid
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance inferInstance
      (Submodule.module (MinimalProjectionModel period hPeriod configuration))
      inferInstance := by
  letI : NormedAddCommGroup
      (MinimalProjectionModel period hPeriod configuration) :=
    normedAddCommGroup
  letI : NormedSpace Real
      (MinimalProjectionModel period hPeriod configuration) :=
    normedSpace
  let adapted :
      @LinearMap Real Real _ _ (RingHom.id Real)
        (MinimalProjectionModel period hPeriod configuration)
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
        normedSpace.toModule inferInstance :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real)
      (MinimalProjectionModel period hPeriod configuration)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
      normedSpace.toModule inferInstance
      (@AddHom.mk
        (MinimalProjectionModel period hPeriod configuration)
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd inferInstance
        (fun direction =>
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
            analysis direction)
        (by
          intro first second
          change
            globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis
                (@Add.add _
                  normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                  first second) =
              globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis first +
                globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                  data analysis second
          rw [bounds.toAddCommGroup_eq]
          exact (globalMinimalPhysicalLLGraphLinearMap period hPeriod
            configuration data analysis).map_add first second))
      (by
        intro scalar direction
        change
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
              data analysis
              (@SMul.smul Real _ normedSpace.toModule.toSMul scalar direction) =
            (RingHom.id Real) scalar •
              globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis direction
        rw [bounds.toSMul_eq]
        have hMap :=
          (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
            data analysis).map_smul scalar direction
        change
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
              data analysis
              (@SMul.smul Real _
                (Submodule.smul
                  (MinimalProjectionModel period hPeriod configuration))
                scalar direction) =
            scalar •
              globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
                data analysis direction
          at hMap
        simpa only [RingHom.id_apply] using hMap)
  let bounded := adapted.mkContinuous bounds.llBound (by
    intro direction
    change
      ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction‖ ≤ bounds.llBound * ‖direction‖
    exact bounds.ll_le direction)
  exact
    { toFun := fun direction =>
        globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction
      map_add' := (globalMinimalPhysicalLLGraphLinearMap period hPeriod
        configuration data analysis).map_add
      map_smul' := by
        intro scalar direction
        simpa only [RingHom.id_apply] using
          (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
            data analysis).map_smul scalar direction
      cont := by
        change Continuous (fun direction =>
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
            analysis direction)
        exact @ContinuousLinearMap.cont Real Real _ _ (RingHom.id Real)
          (MinimalProjectionModel period hPeriod configuration)
          normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          normedAddCommGroup.toSeminormedAddCommGroup.toAddCommMonoid
          (GlobalFullLLGraphHilbert period hPeriod data analysis)
          inferInstance inferInstance normedSpace.toModule inferInstance bounded }

@[simp]
theorem globalMinimalPhysicalMatterGraphCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      couplings NonNullFace NullFace _ _ configuration data analysis realization
        normedAddCommGroup normedSpace)
    (direction : MinimalProjectionModel period hPeriod configuration) :
    globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
        analysis realization bounds direction =
      realization.toGraph direction.1.2 :=
  rfl

@[simp]
theorem globalMinimalPhysicalLLGraphCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      couplings NonNullFace NullFace _ _ configuration data analysis realization
        normedAddCommGroup normedSpace)
    (direction : MinimalProjectionModel period hPeriod configuration) :
    globalMinimalPhysicalLLGraphCLM period hPeriod configuration data analysis
        realization bounds direction =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
          analysis direction) :=
  rfl

/-- Compatibility of the canonical graph projections with the existing
finite/LL diagonal smooth core.  These equalities can normally be discharged
by unfolding the typed tangent assembly; they are kept together here as the
final algebraic adapter. -/
structure GlobalMinimalPhysicalMatterLLGraphCoreCompatibility4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) : Prop where
  matter : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis,
    globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.2.1
  ll : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis,
    globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2.2

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
end JanusFormal
