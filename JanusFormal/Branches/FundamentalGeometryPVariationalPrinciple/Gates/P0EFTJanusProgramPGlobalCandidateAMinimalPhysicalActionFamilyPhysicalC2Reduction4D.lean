import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D

/-!
# Candidate-A local family from the seven physical `C²` blocks

The reduced H13 family still stored `C²` regularity of all nine action blocks.
That duplicates analytic information already proved by the two same-action graph
packages: both the primitive SpinC matter action and the full LL action are
globally smooth quadratic forms on their graph Hilbert spaces.

This file keeps only `C²` regularity of the seven genuinely physical blocks.
The matter and LL fields of `FullCoupledC2WithinAt` are reconstructed from the
exact action identities and the existing continuous graph projections.
Consequently this route does not introduce a second regularity hypothesis for
either closed graph sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

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

private abbrev ReducedFamilyModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- `C²` regularity of exactly the seven physical summands not represented by
the primitive matter and full LL graph actions. -/
structure GlobalCandidateASevenPhysicalC2WithinAt
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (domain : Set Model) (point : Model) : Prop where
  candidateA : ContDiffWithinAt Real 2 blocks.candidateA domain point
  robin : ContDiffWithinAt Real 2 blocks.robin domain point
  einsteinHilbertPlus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertPlus domain point
  einsteinHilbertMinus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertMinus domain point
  maxwellPlus : ContDiffWithinAt Real 2 blocks.maxwellPlus domain point
  maxwellMinus : ContDiffWithinAt Real 2 blocks.maxwellMinus domain point
  finiteBV : ContDiffWithinAt Real 2 blocks.finiteBV domain point

/-- Local Candidate-A data in which only the seven physical blocks carry a
regularity hypothesis. Matter and LL regularity are consequences of the exact
same-action identities below. -/
structure ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) where
  [normedAddCommGroup : NormedAddCommGroup
    (ReducedFamilyModel period hPeriod configuration)]
  [normedSpace : NormedSpace Real
    (ReducedFamilyModel period hPeriod configuration)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (ReducedFamilyModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (ReducedFamilyModel period hPeriod configuration)
  bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace
  domain : Set (ReducedFamilyModel period hPeriod configuration)
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ReducedFamilyModel period hPeriod configuration) ∈
    domain
  datumAt : ∀ point : ReducedFamilyModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  physicalBlocksC2Within : ∀ point (hPoint : point ∈ domain),
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    GlobalCandidateASevenPhysicalC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (@globalMinimalPhysicalMatterGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)
  llAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (@globalMinimalPhysicalLLGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)

/-- The primitive matter block is automatically `C²` after pullback by the
bounded graph projection. -/
private theorem matterGraphPullback_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (ReducedFamilyModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (ReducedFamilyModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization)
    (constant : Real)
    (domain : Set (ReducedFamilyModel period hPeriod configuration))
    (point : ReducedFamilyModel period hPeriod configuration) :
    ContDiffWithinAt Real 2
      (fun state => constant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
            analysis realization bounds state))
      domain point := by
  let projection := @globalMinimalPhysicalMatterGraphCLM period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace bounds
  let adaptedLinear :
      @LinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
        normedSpace.toModule inferInstance :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
      normedSpace.toModule inferInstance
      (@AddHom.mk
        (ReducedFamilyModel period hPeriod configuration)
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd inferInstance
        (fun direction => projection direction)
        (by
        intro first second
        change projection
            (@Add.add _
              normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
              first second) =
          projection first + projection second
        rw [bounds.toAddCommGroup_eq]
        exact projection.map_add first second))
      (by
        intro scalar direction
        change projection
            (@SMul.smul Real _ normedSpace.toModule.toSMul scalar direction) =
          (RingHom.id Real) scalar • projection direction
        rw [bounds.toSMul_eq]
        have hMap := projection.map_smul scalar direction
        change projection
            (@SMul.smul Real _
              (Submodule.smul
                (ReducedFamilyModel period hPeriod configuration))
              scalar direction) =
          scalar • projection direction at hMap
        simpa only [RingHom.id_apply] using hMap)
  let adapted :
      @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid
        (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
          couplings.matterMassSquared)
        inferInstance inferInstance normedSpace.toModule inferInstance :=
    @ContinuousLinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      inferInstance inferInstance normedSpace.toModule inferInstance
      adaptedLinear
      (by
        change Continuous (fun direction => projection direction)
        exact projection.cont)
  have hProjection : ContDiff Real ∞ adapted := adapted.contDiff
  have hProjectionTwo : ContDiff Real 2 adapted :=
    hProjection.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have hAction : ContDiff Real 2
      (programPPrimitiveSpinCMatterGraphAction period hPeriod
        couplings.matterMassSquared) :=
    programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared
  exact (contDiff_const.add (hAction.comp hProjectionTwo)).contDiffWithinAt

/-- The full three-slot LL block is automatically `C²` after pullback by its
bounded graph projection. -/
private theorem llGraphPullback_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [normedAddCommGroup :
      NormedAddCommGroup (ReducedFamilyModel period hPeriod configuration)]
    [normedSpace :
      NormedSpace Real (ReducedFamilyModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization)
    (constant : Real)
    (domain : Set (ReducedFamilyModel period hPeriod configuration))
    (point : ReducedFamilyModel period hPeriod configuration) :
    ContDiffWithinAt Real 2
      (fun state => constant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalMinimalPhysicalLLGraphCLM period hPeriod configuration data
            analysis realization bounds state))
      domain point := by
  letI llNormedSpace : NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace
  let projection := @globalMinimalPhysicalLLGraphCLM period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace bounds
  let adaptedLinear :
      @LinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
        normedSpace.toModule inferInstance :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid inferInstance
      normedSpace.toModule inferInstance
      (@AddHom.mk
        (ReducedFamilyModel period hPeriod configuration)
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd inferInstance
        (fun direction => projection direction)
        (by
          intro first second
          change projection
              (@Add.add _
                normedAddCommGroup.toAddCommGroup.toAddCommMonoid.toAdd
                first second) =
            projection first + projection second
          rw [bounds.toAddCommGroup_eq]
          exact projection.map_add first second))
      (by
        intro scalar direction
        change projection
            (@SMul.smul Real _ normedSpace.toModule.toSMul scalar direction) =
          (RingHom.id Real) scalar • projection direction
        rw [bounds.toSMul_eq]
        have hMap := projection.map_smul scalar direction
        change projection
            (@SMul.smul Real _
              (Submodule.smul
                (ReducedFamilyModel period hPeriod configuration))
              scalar direction) =
          scalar • projection direction at hMap
        simpa only [RingHom.id_apply] using hMap)
  let adapted :
      @ContinuousLinearMap Real Real _ _ (RingHom.id Real)
        (ReducedFamilyModel period hPeriod configuration)
        normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        normedAddCommGroup.toAddCommGroup.toAddCommMonoid
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        inferInstance inferInstance normedSpace.toModule inferInstance :=
    @ContinuousLinearMap.mk Real Real _ _ (RingHom.id Real)
      (ReducedFamilyModel period hPeriod configuration)
      normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      normedAddCommGroup.toAddCommGroup.toAddCommMonoid
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance inferInstance normedSpace.toModule inferInstance
      adaptedLinear
      (by
        change Continuous (fun direction => projection direction)
        exact projection.cont)
  have hProjection : ContDiff Real ∞ adapted :=
    @ContinuousLinearMap.contDiff Real
      (ReducedFamilyModel period hPeriod configuration)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance normedAddCommGroup normedSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
      llNormedSpace ∞ adapted
  have hProjectionTwo : ContDiff Real 2 adapted :=
    hProjection.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have hAction : ContDiff Real 2
      (globalCandidateAFullLLGraphAction period hPeriod data analysis) :=
    globalCandidateAFullLLGraphAction_contDiff_two period hPeriod data analysis
  exact (contDiff_const.add (hAction.comp hProjectionTwo)).contDiffWithinAt

/-- Reconstruct the previous reduced family packet. The two missing `C²`
fields are discharged by the graph-action smoothness theorems. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D.toReduced
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared}
    (family :
      ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D
        period hPeriod (measure := measure) configuration data analysis
          realization) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        realization where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  toAddCommGroup_eq := family.toAddCommGroup_eq
  toSMul_eq := family.toSMul_eq
  bounds := family.bounds
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  blocksC2Within := by
    letI : NormedAddCommGroup
        (ReducedFamilyModel period hPeriod configuration) :=
      family.normedAddCommGroup
    letI : NormedSpace Real
        (ReducedFamilyModel period hPeriod configuration) :=
      family.normedSpace
    intro point hPoint
    let localFamily : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := family.domain
        datumAt := family.datumAt }
    let blocks := globalCandidateAActionBlocks period hPeriod
      (localFamily.toActionFamily period hPeriod 0 family.zero_mem_domain)
      measure
    have hPhysical :
        GlobalCandidateASevenPhysicalC2WithinAt blocks family.domain point := by
      simpa [localFamily, blocks] using
        family.physicalBlocksC2Within point hPoint
    have hMatter :
        ContDiffWithinAt Real 2 blocks.matter family.domain point := by
      rw [show blocks.matter =
          fun state => family.matterConstant +
            programPPrimitiveSpinCMatterGraphAction period hPeriod
              couplings.matterMassSquared
              (@globalMinimalPhysicalMatterGraphCLM period hPeriod couplings
                NonNullFace NullFace _ _ configuration data analysis realization
                family.normedAddCommGroup family.normedSpace family.bounds state)
          by
            simpa [localFamily, blocks] using family.matterAction_eq]
      exact @matterGraphPullback_contDiffWithinAt period hPeriod couplings
        NonNullFace NullFace _ _ measure configuration data analysis realization
        family.normedAddCommGroup family.normedSpace family.bounds
        family.matterConstant family.domain point
    have hLL :
        ContDiffWithinAt Real 2 blocks.ll family.domain point := by
      rw [show blocks.ll =
          fun state => family.llConstant +
            globalCandidateAFullLLGraphAction period hPeriod data analysis
              (@globalMinimalPhysicalLLGraphCLM period hPeriod couplings
                NonNullFace NullFace _ _ configuration data analysis realization
                family.normedAddCommGroup family.normedSpace family.bounds state)
          by
            simpa [localFamily, blocks] using family.llAction_eq]
      exact @llGraphPullback_contDiffWithinAt period hPeriod couplings
        NonNullFace NullFace _ _ measure configuration data analysis realization
        family.normedAddCommGroup family.normedSpace family.bounds
        family.llConstant family.domain point
    exact
      { candidateA := hPhysical.candidateA
        matter := hMatter
        robin := hPhysical.robin
        ll := hLL
        einsteinHilbertPlus := hPhysical.einsteinHilbertPlus
        einsteinHilbertMinus := hPhysical.einsteinHilbertMinus
        maxwellPlus := hPhysical.maxwellPlus
        maxwellMinus := hPhysical.maxwellMinus
        finiteBV := hPhysical.finiteBV }
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- H13 now needs regularity input only for the seven physical summands. -/
theorem global_candidateA_h13_minimalPhysical_physicalC2Family_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (family :
      ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D
        period hPeriod (measure := measure) configuration data analysis
          realization) :
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily
              period hPeriod configuration data analysis realization
                (family.toReduced period hPeriod)))
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily
              period hPeriod configuration data analysis realization
                (family.toReduced period hPeriod))) :=
  global_candidateA_h13_minimalPhysical_reducedFamily_gate period hPeriod
    configuration data analysis realization (family.toReduced period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
end JanusFormal
