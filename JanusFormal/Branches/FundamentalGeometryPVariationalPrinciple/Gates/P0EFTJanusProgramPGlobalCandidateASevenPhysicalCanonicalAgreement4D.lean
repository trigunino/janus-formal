import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D

/-!
# Canonical H11 extensions from dense-core agreement alone

A continuous bilinear extension of one genuine physical Hessian block need not
carry a separate symmetry proof.  The local action block is `C²`, hence its
second Frechet derivative is symmetric on the smooth core.  Since that core is
dense in the unique common Hilbert completion, agreement on the core and
continuity force symmetry everywhere.

This file removes the seven independent symmetry fields from the H11 input.
The only data left for each block are a continuous bilinear form and its exact
agreement with the canonical physical second derivative on the dense core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option synthInstance.maxHeartbeats 2200000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev AgreementCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev AgreementHilbert
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

private abbrev agreementHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (AgreementHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

attribute [local instance 30000] agreementHilbertNormedAddCommGroup

local instance (priority := 30000) agreementHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (AgreementHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) agreementHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (AgreementHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- `C²` regularity of each actual local physical block at the chart base. -/
theorem globalCandidateAPhysicalBlockAction_contDiffAt_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (block : GlobalCandidateAPhysicalBlock) :
    ContDiffAt Real 2
      (globalCandidateAPhysicalBlockAction
        (globalCandidateASevenPhysicalLocalBlocks period hPeriod chart) block)
      point := by
  let blocks := globalCandidateASevenPhysicalLocalBlocks period hPeriod chart
  have hAll : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint)
      chart.isOpen_domain hPoint
  cases block with
  | candidateA =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.candidateA
  | robin =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.robin
  | einsteinHilbertPlus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using
        hAll.einsteinHilbertPlus
  | einsteinHilbertMinus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using
        hAll.einsteinHilbertMinus
  | maxwellPlus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.maxwellPlus
  | maxwellMinus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.maxwellMinus
  | finiteBV =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.finiteBV

/-- Symmetry of each canonical physical core form is a theorem of its genuine
`C²` action block. -/
theorem globalCandidateAPhysicalBlockCanonicalCoreForm_symmetric
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
      period hPeriod configuration data analysis chart)
    (block : GlobalCandidateAPhysicalBlock)
    (first second : AgreementCore period hPeriod analysis) :
    globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block first second =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block second first := by
  have hSmooth : minSmoothness Real 2 ≤ (2 : ℕ∞ω) := by
    simp [minSmoothness_of_isRCLikeNormedField]
  have hSymmetric :=
    (globalCandidateAPhysicalBlockAction_contDiffAt_two period hPeriod chart
      sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem
      block).isSymmSndFDerivAt hSmooth
  unfold globalCandidateAPhysicalBlockCanonicalCoreForm
  exact hSymmetric _ _

/-- H11 input with no supplied symmetry fields. -/
structure GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
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
      period hPeriod configuration data analysis chart) : Type where
  form : GlobalCandidateAPhysicalBlock →
    AgreementHilbert period hPeriod configuration data analysis →L[Real]
      AgreementHilbert period hPeriod configuration data analysis →L[Real] Real
  core_agreement : ∀ block first second,
    form block
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second) =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
        configuration data analysis chart sameAction block first second
  reconstruct : ∀ first second : AgreementCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second =
      ∑ block : GlobalCandidateAPhysicalBlock,
        globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
          configuration data analysis chart sameAction block first second

/-- Dense-core symmetry and continuity force symmetry of every supplied
extension. -/
theorem canonicalContinuousAgreement_symmetric
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
      period hPeriod configuration data analysis chart)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock)
    (first second : AgreementHilbert period hPeriod configuration data analysis) :
    extensions.form block first second =
      extensions.form block second first := by
  let form : AgreementHilbert period hPeriod configuration data analysis →L[Real]
      AgreementHilbert period hPeriod configuration data analysis →L[Real] Real :=
    extensions.form block
  change form first second = form second first
  let embedding := globalCandidateASevenPhysicalCoreEmbedding period hPeriod
    configuration data analysis
  let flipped : AgreementHilbert period hPeriod configuration data analysis →L[Real]
      AgreementHilbert period hPeriod configuration data analysis →L[Real] Real :=
    ContinuousLinearMap.flip
      (𝕜 := Real) (𝕜₂ := Real) (𝕜₃ := Real)
      (E := AgreementHilbert period hPeriod configuration data analysis)
      (F := AgreementHilbert period hPeriod configuration data analysis)
      (G := Real) (σ₁₃ := RingHom.id Real) (σ₂₃ := RingHom.id Real) form
  have hSwapContinuous
      (fixed : AgreementHilbert period hPeriod configuration data analysis) :
      Continuous (fun x => form x fixed) := by
    change Continuous ⇑(flipped fixed)
    exact (flipped fixed).continuous
  have hDense := diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  have hFirst :
      (fun x => form x second) = fun x => form second x := by
    apply hDense.equalizer
    · exact hSwapContinuous second
    · exact (form second).continuous
    · funext core
      have hCore :
          (fun x => form (embedding core) x) =
            fun x => form x (embedding core) := by
        apply hDense.equalizer
        · exact (form (embedding core)).continuous
        · exact hSwapContinuous (embedding core)
        · funext test
          calc
            form (embedding core) (embedding test) =
                globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
                  configuration data analysis chart sameAction block core test :=
              extensions.core_agreement block core test
            _ = globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
                  configuration data analysis chart sameAction block test core :=
              globalCandidateAPhysicalBlockCanonicalCoreForm_symmetric period
                hPeriod (measure := measure) configuration data analysis chart
                  sameAction block core test
            _ = form (embedding test) (embedding core) :=
              (extensions.core_agreement block test core).symm
      exact congrFun hCore second
  exact congrFun hFirst first

/-- Reconstruct the earlier canonical-extension packet. -/
def GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D.toCanonical
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction where
  extension := extensions.form
  extension_agrees := extensions.core_agreement
  symmetric := by
    intro block first second
    exact canonicalContinuousAgreement_symmetric period hPeriod
      (measure := measure) configuration data analysis chart sameAction
        extensions block first second
  reconstruct := extensions.reconstruct

/-- H11 canonical extensions from agreement alone. -/
def candidate_a_seven_physical_canonical_agreement_gate
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
      period hPeriod configuration data analysis chart)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis chart sameAction) :=
  candidate_a_seven_physical_canonical_extensions_gate period hPeriod
    (measure := measure) configuration data analysis chart sameAction
      (extensions.toCanonical period hPeriod (measure := measure))

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D
end JanusFormal
