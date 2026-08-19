import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D

/-!
# Canonical open chart of projected-kernel nondegeneracy

The determinant of the ambient projected Gram matrix defines a canonical
regular parameter set

`U_Gram = {a | det Gram(e~_i(a)) != 0}`.

The selected projected zero modes are continuous, hence `U_Gram` is open.  The
H12 basepoint belongs to it by the already proved Gram nondegeneracy at zero.
On this open chart the projected vectors form the entire actual kernel basis
and every zero mode has unique physical coordinates.

This turns the previous filter-local statement into an explicit maximal open
Fredholm chart.  Extending the preferred physical basis globally is now
reduced to proving that the genuine Candidate-A parameter path remains in this
regular set, or equivalently that the projected Gram determinant never reaches
zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D

set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option synthInstance.maxHeartbeats 24000000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable {measure : Measure (EffectiveQuotient period hPeriod)}

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- Maximal parameter set on which the canonical projected physical vectors
have nonzero scalar Gram determinant. -/
def projectedKernelRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Set Real :=
  {parameter |
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det ≠ 0}

/-- The projected-kernel regular set is open whenever the selected named kernel
family has the required ambient differentiability. -/
theorem isOpen_projectedKernelRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    IsOpen (projectedKernelRegularSet period hPeriod input) := by
  have hContinuous :
      Continuous
        (fun parameter : Real =>
          (finiteFamilyGramMatrix
            (fun mode =>
              projectedNamedKernelVector period hPeriod input parameter mode)).det) :=
    continuous_finiteFamilyGramDeterminant
      (fun parameter mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)
      (projectedNamedKernelVector_continuous period hPeriod input regularity)
  change IsOpen
    ((fun parameter : Real =>
      (finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).det) ⁻¹'
      ({0} : Set Real)ᶜ)
  exact isOpen_compl_singleton.preimage hContinuous

/-- The H12 physical basepoint belongs to the regular chart. -/
theorem zero_mem_projectedKernelRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    (0 : Real) ∈ projectedKernelRegularSet period hPeriod input := by
  letI hNormed : NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  letI hInner : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  letI : Module Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) := hInner.toNormedSpace.toModule
  change
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input 0 mode)).det ≠ 0
  have hInjective :=
    projectedKernelGram_zero_injective period hPeriod input natural
  change Function.Injective
    (@finiteFamilyGramMap ZeroMode
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) inferInstance hNormed hInner
      (fun mode => projectedNamedKernelVector period hPeriod input 0 mode)) at hInjective
  exact (@finiteFamilyGramMap_injective_iff_det_ne_zero ZeroMode
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
      data analysis) inferInstance inferInstance hNormed hInner
    (fun mode => projectedNamedKernelVector period hPeriod input 0 mode)).mp
      hInjective

/-- Membership in the ambient regular chart is equivalent to injectivity of the
genuine projected Gram operator on the true kernel subtype. -/
theorem mem_projectedKernelRegularSet_iff_gram_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) :
    parameter ∈ projectedKernelRegularSet period hPeriod input ↔
      Function.Injective
        (projectedKernelGramMap period hPeriod input natural parameter) := by
  letI hNormed : NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  letI hInner : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  letI : Module Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) := hInner.toNormedSpace.toModule
  change
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det ≠ 0 ↔
      Function.Injective
        (projectedKernelGramMap period hPeriod input natural parameter)
  change
    (finiteFamilyGramMatrix
      (fun mode => projectedNamedKernelVector period hPeriod input parameter mode)).det ≠
        0 ↔
      Function.Injective
        (@finiteFamilyGramMap ZeroMode
          (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
            data analysis) inferInstance hNormed hInner
          (fun mode =>
            projectedNamedKernelVector period hPeriod input parameter mode))
  exact (@finiteFamilyGramMap_injective_iff_det_ne_zero ZeroMode
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
      data analysis) inferInstance inferInstance hNormed hInner
    (fun mode =>
      projectedNamedKernelVector period hPeriod input parameter mode)).symm

/-- The regular chart is an actual neighbourhood of the H12 basepoint. -/
theorem projectedKernelRegularSet_mem_nhds_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    projectedKernelRegularSet period hPeriod input ∈ 𝓝 (0 : Real) :=
  (isOpen_projectedKernelRegularSet period hPeriod input regularity).mem_nhds
    (zero_mem_projectedKernelRegularSet period hPeriod input natural)

/-- Canonical projected physical basis attached to every point of the regular
chart. -/
def projectedKernelBasisOnRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisAt4D
      period hPeriod input natural parameter.1 :=
  projectedKernelBasisAtOfGramInjective period hPeriod input natural parameter.1
    ((mem_projectedKernelRegularSet_iff_gram_injective period hPeriod input
      natural parameter.1).mp parameter.2)

/-- The chart basis vectors are exactly the canonical sector-projected physical
zero modes. -/
theorem projectedKernelBasisOnRegularSet_agreement
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input)
    (mode : ZeroMode) :
    (projectedKernelBasisOnRegularSet period hPeriod input natural parameter).basis
        mode =
      projectedKernelSubtypeVector period hPeriod input natural parameter.1 mode :=
  (projectedKernelBasisOnRegularSet period hPeriod input natural parameter).basis_agreement
    mode

/-- Unique projected physical coordinates exist at every point of the regular
chart, not merely eventually in a filter. -/
theorem existsUnique_projectedKernelCoordinates_onRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input)
    (vector :
      (input.familyIndex.baseFamily.actualOperator parameter.1).ker) :
    ∃! coefficient : ZeroMode → Real,
      finiteFamilySynthesis
          (projectedKernelSubtypeVector period hPeriod input natural parameter.1)
          coefficient =
        vector := by
  have hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter.1) :=
    (mem_projectedKernelRegularSet_iff_gram_injective period hPeriod input natural
      parameter.1).mp parameter.2
  have hBijection :=
    projectedKernelSynthesis_bijective_of_gram_injective period hPeriod input
      natural parameter.1 hGram
  obtain ⟨coefficient, hCoefficient⟩ := hBijection.2 vector
  refine ⟨coefficient, hCoefficient, ?_⟩
  intro other hOther
  exact hBijection.1 (hOther.trans hCoefficient.symm)

/-- Public open projected-kernel Fredholm-chart checkpoint. -/
theorem projected_kernel_regular_chart_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    IsOpen (projectedKernelRegularSet period hPeriod input) ∧
    (0 : Real) ∈ projectedKernelRegularSet period hPeriod input ∧
    projectedKernelRegularSet period hPeriod input ∈ 𝓝 (0 : Real) :=
  ⟨isOpen_projectedKernelRegularSet period hPeriod input regularity,
    zero_mem_projectedKernelRegularSet period hPeriod input natural,
    projectedKernelRegularSet_mem_nhds_zero period hPeriod input natural
      regularity⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
end JanusFormal
