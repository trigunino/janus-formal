import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D

/-!
# Local projected physical basis of the actual Candidate-A kernel

Near the H12 basepoint the projected physical Gram operator is now known to be
injective.  Since the actual kernel has the fixed finite rank indexed by
`ZeroMode`, the projected vectors therefore form a genuine basis of the whole
kernel throughout that neighbourhood.

This file packages the pointwise basis, proves local bijectivity of coefficient
synthesis, and gives unique projected physical coordinates for every actual
zero mode.  At `a = 0` this specializes to the previously constructed H12
basepoint basis; away from zero it is the canonical sector-projected basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D

set_option autoImplicit false
set_option maxHeartbeats 46000000
set_option synthInstance.maxHeartbeats 23000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D
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

/-- A pointwise basis packet whose vectors are exactly the canonical projected
physical zero modes. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelBasisAt4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) where
  basis : Module.Basis ZeroMode Real
    (input.familyIndex.baseFamily.actualOperator parameter).ker
  basis_agreement : ∀ mode,
    basis mode =
      projectedKernelSubtypeVector period hPeriod input natural parameter mode

/-- Gram injectivity at one parameter constructs the corresponding canonical
projected physical basis of the whole actual kernel. -/
def projectedKernelBasisAtOfGramInjective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter)) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisAt4D
      period hPeriod input natural parameter := by
  exact
    { basis :=
        GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D.projectedKernelBasisAtOfGramInjective
          period hPeriod input natural parameter hGram
      basis_agreement := by
        intro mode
        apply Subtype.ext
        exact
          GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D.projectedKernelBasisAtOfGramInjective_apply
            period hPeriod input natural parameter hGram mode }

/-- The canonical pointwise projected basis exists throughout a neighbourhood
of the H12 basepoint. -/
theorem eventually_projectedKernelBasisAt
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    ∀ᶠ parameter in 𝓝 (0 : Real),
      Nonempty
        (GlobalHessianPreferredFiveSectorProjectedKernelBasisAt4D
          period hPeriod input natural parameter) := by
  filter_upwards
    [eventually_projectedKernelGram_injective period hPeriod input natural
      regularity] with parameter hGram
  exact ⟨projectedKernelBasisAtOfGramInjective period hPeriod input natural
    parameter hGram⟩

/-- At every parameter where the projected Gram operator is injective,
coefficient synthesis by the projected physical vectors is bijective onto the
whole actual kernel. -/
theorem projectedKernelSynthesis_bijective_of_gram_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter)) :
    Function.Bijective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural parameter)) := by
  let basisData := projectedKernelBasisAtOfGramInjective period hPeriod input
    natural parameter hGram
  exact finiteFamilySynthesis_bijective_of_basis
    (projectedKernelSubtypeVector period hPeriod input natural parameter)
    basisData.basis basisData.basis_agreement

/-- Projected physical coefficient synthesis is locally bijective around the
H12 basepoint. -/
theorem eventually_projectedKernelSynthesis_bijective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    ∀ᶠ parameter in 𝓝 (0 : Real),
      Function.Bijective
        (finiteFamilySynthesis
          (projectedKernelSubtypeVector period hPeriod input natural parameter)) := by
  filter_upwards
    [eventually_projectedKernelGram_injective period hPeriod input natural
      regularity] with parameter hGram
  exact projectedKernelSynthesis_bijective_of_gram_injective period hPeriod input
    natural parameter hGram

/-- Every actual zero mode has one and only one set of projected physical
coordinates throughout the basepoint neighbourhood. -/
theorem eventually_existsUnique_projectedKernelCoordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    ∀ᶠ parameter in 𝓝 (0 : Real),
      ∀ vector : (input.familyIndex.baseFamily.actualOperator parameter).ker,
        ∃! coefficient : ZeroMode → Real,
          finiteFamilySynthesis
              (projectedKernelSubtypeVector period hPeriod input natural parameter)
              coefficient =
            vector := by
  filter_upwards
    [eventually_projectedKernelSynthesis_bijective period hPeriod input natural
      regularity] with parameter hBijection
  intro vector
  obtain ⟨coefficient, hCoefficient⟩ := hBijection.2 vector
  refine ⟨coefficient, hCoefficient, ?_⟩
  intro other hOther
  exact hBijection.1 (hOther.trans hCoefficient.symm)

/-- Public local projected-basis and unique-coordinate checkpoint. -/
theorem projected_kernel_basis_local_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (∀ᶠ parameter in 𝓝 (0 : Real),
      Nonempty
        (GlobalHessianPreferredFiveSectorProjectedKernelBasisAt4D
          period hPeriod input natural parameter)) ∧
    (∀ᶠ parameter in 𝓝 (0 : Real),
      ∀ vector : (input.familyIndex.baseFamily.actualOperator parameter).ker,
        ∃! coefficient : ZeroMode → Real,
          finiteFamilySynthesis
              (projectedKernelSubtypeVector period hPeriod input natural parameter)
              coefficient =
            vector) :=
  ⟨eventually_projectedKernelBasisAt period hPeriod input natural regularity,
    eventually_existsUnique_projectedKernelCoordinates period hPeriod input
      natural regularity⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D
end JanusFormal
