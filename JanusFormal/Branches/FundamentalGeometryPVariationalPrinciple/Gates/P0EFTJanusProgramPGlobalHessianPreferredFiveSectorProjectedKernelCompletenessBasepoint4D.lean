import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisBasepoint4D

/-!
# Full projected-kernel completeness at the H12 basepoint

The preceding basepoint file constructs the projected physical modes as a basis
of the true Candidate-A Hessian kernel at `a = 0`.  Here we expose the stronger
coordinate statement used by the later Fredholm-family layer: coefficient
synthesis by those projected modes is a linear bijection onto the actual
kernel.

Consequently every genuine basepoint zero mode has unique physical projected
coordinates.  This closes the basepoint form of the "action generators span the
actual kernel" statement without adding a dimension or completeness premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCompletenessBasepoint4D

set_option autoImplicit false
set_option maxHeartbeats 42000000
set_option synthInstance.maxHeartbeats 21000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisBasepoint4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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
      period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- At the basepoint, coefficient synthesis by the projected physical modes is
bijective onto the actual Hessian kernel. -/
theorem projectedKernelSynthesis_zero_bijective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Bijective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)) := by
  letI : FiniteDimensional Real
      (input.familyIndex.baseFamily.actualOperator 0).ker :=
    (input.kernels.basis 0).finiteDimensional
  exact finiteFamilySynthesis_bijective_of_gram_injective
    (projectedKernelSubtypeVector period hPeriod input natural 0)
    (input.kernels.kernel_finrank_eq_card 0)
    (projectedKernelGram_zero_injective period hPeriod input natural)

/-- Every genuine zero mode at `a = 0` is synthesized by projected physical
modes. -/
theorem projectedKernelSynthesis_zero_surjective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Surjective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)) :=
  (projectedKernelSynthesis_zero_bijective period hPeriod input natural).2

/-- The projected physical coordinates of a basepoint zero mode are unique. -/
theorem projectedKernelSynthesis_zero_injective'
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)) :=
  (projectedKernelSynthesis_zero_bijective period hPeriod input natural).1

/-- Explicit existence and uniqueness of projected physical coordinates for
any actual basepoint zero mode. -/
theorem existsUnique_projectedKernelCoordinates_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).ker) :
    ∃! coefficient : ZeroMode → Real,
      finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)
        coefficient = vector := by
  obtain ⟨coefficient, hCoefficient⟩ :=
    projectedKernelSynthesis_zero_surjective period hPeriod input natural vector
  refine ⟨coefficient, hCoefficient, ?_⟩
  intro other hOther
  exact projectedKernelSynthesis_zero_injective' period hPeriod input natural
    (hOther.trans hCoefficient.symm)

/-- Public completeness checkpoint: at H12 the actual kernel is exactly the
finite span of the projected physical action-generated modes, with unique
coordinates. -/
theorem projected_kernel_completeness_basepoint_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Bijective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)) ∧
    (∀ vector : (input.familyIndex.baseFamily.actualOperator 0).ker,
      ∃! coefficient : ZeroMode → Real,
        finiteFamilySynthesis
          (projectedKernelSubtypeVector period hPeriod input natural 0)
          coefficient = vector) :=
  ⟨projectedKernelSynthesis_zero_bijective period hPeriod input natural,
    existsUnique_projectedKernelCoordinates_zero period hPeriod input natural⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCompletenessBasepoint4D
end JanusFormal
