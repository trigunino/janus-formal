import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D

/-!
# Basepoint nondegeneracy of the projected physical kernel Gram operator

At `a = 0` the projected physical vectors are exactly the existing H12 named
kernel basis.  Their coefficient synthesis therefore has the ordinary basis
coordinate map as a left inverse.  It is injective, hence the Gram operator is
injective.

Thus the new projected-kernel Gram condition is not an extra basepoint premise;
only its persistence away from `a = 0` remains to be proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D

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
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
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

/-- At the basepoint the projected kernel subtype vector is exactly the old
H12 basis vector. -/
theorem projectedKernelSubtypeVector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (mode : ZeroMode) :
    projectedKernelSubtypeVector period hPeriod input natural 0 mode =
      input.kernels.basis 0 mode := by
  apply Subtype.ext
  change projectedNamedKernelVector period hPeriod input 0 mode =
    input.kernels.vector 0 mode
  exact projectedNamedKernelVector_zero period hPeriod input mode

/-- Basis coordinates are a left inverse of coefficient synthesis for the old
H12 basis vectors. -/
theorem basepointBasis_synthesis_leftInverse
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (coefficient : ZeroMode → Real) :
    (input.kernels.basis 0).equivFun
        (finiteFamilySynthesis (fun mode => input.kernels.basis 0 mode)
          coefficient) = coefficient := by
  ext mode
  simp [finiteFamilySynthesis]

/-- Coefficient synthesis of the old H12 basis is injective. -/
theorem basepointBasis_synthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Function.Injective
      (finiteFamilySynthesis (fun mode => input.kernels.basis 0 mode)) := by
  intro first second hEqual
  have hCoordinates := congrArg (input.kernels.basis 0).equivFun hEqual
  simpa [basepointBasis_synthesis_leftInverse] using hCoordinates

/-- Projected physical coefficient synthesis is injective at the H12 basepoint. -/
theorem projectedKernelSynthesis_zero_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (finiteFamilySynthesis
        (projectedKernelSubtypeVector period hPeriod input natural 0)) := by
  have hFamily :
      (fun mode => projectedKernelSubtypeVector period hPeriod input natural 0 mode) =
        fun mode => input.kernels.basis 0 mode := by
    funext mode
    exact projectedKernelSubtypeVector_zero period hPeriod input natural mode
  rw [hFamily]
  exact basepointBasis_synthesis_injective period hPeriod input

/-- The projected physical Gram operator is injective at parameter zero. -/
theorem projectedKernelGram_zero_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (projectedKernelGramMap period hPeriod input natural 0) := by
  unfold projectedKernelGramMap
  exact finiteFamilyGramMap_injective_of_synthesis_injective
    (projectedKernelSubtypeVector period hPeriod input natural 0)
    (projectedKernelSynthesis_zero_injective period hPeriod input natural)

/-- Public basepoint Gram checkpoint. -/
theorem projected_kernel_gram_basepoint_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (projectedKernelGramMap period hPeriod input natural 0) :=
  projectedKernelGram_zero_injective period hPeriod input natural

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
end JanusFormal
