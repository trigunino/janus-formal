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
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
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

/-- The projected physical Gram operator is injective at parameter zero. -/
theorem projectedKernelGram_zero_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (projectedKernelGramMap period hPeriod input natural 0) := by
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
  let inclusion : @LinearMap Real Real _ _ (RingHom.id Real)
      (input.familyIndex.baseFamily.actualOperator 0).ker
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (input.familyIndex.baseFamily.actualOperator 0).ker.addCommMonoid
      hNormed.toAddCommMonoid
      (input.familyIndex.baseFamily.actualOperator 0).ker.module
      hInner.toModule :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real) _ _
      (input.familyIndex.baseFamily.actualOperator 0).ker.addCommMonoid
      hNormed.toAddCommMonoid
      (input.familyIndex.baseFamily.actualOperator 0).ker.module
      hInner.toModule
      (@AddHom.mk _ _
        (input.familyIndex.baseFamily.actualOperator 0).ker.addCommMonoid.toAdd
        hNormed.toAddCommMonoid.toAdd
        (fun vector => vector.1) (by intro first second; rfl))
      (by intro scalar vector; rfl)
  have hMapped := @LinearIndependent.map' ZeroMode Real
    (input.familyIndex.baseFamily.actualOperator 0).ker
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (fun mode => input.kernels.basis 0 mode) _
    (input.familyIndex.baseFamily.actualOperator 0).ker.addCommGroup
    hNormed.toAddCommGroup
    (input.familyIndex.baseFamily.actualOperator 0).ker.module hInner.toModule
    (input.kernels.basis 0).linearIndependent inclusion
    (LinearMap.ker_eq_bot.mpr fun first second hEqual => Subtype.ext hEqual)
  have hFamily :
      (inclusion ∘ fun mode => input.kernels.basis 0 mode) =
        fun mode => projectedNamedKernelVector period hPeriod input 0 mode := by
    funext mode
    change input.kernels.vector 0 mode =
      projectedNamedKernelVector period hPeriod input 0 mode
    exact (projectedNamedKernelVector_zero period hPeriod input mode).symm
  rw [hFamily] at hMapped
  simpa [projectedKernelGramMap] using
    (@finiteFamilyGramMap_injective_of_linearIndependent ZeroMode
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) inferInstance inferInstance hNormed hInner
      (fun mode => projectedNamedKernelVector period hPeriod input 0 mode)
      hMapped)

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
