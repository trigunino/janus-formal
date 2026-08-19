import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramBasis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D

/-!
# Gram criterion for completeness of the projected physical kernel family

The projected vectors

`e~_i(a) = P_{s(i)} e_i(a)`

are already genuine sector-pure zero modes.  Their completeness is reduced here
to one finite Gram condition at every parameter.

Work inside the actual kernel subtype.  If the Gram endomorphism of the
projected vectors is injective, their synthesis map is injective.  The existing
named kernel basis already proves

`finrank ker H_a = card ZeroMode`,

so finite-dimensional rank equality makes synthesis bijective and yields the
preferred projected physical basis automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
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
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
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

/-- Projected physical vector regarded as an element of the true kernel
subtype. -/
def projectedKernelSubtypeVector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    (input.familyIndex.baseFamily.actualOperator parameter).ker :=
  ⟨projectedNamedKernelVector period hPeriod input parameter mode,
    LinearMap.mem_ker.mpr
      (projectedNamedKernelVector_mem_kernel period hPeriod input natural
        parameter mode)⟩

/-- Gram endomorphism of the projected physical zero modes at one parameter. -/
def projectedKernelGramMap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) :
    (ZeroMode → Real) →ₗ[Real] (ZeroMode → Real) :=
  by
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
    exact @finiteFamilyGramMap ZeroMode
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) inferInstance hNormed hInner
      (fun mode => projectedNamedKernelVector period hPeriod input parameter mode)

/-- Exact scalar finite-dimensional completeness premise. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Prop where
  gram_injective : ∀ parameter,
    Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter)

namespace GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D

theorem projectedKernelSubtypeVector_linearIndependent_of_gram_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter)) :
    LinearIndependent Real
      (projectedKernelSubtypeVector period hPeriod input natural parameter) := by
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
  have hAmbient := @finiteFamily_linearIndependent_of_gram_injective ZeroMode
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance hNormed hInner
    (fun mode => projectedNamedKernelVector period hPeriod input parameter mode)
    (by simpa [projectedKernelGramMap] using hGram)
  let inclusion : @LinearMap Real Real _ _ (RingHom.id Real)
      (input.familyIndex.baseFamily.actualOperator parameter).ker
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (input.familyIndex.baseFamily.actualOperator parameter).ker.addCommMonoid
      hNormed.toAddCommMonoid
      (input.familyIndex.baseFamily.actualOperator parameter).ker.module
      hInner.toModule :=
    @LinearMap.mk Real Real _ _ (RingHom.id Real) _ _
      (input.familyIndex.baseFamily.actualOperator parameter).ker.addCommMonoid
      hNormed.toAddCommMonoid
      (input.familyIndex.baseFamily.actualOperator parameter).ker.module
      hInner.toModule
      (@AddHom.mk _ _
        (input.familyIndex.baseFamily.actualOperator parameter).ker.addCommMonoid.toAdd
        hNormed.toAddCommMonoid.toAdd
        (fun vector => vector.1) (by intro first second; rfl))
      (by intro scalar vector; rfl)
  apply @LinearIndependent.of_comp ZeroMode Real
    (input.familyIndex.baseFamily.actualOperator parameter).ker
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (projectedKernelSubtypeVector period hPeriod input natural parameter)
    _
    (input.familyIndex.baseFamily.actualOperator parameter).ker.addCommMonoid
    hNormed.toAddCommMonoid
    (input.familyIndex.baseFamily.actualOperator parameter).ker.module
    hInner.toModule inclusion
  simpa [Function.comp_def, inclusion, projectedKernelSubtypeVector] using
    hAmbient

def projectedKernelBasisAtOfGramInjective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter)) :
    Module.Basis ZeroMode Real
      (input.familyIndex.baseFamily.actualOperator parameter).ker := by
  letI : Module.Finite Real
      (input.familyIndex.baseFamily.actualOperator parameter).ker :=
    Module.Finite.of_basis (input.kernels.basis parameter)
  exact basisOfLinearIndependentOfCardEqFinrank'
    (projectedKernelSubtypeVector period hPeriod input natural parameter)
    (projectedKernelSubtypeVector_linearIndependent_of_gram_injective period
      hPeriod input natural parameter hGram)
    (input.kernels.kernel_finrank_eq_card parameter).symm

@[simp]
theorem projectedKernelBasisAtOfGramInjective_apply
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (hGram : Function.Injective
      (projectedKernelGramMap period hPeriod input natural parameter))
    (mode : ZeroMode) :
    ((projectedKernelBasisAtOfGramInjective period hPeriod input natural parameter
        hGram mode).1) =
      projectedNamedKernelVector period hPeriod input parameter mode := by
  unfold projectedKernelBasisAtOfGramInjective
  simp [projectedKernelSubtypeVector]

private def projectedKernelBasisAt
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gram : GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural)
    (parameter : Real) :
    Module.Basis ZeroMode Real
      (input.familyIndex.baseFamily.actualOperator parameter).ker :=
  projectedKernelBasisAtOfGramInjective period hPeriod input natural parameter
    (gram.gram_injective parameter)

@[simp]
private theorem projectedKernelBasisAt_apply
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gram : GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    ((projectedKernelBasisAt period hPeriod input natural gram parameter mode).1) =
      projectedNamedKernelVector period hPeriod input parameter mode :=
  projectedKernelBasisAtOfGramInjective_apply period hPeriod input natural
    parameter (gram.gram_injective parameter) mode

/-- Gram nondegeneracy constructs the complete physical projected kernel basis
at every parameter. -/
def toProjectedKernelBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gram : GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural where
  basis := projectedKernelBasisAt period hPeriod input natural gram
  basis_agreement := by
    intro parameter mode
    exact projectedKernelBasisAt_apply period hPeriod input natural gram
      parameter mode

/-- Public projected-kernel Gram checkpoint. -/
theorem projected_kernel_gram_nondegenerate_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gram : GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural) :
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) :=
  ⟨gram.toProjectedKernelBasisFamily period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
end JanusFormal
