import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D

/-!
# Projected-Gram closure from named transport commutation

When the existing named-kernel coordinate transport commutes with the natural
physical kernel projectors, every named basis vector is already sector-pure.
The canonical projected family is then literally the selected named basis.

Consequently its Gram determinant never crosses zero, the maximal projected
regular chart is all of `Real`, and the global projected-basis packet can be
chosen to be the existing kernel basis itself.  This identifies the transport
route and the projected-Gram route without adding a second family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportGramClosure4D

set_option autoImplicit false
set_option maxHeartbeats 76000000
set_option synthInstance.maxHeartbeats 38000000
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
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
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

/-- Under transport commutation the projected kernel subtype vector is exactly
the existing named basis vector. -/
theorem projectedKernelSubtypeVector_eq_namedBasis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    projectedKernelSubtypeVector period hPeriod input natural parameter mode =
      input.kernels.basis parameter mode := by
  apply Subtype.ext
  change projectedNamedKernelVector period hPeriod input parameter mode =
    input.kernels.vector parameter mode
  unfold projectedNamedKernelVector
  exact commutation.projectedNamedKernelVector_eq_namedVector period hPeriod input
    natural parameter mode

/-- The existing named basis itself supplies the global projected physical basis
packet. -/
def toProjectedKernelBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural where
  basis := input.kernels.basis
  basis_agreement := by
    intro parameter mode
    exact congrArg Subtype.val
      (commutation.projectedKernelSubtypeVector_eq_namedBasis period hPeriod input
        natural parameter mode).symm

/-- Named transport commutation closes the projected regular chart globally. -/
theorem projectedKernelRegularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  projectedKernelRegularSet_eq_univ_of_basisFamily period hPeriod input natural
    (commutation.toProjectedKernelBasisFamily period hPeriod input natural)

/-- Named transport commutation also supplies the former global Gram packet. -/
def toProjectedKernelGramNondegenerate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural :=
  projectedKernelGramNondegenerateOfBasisFamily period hPeriod input natural
    (commutation.toProjectedKernelBasisFamily period hPeriod input natural)

/-- The physical basis produced by the global continuation machinery is
pointwise the already selected named basis. -/
theorem projectedPhysicalBasis_eq_namedBasis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural)
    (parameter : Real) :
    (commutation.toProjectedKernelBasisFamily period hPeriod input natural).basis
        parameter = input.kernels.basis parameter :=
  rfl

/-- Public transport-to-Gram closure checkpoint. -/
theorem global_hessian_preferred_five_sector_named_kernel_transport_gram_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    (∀ parameter mode,
      projectedKernelSubtypeVector period hPeriod input natural parameter mode =
        input.kernels.basis parameter mode) ∧
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural ∧
    (∀ parameter,
      (commutation.toProjectedKernelBasisFamily period hPeriod input natural).basis
        parameter = input.kernels.basis parameter) :=
  ⟨commutation.projectedKernelSubtypeVector_eq_namedBasis period hPeriod input
      natural,
    commutation.projectedKernelRegularSet_eq_univ period hPeriod input natural,
    commutation.toProjectedKernelGramNondegenerate period hPeriod input natural,
    commutation.projectedPhysicalBasis_eq_namedBasis period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportGramClosure4D
end JanusFormal