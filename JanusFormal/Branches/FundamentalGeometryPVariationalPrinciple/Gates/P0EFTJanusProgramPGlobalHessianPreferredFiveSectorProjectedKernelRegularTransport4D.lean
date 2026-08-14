import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D

/-!
# Canonical physical kernel transport on the regular Gram chart

The open projected-kernel regular set carries a basis of the actual kernel at
every point.  The fixed `ZeroMode` labels therefore produce the same canonical
coordinate transport as the global finite-kernel architecture, now without an
unproved all-parameter nondegeneracy assumption.

For regular parameters `a,b`, transport is

`B_a.equivFun >> B_b.equivFun.symm`.

It sends every projected sector-pure physical mode at `a` to the identically
labelled projected mode at `b`, is the identity on the diagonal, and composes
exactly on triples.  Thus the H12 neighbourhood now carries a genuine local
Fredholm kernel trivialization rather than only pointwise bases.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularTransport4D

set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option synthInstance.maxHeartbeats 25000000
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
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

/-- Canonical projected physical basis on one point of the open regular chart. -/
def regularProjectedKernelBasis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input) :
    Basis ZeroMode Real
      (input.familyIndex.baseFamily.actualOperator parameter.1).ker :=
  (projectedKernelBasisOnRegularSet period hPeriod input natural parameter).basis

/-- Ambient vector of the chart basis is exactly the canonical projected
sector-pure zero mode. -/
theorem regularProjectedKernelBasis_vector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input)
    (mode : ZeroMode) :
    (regularProjectedKernelBasis period hPeriod input natural parameter mode).1 =
      projectedNamedKernelVector period hPeriod input parameter.1 mode := by
  have hAgreement :=
    projectedKernelBasisOnRegularSet_agreement period hPeriod input natural
      parameter mode
  exact congrArg Subtype.val hAgreement

/-- Coordinates of one true zero mode in the chart basis. -/
def regularProjectedKernelAnalyze
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input) :
    (input.familyIndex.baseFamily.actualOperator parameter.1).ker →ₗ[Real]
      (ZeroMode → Real) :=
  (regularProjectedKernelBasis period hPeriod input natural parameter).equivFun.
    toLinearMap

/-- Synthesis of true zero modes from fixed physical coordinates on the chart. -/
def regularProjectedKernelSynthesize
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input) :
    (ZeroMode → Real) →ₗ[Real]
      (input.familyIndex.baseFamily.actualOperator parameter.1).ker :=
  (regularProjectedKernelBasis period hPeriod input natural parameter).equivFun.
    symm.toLinearMap

/-- Canonical local kernel transport: keep the fixed physical coordinates. -/
def regularProjectedKernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (first second : projectedKernelRegularSet period hPeriod input) :
    (input.familyIndex.baseFamily.actualOperator first.1).ker ≃ₗ[Real]
      (input.familyIndex.baseFamily.actualOperator second.1).ker :=
  (regularProjectedKernelBasis period hPeriod input natural first).equivFun.trans
    (regularProjectedKernelBasis period hPeriod input natural second).equivFun.symm

/-- Local transport sends each projected named mode to the identically labelled
projected named mode. -/
@[simp]
theorem regularProjectedKernelTransport_basis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (first second : projectedKernelRegularSet period hPeriod input)
    (mode : ZeroMode) :
    regularProjectedKernelTransport period hPeriod input natural first second
        (regularProjectedKernelBasis period hPeriod input natural first mode) =
      regularProjectedKernelBasis period hPeriod input natural second mode := by
  apply (regularProjectedKernelBasis period hPeriod input natural second).equivFun.
    injective
  simp [regularProjectedKernelTransport]

/-- Local transport is the identity on the diagonal. -/
@[simp]
theorem regularProjectedKernelTransport_self
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input) :
    regularProjectedKernelTransport period hPeriod input natural parameter
        parameter =
      LinearEquiv.refl Real _ := by
  ext zeroMode
  apply (regularProjectedKernelBasis period hPeriod input natural parameter).
    equivFun.injective
  simp [regularProjectedKernelTransport]

/-- Exact cocycle/composition law of the chart transports. -/
theorem regularProjectedKernelTransport_trans
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (first second third : projectedKernelRegularSet period hPeriod input) :
    (regularProjectedKernelTransport period hPeriod input natural second third).comp
        (regularProjectedKernelTransport period hPeriod input natural first
          second) =
      regularProjectedKernelTransport period hPeriod input natural first third := by
  ext zeroMode
  apply (regularProjectedKernelBasis period hPeriod input natural third).equivFun.
    injective
  simp [regularProjectedKernelTransport]

/-- Every local chart basis vector belongs to its assigned physical sector
kernel. -/
theorem regularProjectedKernelBasis_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : projectedKernelRegularSet period hPeriod input)
    (mode : ZeroMode) :
    (regularProjectedKernelBasis period hPeriod input natural parameter mode).1 ∈
      sectorKernel period hPeriod input parameter.1
        (namedModeFiveSector period hPeriod input mode) := by
  rw [regularProjectedKernelBasis_vector period hPeriod input natural]
  exact projectedNamedKernelVector_mem_sectorKernel period hPeriod input natural
    parameter.1 mode

/-- At the distinguished basepoint the local physical basis is the original
H12 action-generated named basis in the ambient Hilbert space. -/
theorem regularProjectedKernelBasis_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (mode : ZeroMode) :
    (regularProjectedKernelBasis period hPeriod input natural
      ⟨0, zero_mem_projectedKernelRegularSet period hPeriod input natural⟩ mode).1 =
      input.kernels.vector 0 mode := by
  rw [regularProjectedKernelBasis_vector period hPeriod input natural]
  exact projectedNamedKernelVector_zero period hPeriod input mode

/-- Public local Fredholm-kernel trivialization checkpoint. -/
theorem projected_kernel_regular_transport_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    (∀ parameter mode,
      (regularProjectedKernelBasis period hPeriod input natural parameter mode).1 ∈
        sectorKernel period hPeriod input parameter.1
          (namedModeFiveSector period hPeriod input mode)) ∧
    (∀ first second mode,
      regularProjectedKernelTransport period hPeriod input natural first second
          (regularProjectedKernelBasis period hPeriod input natural first mode) =
        regularProjectedKernelBasis period hPeriod input natural second mode) ∧
    (∀ first second third,
      (regularProjectedKernelTransport period hPeriod input natural second third).
          comp
          (regularProjectedKernelTransport period hPeriod input natural first
            second) =
        regularProjectedKernelTransport period hPeriod input natural first third) :=
  ⟨regularProjectedKernelBasis_mem_sectorKernel period hPeriod input natural,
    regularProjectedKernelTransport_basis period hPeriod input natural,
    regularProjectedKernelTransport_trans period hPeriod input natural⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularTransport4D
end JanusFormal
