import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPreservingKernelTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalKernelResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D

/-!
# Global physical kernel family from sector-preserving transport

The projected-Gram route starts with an arbitrary moving named basis and asks
whether its physical projections remain complete.  There is a second, more
geometric route: transport the already sector-resolved H12 basis directly
through the true kernel bundle.

This file isolates the exact required datum.  A coherent family of linear
kernel equivalences must commute with the canonical five physical kernel
projectors, and the transported H12 basis vectors must be differentiable in the
fixed ambient Candidate-A Hilbert space.

Under those conditions the transported vectors are automatically a basis of
every actual kernel, remain sector-pure at every parameter, agree with the
action generators at `a = 0`, and rebuild the existing named-kernel family
closure with the same family-index, heat, zeta and spectral-cut data.  No Gram
nondegeneracy or angle estimate is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D

set_option autoImplicit false
set_option maxHeartbeats 68000000
set_option synthInstance.maxHeartbeats 34000000
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
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiniteSectorPreservingKernelTransport4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalKernelResolution4D
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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Coherent sector-preserving C1 transport of the genuine Candidate-A kernel
fibres. -/
structure GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  transport : ∀ first second,
    (input.familyIndex.baseFamily.actualOperator first).ker ≃ₗ[Real]
      (input.familyIndex.baseFamily.actualOperator second).ker
  transport_self : ∀ parameter,
    transport parameter parameter = LinearEquiv.refl Real _
  transport_trans : ∀ first second third,
    (transport second third).comp (transport first second) =
      transport first third
  transport_commutes : ∀ first second sector vector,
    transport first second
        (naturalCandidateAKernelProjection period hPeriod input natural first
          sector vector) =
      naturalCandidateAKernelProjection period hPeriod input natural second
        sector (transport first second vector)
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        (transport 0 parameter (input.kernels.basis 0 mode)).1)

namespace GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D

/-- Adapter to the generic sector-preserving kernel-transport mechanism. -/
def toFiniteSectorPreservingKernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    FiniteSectorPreservingKernelTransportData
      input.familyIndex.baseFamily.actualOperator
      (naturalCandidateAKernelProjection period hPeriod input natural) where
  transport := transportData.transport
  transport_self := transportData.transport_self
  transport_trans := transportData.transport_trans
  transport_commutes := transportData.transport_commutes

/-- Global sector-pure basis family obtained by transporting the exact H12
basis. -/
def physicalKernels
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    FiniteKernelBasisFamilyData
      input.familyIndex.baseFamily.actualOperator ZeroMode :=
  (transportData.toFiniteSectorPreservingKernelTransport period hPeriod input
    natural).toFiniteKernelBasisFamily (input.kernels.basis 0)

/-- The transported physical basis is fixed by the assigned physical kernel
projector at every parameter. -/
theorem physicalKernels_basis_fixed_by_sector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    naturalCandidateAKernelProjection period hPeriod input natural parameter
        (namedModeFiveSector period hPeriod input mode)
        ((transportData.physicalKernels period hPeriod input natural).basis
          parameter mode) =
      (transportData.physicalKernels period hPeriod input natural).basis
        parameter mode :=
  (transportData.toFiniteSectorPreservingKernelTransport period hPeriod input
    natural).transportedBasis_fixed_by_sector
      (input.kernels.basis 0)
      (namedModeFiveSector period hPeriod input)
      (basepointKernelBasis_fixed_by_sector period hPeriod input natural)
      parameter mode

/-- The transported physical basis agrees exactly with the original H12 basis
at parameter zero. -/
theorem physicalKernels_basis_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    (transportData.physicalKernels period hPeriod input natural).basis 0 =
      input.kernels.basis 0 :=
  (transportData.toFiniteSectorPreservingKernelTransport period hPeriod input
    natural).transportedBasis_zero (input.kernels.basis 0)

/-- Rebuild the existing Candidate-A named-kernel family closure using the
transported sector-pure basis while retaining every family-index datum. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index where
  familyIndex := input.familyIndex
  kernels := transportData.physicalKernels period hPeriod input natural
  basis_zero_agreement := by
    intro mode
    rw [transportData.physicalKernels_basis_zero period hPeriod input natural]
    exact input.basis_zero_agreement mode

/-- The transported physical closure is sector-resolved at every parameter. -/
def physicalResolvedKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (transportData.physicalNamedKernelFamilyClosure period hPeriod input
          natural) where
  basis_fixed_by_sector := by
    intro parameter mode
    have hFixed := transportData.physicalKernels_basis_fixed_by_sector period
      hPeriod input natural parameter mode
    exact congrArg Subtype.val hFixed

/-- The transported basis vectors form the standard differentiable named-kernel
family in the fixed ambient Hilbert space. -/
def physicalRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (transportData.physicalNamedKernelFamilyClosure period hPeriod input
          natural) where
  vector_differentiable := transportData.transported_vector_differentiable

/-- The rebuilt physical closure has the same exact action generators at H12. -/
theorem physical_vector_zero_eq_actionGenerator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural)
    (mode : ZeroMode) :
    (transportData.physicalNamedKernelFamilyClosure period hPeriod input natural).
        kernels.vector 0 mode =
      input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
        closure.frontier.generators.translations.vector mode :=
  (transportData.physicalNamedKernelFamilyClosure period hPeriod input natural).
    vector_zero_eq_actionGenerator period hPeriod mode

/-- Public global sector-preserving kernel-transport checkpoint. -/
theorem global_hessian_preferred_five_sector_sector_preserving_kernel_transport_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (transportData :
      GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
        period hPeriod input natural) :
    (∀ parameter mode,
      naturalCandidateAKernelProjection period hPeriod input natural parameter
          (namedModeFiveSector period hPeriod input mode)
          ((transportData.physicalKernels period hPeriod input natural).basis
            parameter mode) =
        (transportData.physicalKernels period hPeriod input natural).basis
          parameter mode) ∧
    ((transportData.physicalKernels period hPeriod input natural).basis 0 =
      input.kernels.basis 0) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (transportData.physicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (transportData.physicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    (∀ mode,
      (transportData.physicalNamedKernelFamilyClosure period hPeriod input natural).
          kernels.vector 0 mode =
        input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
          closure.frontier.generators.translations.vector mode) :=
  ⟨transportData.physicalKernels_basis_fixed_by_sector period hPeriod input natural,
    transportData.physicalKernels_basis_zero period hPeriod input natural,
    transportData.physicalResolvedKernelFamily period hPeriod input natural,
    transportData.physicalRegularity period hPeriod input natural,
    transportData.physical_vector_zero_eq_actionGenerator period hPeriod input
      natural⟩

end GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
end JanusFormal