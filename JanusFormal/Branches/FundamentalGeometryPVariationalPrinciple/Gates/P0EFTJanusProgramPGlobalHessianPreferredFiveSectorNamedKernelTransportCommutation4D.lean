import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D

/-!
# Sector commutation of the existing named-kernel transport

The existing fixed-label kernel family already carries canonical coordinate
transport, exact identity/composition laws and C1 ambient basis vectors.  Hence
the general sector-preserving transport route reduces, for this selected family,
to one equation:

`T_ab P_s,a = P_s,b T_ab`.

If that equation holds, transporting the sector-resolved H12 basis is exactly
the already selected named basis at every parameter.  The existing named-kernel
family is therefore sector-resolved globally, with no projection, Gram
condition, replacement family or additional regularity premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D

set_option autoImplicit false
set_option maxHeartbeats 72000000
set_option synthInstance.maxHeartbeats 36000000
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
open P0EFTJanusProgramPFiniteSectorPreservingKernelTransport4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalKernelResolution4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
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

/-- The coordinate-preserving transport of the existing named basis commutes
with every natural physical kernel projector. -/
structure GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Prop where
  kernelTransport_commutes : ∀ first second sector vector,
    input.kernels.kernelTransport first second
        (naturalCandidateAKernelProjection period hPeriod input natural first
          sector vector) =
      naturalCandidateAKernelProjection period hPeriod input natural second
        sector (input.kernels.kernelTransport first second vector)

namespace GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D

/-- The existing kernel transport satisfies the full sector-preserving C1
transport interface. -/
def toSectorPreservingKernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
      period hPeriod input natural where
  transport := input.kernels.kernelTransport
  transport_self := input.kernels.kernelTransport_self
  transport_trans := input.kernels.kernelTransport_trans
  transport_commutes := commutation.kernelTransport_commutes
  transported_vector_differentiable := by
    intro mode
    convert regularity.vector_differentiable mode using 1
    funext parameter
    have hTransport :=
      input.kernels.kernelTransport_basis 0 parameter mode
    exact congrArg Subtype.val hTransport

/-- The named basis at every parameter is exactly the H12 basis transported by
its own coordinate transport. -/
theorem transportedBasis_eq_namedBasis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural)
    (parameter : Real) :
    ((commutation.toSectorPreservingKernelTransport period hPeriod input natural
      regularity).physicalKernels period hPeriod input natural).basis parameter =
      input.kernels.basis parameter := by
  ext mode
  change input.kernels.kernelTransport 0 parameter
      (input.kernels.basis 0 mode) = input.kernels.basis parameter mode
  exact input.kernels.kernelTransport_basis 0 parameter mode

/-- Commutation of the existing coordinate transport forces every selected
named basis vector to remain in its assigned physical sector. -/
def toResolvedKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input where
  basis_fixed_by_sector := by
    intro parameter mode
    have hCommute := commutation.kernelTransport_commutes 0 parameter
      (namedModeFiveSector period hPeriod input mode)
      (input.kernels.basis 0 mode)
    rw [basepointKernelBasis_fixed_by_sector period hPeriod input natural mode]
      at hCommute
    rw [input.kernels.kernelTransport_basis 0 parameter mode] at hCommute
    exact (congrArg Subtype.val hCommute).symm

/-- Under transport commutation the projected candidate is exactly the existing
named basis vector at every parameter. -/
theorem projectedNamedKernelVector_eq_namedVector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
        sectorProjector (namedModeFiveSector period hPeriod input mode)
        (input.kernels.vector parameter mode) =
      input.kernels.vector parameter mode :=
  (commutation.toResolvedKernelFamily period hPeriod input natural).
    basis_fixed_by_sector parameter mode

/-- Public existing-kernel-transport commutation checkpoint. -/
theorem global_hessian_preferred_five_sector_named_kernel_transport_commutation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod input ∧
    (∀ parameter,
      ((commutation.toSectorPreservingKernelTransport period hPeriod input natural
        regularity).physicalKernels period hPeriod input natural).basis parameter =
        input.kernels.basis parameter) ∧
    (∀ parameter mode,
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector (namedModeFiveSector period hPeriod input mode)
          (input.kernels.vector parameter mode) =
        input.kernels.vector parameter mode) :=
  ⟨commutation.toResolvedKernelFamily period hPeriod input natural,
    commutation.transportedBasis_eq_namedBasis period hPeriod input natural
      regularity,
    commutation.projectedNamedKernelVector_eq_namedVector period hPeriod input
      natural⟩

end GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
end JanusFormal