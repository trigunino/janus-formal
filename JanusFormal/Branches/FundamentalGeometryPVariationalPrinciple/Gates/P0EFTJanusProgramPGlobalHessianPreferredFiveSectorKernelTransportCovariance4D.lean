import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D

/-!
# Sector covariance of the canonical named-kernel transport

The physical sector of every named zero mode is known at the H12 basepoint.
The all-parameter D11 factorization makes each physical projector preserve the
kernel of every `H_a`.

It therefore remains only to require compatibility of the existing canonical
kernel transport with those fixed projectors.  Once

`T_ab P_s = P_s T_ab`

holds on the actual kernels, the basepoint sector resolution transports to all
parameters automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorKernelTransportCovariance4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

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
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Project a genuine zero mode to one physical sector; family-wide operator
commutation proves that the result is still a genuine zero mode. -/
def projectedKernelVector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).ker) :
    (input.familyIndex.baseFamily.actualOperator parameter).ker := by
  refine ⟨(Coordinates period hPeriod input).sectorProjector sector vector.1, ?_⟩
  apply LinearMap.mem_ker.mpr
  rw [actualOperator_commutes_sectorProjector period hPeriod input natural
    parameter sector vector.1]
  rw [LinearMap.mem_ker.mp vector.2]
  simp

/-- Compatibility of the existing named-basis kernel transport with the fixed
physical projectors. -/
structure GlobalHessianPreferredFiveSectorKernelTransportCovariance4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Prop where
  transport_commutes : ∀ first second sector vector,
    (input.kernels.kernelTransport first second
        (projectedKernelVector period hPeriod input natural first sector vector)).1 =
      (Coordinates period hPeriod input).sectorProjector sector
        (input.kernels.kernelTransport first second vector).1

namespace GlobalHessianPreferredFiveSectorKernelTransportCovariance4D

/-- Transport covariance plus the H12 basepoint sector theorem generates the
strong sector-resolved kernel family at every parameter. -/
def toResolvedKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (covariance : GlobalHessianPreferredFiveSectorKernelTransportCovariance4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input where
  basis_fixed_by_sector := by
    intro parameter mode
    let sector := namedModeFiveSector period hPeriod input mode
    let baseVector := input.kernels.basis 0 mode
    have hBase := basis_fixed_by_sector_zero period hPeriod input mode
    have hProjected :
        projectedKernelVector period hPeriod input natural 0 sector baseVector =
          baseVector := by
      apply Subtype.ext
      simpa [sector, FiniteKernelBasisFamilyData.vector] using hBase
    have hTransport := covariance.transport_commutes 0 parameter sector baseVector
    rw [hProjected, input.kernels.kernelTransport_basis 0 parameter mode]
      at hTransport
    simpa [FiniteKernelBasisFamilyData.vector, sector] using hTransport.symm

/-- Public reduction of dynamic kernel-sector resolution to transport
covariance. -/
theorem kernel_transport_covariance_resolves_sectors_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (covariance : GlobalHessianPreferredFiveSectorKernelTransportCovariance4D
      period hPeriod input natural) :
    Nonempty
      (GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod input) :=
  ⟨covariance.toResolvedKernelFamily period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorKernelTransportCovariance4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorKernelTransportCovariance4D
end JanusFormal
