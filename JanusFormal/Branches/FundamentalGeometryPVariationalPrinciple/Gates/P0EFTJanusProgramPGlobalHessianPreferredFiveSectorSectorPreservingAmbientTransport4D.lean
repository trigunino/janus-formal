import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D

/-!
# Global physical kernel family from ambient Candidate-A transport

A linearized geometric transport naturally acts on the common ambient
Candidate-A Hilbert space before it is restricted to zero modes.  This file
states the exact ambient conditions needed for the kernel construction:

* coherent linear equivalences `U_ab`;
* operator intertwining `H_b U_ab = U_ab H_a`;
* commutation with every fixed physical projector `P_s`;
* C1 dependence of the transported H12 generators.

The generic intertwining theorem restricts `U_ab` to the true kernels.  Ambient
projector commutation then becomes commutation with the canonical restricted
kernel projectors, so the sector-preserving kernel-transport closure applies
without any additional finite-dimensional premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalKernelResolution4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  candidateAHilbertNormedAddCommGroup
  candidateAHilbertInnerProductSpace
  candidateAHilbertNormedSpace
  candidateAHilbertModule
  candidateAHilbertCompleteSpace

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

private abbrev Ambient
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
    configuration data analysis

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Coherent sector-preserving ambient transport intertwining the actual
Candidate-A operator family. -/
structure GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  transport : ∀ first second,
    Ambient period hPeriod configuration data analysis ≃ₗ[Real]
      Ambient period hPeriod configuration data analysis
  transport_self : ∀ parameter,
    transport parameter parameter = LinearEquiv.refl Real _
  transport_trans : ∀ first second third,
    (transport first second).trans (transport second third) =
      transport first third
  operator_intertwining : ∀ first second vector,
    input.familyIndex.baseFamily.actualOperator second
        (transport first second vector) =
      transport first second
        (input.familyIndex.baseFamily.actualOperator first vector)
  sector_commutation : ∀ first second sector vector,
    transport first second
        ((Coordinates period hPeriod input).sectorProjector sector vector) =
      (Coordinates period hPeriod input).sectorProjector sector
        (transport first second vector)
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        transport 0 parameter (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D

/-- Adapter to the generic ambient intertwining package. -/
def toFiniteIntertwiningOperatorTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural) :
    FiniteIntertwiningOperatorTransportData
      input.familyIndex.baseFamily.actualOperator where
  transport := ambientTransport.transport
  transport_self := ambientTransport.transport_self
  transport_trans := ambientTransport.transport_trans
  intertwines := ambientTransport.operator_intertwining

/-- Ambient transport restricted to the actual kernel fibres. -/
def kernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural)
    (first second : Real) :
    (input.familyIndex.baseFamily.actualOperator first).ker ≃ₗ[Real]
      (input.familyIndex.baseFamily.actualOperator second).ker :=
  (ambientTransport.toFiniteIntertwiningOperatorTransport period hPeriod input
    natural).kernelTransport first second

/-- Restricted kernel transport commutes with the canonical physical kernel
projectors. -/
theorem kernelTransport_commutes
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural)
    (first second : Real) (sector : FivePhysicalSector)
    (vector : (input.familyIndex.baseFamily.actualOperator first).ker) :
    ambientTransport.kernelTransport period hPeriod input natural first second
        (naturalCandidateAKernelProjection period hPeriod input natural first
          sector vector) =
      naturalCandidateAKernelProjection period hPeriod input natural second
        sector
        (ambientTransport.kernelTransport period hPeriod input natural first
          second vector) := by
  apply Subtype.ext
  change ambientTransport.transport first second
      ((Coordinates period hPeriod input).sectorProjector sector vector.1) =
    (Coordinates period hPeriod input).sectorProjector sector
      (ambientTransport.transport first second vector.1)
  exact ambientTransport.sector_commutation first second sector vector.1

/-- The ambient transport induces the complete sector-preserving C1 kernel
transport packet. -/
def toSectorPreservingKernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
      period hPeriod input natural where
  transport := ambientTransport.kernelTransport period hPeriod input natural
  transport_self :=
    (ambientTransport.toFiniteIntertwiningOperatorTransport period hPeriod input
      natural).kernelTransport_self
  transport_trans :=
    (ambientTransport.toFiniteIntertwiningOperatorTransport period hPeriod input
      natural).kernelTransport_trans
  transport_commutes := ambientTransport.kernelTransport_commutes period hPeriod
    input natural
  transported_vector_differentiable := by
    intro mode
    exact ambientTransport.transported_vector_differentiable mode

/-- Sector-preserving ambient transport constructs the global physical kernel
basis. -/
def toPhysicalKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural) :
    FiniteKernelBasisFamilyData input.familyIndex.baseFamily.actualOperator
      ZeroMode :=
  (ambientTransport.toSectorPreservingKernelTransport period hPeriod input
    natural).physicalKernels period hPeriod input natural

/-- Sector-preserving ambient transport rebuilds the same family-index closure
with a sector-pure C1 kernel basis. -/
def toPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (ambientTransport.toSectorPreservingKernelTransport period hPeriod input
    natural).physicalNamedKernelFamilyClosure period hPeriod input natural

/-- Public ambient-transport closure checkpoint. -/
theorem global_hessian_preferred_five_sector_sector_preserving_ambient_transport_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (ambientTransport :
      GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
        period hPeriod input natural) :
    (∀ first second vector,
      input.familyIndex.baseFamily.actualOperator second
          (ambientTransport.transport first second vector) =
        ambientTransport.transport first second
          (input.familyIndex.baseFamily.actualOperator first vector)) ∧
    (∀ first second sector vector,
      ambientTransport.kernelTransport period hPeriod input natural first second
          (naturalCandidateAKernelProjection period hPeriod input natural first
            sector vector) =
        naturalCandidateAKernelProjection period hPeriod input natural second
          sector
          (ambientTransport.kernelTransport period hPeriod input natural first
            second vector)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (ambientTransport.toPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (ambientTransport.toPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨ambientTransport.operator_intertwining,
    ambientTransport.kernelTransport_commutes period hPeriod input natural,
    (ambientTransport.toSectorPreservingKernelTransport period hPeriod input
      natural).physicalResolvedKernelFamily period hPeriod input natural,
    (ambientTransport.toSectorPreservingKernelTransport period hPeriod input
      natural).physicalRegularity period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
end JanusFormal
