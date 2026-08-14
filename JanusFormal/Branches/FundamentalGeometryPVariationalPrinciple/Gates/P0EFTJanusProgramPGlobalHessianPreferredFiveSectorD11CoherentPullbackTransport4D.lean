import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D

/-!
# Candidate-A transport from coherent represented D11 pullbacks

For the preferred Candidate-A representation, identity and composition of the
linear ambient transport are now derived rather than supplied.  The remaining
D11 family datum consists of

* coherent reverse admissible morphisms between the represented objects;
* one represented real-linear equivalence agreeing with source and target
  pullback;
* C1 dependence of the exact H12 generators under that equivalence.

Section-functor laws generate the transport cocycle.  The preceding D11 linear
transport closure then supplies operator intertwining, physical-sector
commutation, true-kernel transport and the global sector-pure C1 kernel family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D

set_option autoImplicit false
set_option maxHeartbeats 86000000
set_option synthInstance.maxHeartbeats 43000000
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
open P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
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

/-- Candidate-A represented D11 pullbacks with morphism-level coherence and C1
transport of the H12 basis. -/
structure GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  coherentPullback :
    CoherentLinearNaturalRepresentationPullbackTransportData
      (operator := input.familyIndex.baseFamily.actualOperator)
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        coherentPullback.transport 0 parameter
          (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D

/-- Upgrade coherent represented pullbacks to the full Candidate-A D11 linear
transport packet. -/
def toD11LinearPullbackTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
      period hPeriod input natural where
  linearPullback :=
    coherent.coherentPullback.toLinearNaturalRepresentationIsomorphismTransport
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable :=
    coherent.transported_vector_differentiable

/-- Coherent D11 pullbacks construct the global sector-pure actual-kernel
family. -/
def physicalKernels
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    FiniteKernelBasisFamilyData
      input.familyIndex.baseFamily.actualOperator ZeroMode :=
  (coherent.toD11LinearPullbackTransport period hPeriod input natural).
    physicalKernels period hPeriod input natural

/-- Coherent D11 pullbacks rebuild the existing family-index closure with the
transported physical basis. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (coherent.toD11LinearPullbackTransport period hPeriod input natural).
    physicalNamedKernelFamilyClosure period hPeriod input natural

/-- Coherent D11 pullbacks give a sector-resolved physical closure. -/
def physicalResolvedKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (coherent.physicalNamedKernelFamilyClosure period hPeriod input natural) :=
  (coherent.toD11LinearPullbackTransport period hPeriod input natural).
    physicalResolvedKernelFamily period hPeriod input natural

/-- Coherent D11 pullbacks give C1 ambient zero modes. -/
def physicalRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (coherent.physicalNamedKernelFamilyClosure period hPeriod input natural) :=
  (coherent.toD11LinearPullbackTransport period hPeriod input natural).
    physicalRegularity period hPeriod input natural

/-- Public coherent Candidate-A D11 pullback checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_coherent_pullback_transport_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coherent :
      GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
        period hPeriod input natural) :
    (∀ parameter,
      coherent.coherentPullback.transport parameter parameter =
        LinearEquiv.refl Real _) ∧
    (∀ first second third,
      (coherent.coherentPullback.transport second third).comp
          (coherent.coherentPullback.transport first second) =
        coherent.coherentPullback.transport first third) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (coherent.physicalNamedKernelFamilyClosure period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (coherent.physicalNamedKernelFamilyClosure period hPeriod input natural) :=
  ⟨coherent.coherentPullback.transport_self
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback,
    coherent.coherentPullback.transport_trans
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback,
    coherent.physicalResolvedKernelFamily period hPeriod input natural,
    coherent.physicalRegularity period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
end JanusFormal