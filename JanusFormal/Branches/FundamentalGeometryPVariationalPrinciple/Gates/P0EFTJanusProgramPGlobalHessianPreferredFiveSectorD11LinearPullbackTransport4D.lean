import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D

/-!
# Candidate-A kernel transport from linear D11 pullback isomorphisms

The preferred D11 representation already identifies its represented operator
with the genuine Candidate-A Hessian and proves that represented source and
target pullbacks preserve the five physical sectors.  This layer adds exactly
the missing groupoid-strength analytic datum: reverse represented pullbacks are
one coherent family of real-linear equivalences of the fixed Candidate-A
Hilbert space.

The generic D11 naturality theorem then produces ambient operator
intertwining, while the existing sector-covariance theorem produces projector
commutation.  After adding C1 dependence of the transported H12 generators,
the ambient transport restricts to the true kernels and constructs a global
sector-pure kernel basis, a resolved named-kernel family and its C1 regularity.

No Gram, determinant margin or replacement operator is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D

set_option autoImplicit false
set_option maxHeartbeats 82000000
set_option synthInstance.maxHeartbeats 41000000
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
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalKernelResolution4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
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

/-- Linear groupoid-strength realization of reverse D11 pullbacks, together with
C1 dependence of the transported exact H12 zero modes. -/
structure GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  linearPullback :
    LinearNaturalRepresentationIsomorphismTransportData
      (operator := input.familyIndex.baseFamily.actualOperator)
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        linearPullback.transport 0 parameter
          (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D

/-- D11 pullback isomorphisms produce the exact sector-preserving ambient
transport packet for the genuine Candidate-A Hessian. -/
def toSectorPreservingAmbientTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
      period hPeriod input natural where
  transport := d11Transport.linearPullback.transport
  transport_self := d11Transport.linearPullback.transport_self
  transport_trans := d11Transport.linearPullback.transport_trans
  operator_intertwining :=
    d11Transport.linearPullback.operator_intertwining
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  sector_commutation :=
    d11Transport.linearPullback.transport_commutes_sectorProjector
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable :=
    d11Transport.transported_vector_differentiable

/-- D11 pullback isomorphisms restrict to coherent sector-preserving
equivalences of the true Candidate-A kernels. -/
def toSectorPreservingKernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :=
  (d11Transport.toSectorPreservingAmbientTransport period hPeriod input natural).
    toSectorPreservingKernelTransport period hPeriod input natural

/-- Global physical actual-kernel family transported directly from the H12
basis by the represented D11 pullbacks. -/
def physicalKernels
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    FiniteKernelBasisFamilyData
      input.familyIndex.baseFamily.actualOperator ZeroMode :=
  (d11Transport.toSectorPreservingKernelTransport period hPeriod input natural).
    physicalKernels period hPeriod input natural

/-- Rebuild the existing family-index closure with the D11-transported physical
basis, retaining the same actual operator, heat, zeta and spectral-cut data. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (d11Transport.toSectorPreservingKernelTransport period hPeriod input natural).
    physicalNamedKernelFamilyClosure period hPeriod input natural

/-- The D11-transported closure is sector-resolved. -/
def physicalResolvedKernelFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (d11Transport.physicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (d11Transport.toSectorPreservingKernelTransport period hPeriod input natural).
    physicalResolvedKernelFamily period hPeriod input natural

/-- The D11-transported closure is C1 in the common ambient Hilbert space. -/
def physicalRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (d11Transport.physicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (d11Transport.toSectorPreservingKernelTransport period hPeriod input natural).
    physicalRegularity period hPeriod input natural

/-- Public Candidate-A linear D11 pullback transport checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_linear_pullback_transport_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    (∀ first second,
      AdmissibleMorphism
        natural.covariance.sectorRepresentation.bridge.immersionCategory
        (natural.covariance.sectorRepresentation.bridge.representation.objectAt
          second)
        (natural.covariance.sectorRepresentation.bridge.representation.objectAt
          first)) ∧
    (∀ first second state,
      input.familyIndex.baseFamily.actualOperator second
          (d11Transport.linearPullback.transport first second state) =
        d11Transport.linearPullback.transport first second
          (input.familyIndex.baseFamily.actualOperator first state)) ∧
    (∀ first second sector state,
      d11Transport.linearPullback.transport first second
          ((Coordinates period hPeriod input).sectorProjector sector state) =
        (Coordinates period hPeriod input).sectorProjector sector
          (d11Transport.linearPullback.transport first second state)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (d11Transport.physicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (d11Transport.physicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨d11Transport.linearPullback.reverseMorphism,
    d11Transport.linearPullback.operator_intertwining
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback,
    d11Transport.linearPullback.transport_commutes_sectorProjector
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback,
    d11Transport.physicalResolvedKernelFamily period hPeriod input natural,
    d11Transport.physicalRegularity period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
end JanusFormal