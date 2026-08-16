import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D

/-!
# Candidate-A continuation from D11 admissible isomorphisms

This is the most geometric continuation interface currently available for the
preferred Candidate-A family.  It asks for a coherent family of admissible D11
isomorphisms between the represented immersion objects, real-linearity of their
represented forward and reverse pullbacks, agreement of reverse source and
target pullback, and C1 dependence of the transported H12 generators.

The two pullbacks produce a `LinearEquiv` automatically.  Functoriality derives
its identity and cocycle laws.  D11 naturality derives Hessian intertwining and
the established five-sector covariance derives projector commutation.  The
result is the route-independent physical-kernel continuation output consumed by
the Fredholm--zeta layers.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D

set_option autoImplicit false
set_option maxHeartbeats 96000000
set_option synthInstance.maxHeartbeats 48000000
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
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D
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

/-- Coherent admissible D11 isomorphisms with linear represented pullbacks and
C1 transport of the exact H12 basis. -/
structure GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  linearIsomorphismFamily :
    LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      (operator := input.familyIndex.baseFamily.actualOperator)
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        linearIsomorphismFamily.transport
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback 0 parameter
          (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D

/-- Upgrade admissible-isomorphism data to coherent represented pullback
transport. -/
def toD11CoherentPullbackTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11CoherentPullbackTransport4D
      period hPeriod input natural where
  coherentPullback :=
    isomorphisms.linearIsomorphismFamily.toCoherentPullbackTransport
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable :=
    isomorphisms.transported_vector_differentiable

/-- Upgrade directly to the full D11 linear pullback transport. -/
def toD11LinearPullbackTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
      period hPeriod input natural :=
  (isomorphisms.toD11CoherentPullbackTransport period hPeriod input natural).
    toD11LinearPullbackTransport period hPeriod input natural

/-- Route-independent physical continuation output generated by the D11
admissible-isomorphism family. -/
def toPhysicalKernelContinuationOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input :=
  physicalKernelContinuationOfD11LinearPullback period hPeriod input natural
    (isomorphisms.toD11LinearPullbackTransport period hPeriod input natural)

/-- The resulting physical closure. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
        period hPeriod input natural) :=
  (isomorphisms.toPhysicalKernelContinuationOutput period hPeriod input natural).
    closure

/-- Public Candidate-A admissible-isomorphism continuation checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_admissible_isomorphism_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
        period hPeriod input natural) :
    (∀ first second,
      Function.LeftInverse
        (isomorphisms.linearIsomorphismFamily.forwardLinear first second)
        (isomorphisms.linearIsomorphismFamily.reverseLinear first second)) ∧
    (∀ first second,
      Function.RightInverse
        (isomorphisms.linearIsomorphismFamily.forwardLinear first second)
        (isomorphisms.linearIsomorphismFamily.reverseLinear first second)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (isomorphisms.physicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (isomorphisms.physicalNamedKernelFamilyClosure period hPeriod input
          natural) ∧
    ((isomorphisms.toPhysicalKernelContinuationOutput period hPeriod input natural).
      closure.familyIndex = input.familyIndex) := by
  let representation :=
    natural.covariance.sectorRepresentation.bridge.representation
  let coordinates := Coordinates period hPeriod input
  let refinement := natural.covariance.sectorRepresentation.sectorRefinement
  let pullback := natural.covariance.pullback
  have hLinear :=
    isomorphisms.linearIsomorphismFamily.
      linear_natural_representation_admissible_isomorphism_family_gate
        representation coordinates refinement pullback
  exact
    ⟨hLinear.1,
      hLinear.2.1,
      (isomorphisms.toPhysicalKernelContinuationOutput period hPeriod input
        natural).resolved,
      (isomorphisms.toPhysicalKernelContinuationOutput period hPeriod input
        natural).regularity,
      (isomorphisms.toPhysicalKernelContinuationOutput period hPeriod input
        natural).familyIndex_eq⟩

end GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFamily4D
end JanusFormal