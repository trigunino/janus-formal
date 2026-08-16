import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D

/-!
# Candidate-A continuation from basepoint D11 admissible isomorphisms

This file records the smallest current D11 transport frontier for the preferred
Candidate-A kernel family.  For every parameter `a`, choose one admissible
isomorphism from the represented H12 object to the represented object at `a`.
Prove that its forward and reverse represented pullbacks are real-linear and
that reverse source and target pullbacks agree.  Add C1 dependence of the exact
H12 basis under the resulting frame.

Everything else is derived:

* forward/reverse pullbacks are mutual linear inverses;
* D11 naturality gives `H_a F_a = F_a H_0`;
* D11 sector covariance gives `F_a P_s = P_s F_a`;
* `T_ab = F_b F_a⁻¹` gives the pairwise cocycle;
* the route-independent global physical-kernel continuation output follows.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D

set_option autoImplicit false
set_option maxHeartbeats 98000000
set_option synthInstance.maxHeartbeats 49000000
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
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
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

/-- Basepoint represented D11 admissible isomorphisms with linear pullbacks and
C1 transport of the exact H12 basis. -/
structure GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  linearFrame :
    LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      (operator := input.familyIndex.baseFamily.actualOperator)
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        linearFrame.frame
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback parameter
          (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D

/-- The represented D11 basepoint frame satisfies the complete
sector-preserving Candidate-A frame interface. -/
def toSectorPreservingAmbientFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Frame :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural where
  frameData := d11Frame.linearFrame.toFiniteIntertwiningOperatorFrame
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback
  frame_commutes_sector :=
    d11Frame.linearFrame.frame_commutes_sectorProjector
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  transported_vector_differentiable :=
    d11Frame.transported_vector_differentiable

/-- Route-independent global physical continuation output generated from the
basepoint D11 isomorphisms. -/
def toPhysicalKernelContinuationOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Frame :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input :=
  (d11Frame.toSectorPreservingAmbientFrame period hPeriod input natural).
    toPhysicalKernelContinuationOutput period hPeriod input natural

/-- The resulting physical closure. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Frame :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
        period hPeriod input natural) :=
  (d11Frame.toPhysicalKernelContinuationOutput period hPeriod input natural).
    closure

/-- Public minimal D11 basepoint-frame checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_admissible_isomorphism_frame_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Frame :
      GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    (∀ parameter,
      Function.LeftInverse
        (d11Frame.linearFrame.forwardLinear parameter)
        (d11Frame.linearFrame.reverseLinear parameter)) ∧
    (∀ parameter,
      Function.RightInverse
        (d11Frame.linearFrame.forwardLinear parameter)
        (d11Frame.linearFrame.reverseLinear parameter)) ∧
    (∀ parameter state,
      input.familyIndex.baseFamily.actualOperator parameter
          ((d11Frame.toSectorPreservingAmbientFrame period hPeriod input natural).
            frameData.frame parameter state) =
        (d11Frame.toSectorPreservingAmbientFrame period hPeriod input natural).
          frameData.frame parameter
            (input.familyIndex.baseFamily.actualOperator 0 state)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (d11Frame.physicalNamedKernelFamilyClosure period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (d11Frame.physicalNamedKernelFamilyClosure period hPeriod input natural) ∧
    ((d11Frame.toPhysicalKernelContinuationOutput period hPeriod input natural).
      closure.familyIndex = input.familyIndex) := by
  let representation :=
    natural.covariance.sectorRepresentation.bridge.representation
  let coordinates := Coordinates period hPeriod input
  let refinement := natural.covariance.sectorRepresentation.sectorRefinement
  let pullback := natural.covariance.pullback
  have hFrame := d11Frame.linearFrame.
    linear_natural_representation_admissible_isomorphism_frame_gate
      representation coordinates refinement pullback
  exact
    ⟨hFrame.1,
      hFrame.2.1,
      hFrame.2.2.1,
      (d11Frame.toPhysicalKernelContinuationOutput period hPeriod input natural).
        resolved,
      (d11Frame.toPhysicalKernelContinuationOutput period hPeriod input natural).
        regularity,
      (d11Frame.toPhysicalKernelContinuationOutput period hPeriod input natural).
        familyIndex_eq⟩

end GlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11AdmissibleIsomorphismFrame4D
end JanusFormal