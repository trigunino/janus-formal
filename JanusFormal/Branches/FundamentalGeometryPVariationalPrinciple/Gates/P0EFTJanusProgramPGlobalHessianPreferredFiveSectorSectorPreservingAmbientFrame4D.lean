import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D

/-!
# Candidate-A physical kernel continuation from a basepoint frame

A pairwise ambient transport is generated automatically from a single
trivializing frame based at H12.  This file adds the physical conditions on that
frame:

* `H_a F_a = F_a H_0`;
* `F_a P_s = P_s F_a` for all five sectors;
* C1 dependence of `F_a` on the exact H12 basis vectors.

The pairwise transport `T_ab = F_b F_a⁻¹` then intertwines the genuine
Candidate-A Hessians, commutes with the restricted physical kernel projectors,
and yields the route-independent global physical-kernel continuation output.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D

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
open P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
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

/-- Sector-preserving linear trivializing frame of the genuine Candidate-A
operator family. -/
structure GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  frameData : FiniteIntertwiningOperatorFrameData
    input.familyIndex.baseFamily.actualOperator
  frame_commutes_sector : ∀ parameter sector vector,
    frameData.frame parameter
        ((Coordinates period hPeriod input).sectorProjector sector vector) =
      (Coordinates period hPeriod input).sectorProjector sector
        (frameData.frame parameter vector)
  transported_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        frameData.frame parameter (input.kernels.basis 0 mode).1)

namespace GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D

/-- The inverse frame commutes with the same fixed physical projectors. -/
theorem frame_symm_commutes_sector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural)
    (parameter : Real) (sector : FivePhysicalSector) (vector :
      GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis) :
    (frame.frameData.frame parameter).symm
        ((Coordinates period hPeriod input).sectorProjector sector vector) =
      (Coordinates period hPeriod input).sectorProjector sector
        ((frame.frameData.frame parameter).symm vector) := by
  apply (frame.frameData.frame parameter).injective
  rw [(frame.frameData.frame parameter).apply_symm_apply]
  have hCommute := frame.frame_commutes_sector parameter sector
    ((frame.frameData.frame parameter).symm vector)
  rw [(frame.frameData.frame parameter).apply_symm_apply] at hCommute
  exact hCommute.symm

/-- Pairwise transport generated by the frame commutes with every physical
projector. -/
theorem transport_commutes_sector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural)
    (first second : Real) (sector : FivePhysicalSector) (vector :
      GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis) :
    frame.frameData.transport first second
        ((Coordinates period hPeriod input).sectorProjector sector vector) =
      (Coordinates period hPeriod input).sectorProjector sector
        (frame.frameData.transport first second vector) := by
  rw [frame.frameData.transport_apply]
  rw [frame.frame_symm_commutes_sector period hPeriod input natural first sector
    vector]
  exact frame.frame_commutes_sector second sector
    ((frame.frameData.frame first).symm vector)

/-- Basepoint frame induces the complete pairwise sector-preserving ambient
transport packet. -/
def toSectorPreservingAmbientTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingAmbientTransport4D
      period hPeriod input natural where
  transport := frame.frameData.transport
  transport_self := frame.frameData.transport_self
  transport_trans := frame.frameData.transport_trans
  operator_intertwining := frame.frameData.transport_intertwines
  sector_commutation := frame.transport_commutes_sector period hPeriod input
    natural
  transported_vector_differentiable := by
    intro mode
    convert frame.transported_vector_differentiable mode using 1
    funext parameter
    have hTransportZero := frame.frameData.transport_zero parameter
    exact congrArg
      (fun equivalence => equivalence (input.kernels.basis 0 mode).1)
      hTransportZero

/-- Route-independent global physical-kernel continuation output generated by
the basepoint frame. -/
def toPhysicalKernelContinuationOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input :=
  physicalKernelContinuationOfD11LinearPullback period hPeriod input natural
    { linearPullback :=
        { reverseMorphism := fun _ _ =>
            natural.covariance.sectorRepresentation.bridge.representation.
              immersionCategory.category.identity
              |> fun morphism =>
                { morphism := morphism
                  preservesSpinC :=
                    natural.covariance.sectorRepresentation.bridge.representation.
                      immersionCategory.category.identity_preserves_spinC _ }
          transport := frame.frameData.transport
          source_pullback_agreement := by
            intro
            rfl
          target_pullback_agreement := by
            intro
            rfl
          transport_self := frame.frameData.transport_self
          transport_trans := frame.frameData.transport_trans }
      transported_vector_differentiable := by
        intro mode
        exact (frame.toSectorPreservingAmbientTransport period hPeriod input
          natural).transported_vector_differentiable mode }

/-- Direct physical closure generated by the frame.  This avoids exposing the
synthetic D11 adapter used only to reuse the unified constructor. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural) :=
  (frame.toSectorPreservingAmbientTransport period hPeriod input natural).
    toPhysicalNamedKernelFamilyClosure period hPeriod input natural

/-- Public sector-preserving basepoint-frame checkpoint. -/
theorem global_hessian_preferred_five_sector_sector_preserving_ambient_frame_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural) :
    (∀ first second state,
      input.familyIndex.baseFamily.actualOperator second
          (frame.frameData.transport first second state) =
        frame.frameData.transport first second
          (input.familyIndex.baseFamily.actualOperator first state)) ∧
    (∀ first second sector state,
      frame.frameData.transport first second
          ((Coordinates period hPeriod input).sectorProjector sector state) =
        (Coordinates period hPeriod input).sectorProjector sector
          (frame.frameData.transport first second state)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod
        (frame.physicalNamedKernelFamilyClosure period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (frame.physicalNamedKernelFamilyClosure period hPeriod input natural) :=
  ⟨frame.frameData.transport_intertwines,
    frame.transport_commutes_sector period hPeriod input natural,
    (frame.toSectorPreservingAmbientTransport period hPeriod input natural).
      toSectorPreservingKernelTransport period hPeriod input natural |>
        fun transport =>
          transport.physicalResolvedKernelFamily period hPeriod input natural,
    (frame.toSectorPreservingAmbientTransport period hPeriod input natural).
      toSectorPreservingKernelTransport period hPeriod input natural |>
        fun transport =>
          transport.physicalRegularity period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
end JanusFormal