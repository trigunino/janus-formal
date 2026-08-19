import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D

/-!
# Unitary Fredholm frame for the preferred Candidate-A family

The finite zero-mode continuation and the reduced Fredholm family must use the
same ambient geometry.  A sector-preserving unitary frame based at H12 supplies
both at once:

* it transports the exact H12 physical kernel basis to every true kernel;
* it transports `(ker H_0)ᗮ` isometrically onto `(ker H_a)ᗮ`;
* it preserves all five physical projectors;
* its transported kernel and complement vectors are C1 in the common ambient
  Candidate-A Hilbert space.

This file packages that output without choosing a second completion or a
separate complement trivialization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D

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
open P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D
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

/-- Sector-preserving unitary frame of the genuine Candidate-A family, with C1
control on both the finite kernel basis and every fixed basepoint complement
vector. -/
structure GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  frameData : FiniteUnitaryIntertwiningOperatorFrameData
    input.familyIndex.baseFamily.actualOperator
  frame_commutes_sector : ∀ parameter sector vector,
    frameData.frame parameter
        ((Coordinates period hPeriod input).sectorProjector sector vector) =
      (Coordinates period hPeriod input).sectorProjector sector
        (frameData.frame parameter vector)
  kernel_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        frameData.frame parameter (input.kernels.basis 0 mode).1)
  complement_vector_differentiable : ∀
      vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ,
    Differentiable Real
      (fun parameter : Real =>
        (frameData.kernelComplementFrame parameter vector).1)

namespace GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D

/-- Forgetting metric preservation yields the earlier sector-preserving ambient
frame used for the physical zero modes. -/
def toSectorPreservingAmbientFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D
      period hPeriod input natural where
  frameData :=
    { frame := fun parameter => (unitary.frameData.frame parameter).toLinearEquiv
      frame_zero := by
        rw [unitary.frameData.frame_zero]
        rfl
      intertwines_basepoint := unitary.frameData.intertwines_basepoint }
  frame_commutes_sector := unitary.frame_commutes_sector
  transported_vector_differentiable := unitary.kernel_vector_differentiable

/-- Route-independent physical kernel continuation generated by the unitary
frame. -/
def physicalKernelContinuation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input :=
  GlobalHessianPreferredFiveSectorSectorPreservingAmbientFrame4D.toPhysicalKernelContinuationOutput
    period hPeriod input natural
    (unitary.toSectorPreservingAmbientFrame period hPeriod input natural)

/-- Pairwise unitary transport on the common ambient Hilbert space. -/
def ambientTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) :
    FiniteUnitaryIntertwiningOperatorTransportData
      input.familyIndex.baseFamily.actualOperator :=
  unitary.frameData.toFiniteUnitaryIntertwiningOperatorTransport

/-- Pairwise unitary transport of the true kernels. -/
def kernelTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural)
    (first second : Real) :=
  (unitary.ambientTransport period hPeriod input natural).kernelTransport
    first second

/-- Pairwise unitary transport of the canonical reduced spaces. -/
def kernelComplementTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural)
    (first second : Real) :=
  (unitary.ambientTransport period hPeriod input natural).kernelComplementTransport
    first second

/-- The complement frame is literally the restriction of the same ambient
unitary frame. -/
theorem kernelComplementFrame_apply_val
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    (unitary.kernelComplementTransport period hPeriod input natural 0 parameter
      vector).1 = unitary.frameData.frame parameter vector.1 := by
  exact unitary.frameData.kernelComplementFrame_apply_val parameter vector

/-- Exact cocycle of the reduced-space transports. -/
theorem kernelComplementTransport_trans
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural)
    (first second third : Real) :
    (unitary.kernelComplementTransport period hPeriod input natural first second).trans
      (unitary.kernelComplementTransport period hPeriod input natural second third) =
      unitary.kernelComplementTransport period hPeriod input natural first third :=
  (unitary.ambientTransport period hPeriod input natural).kernelComplementTransport_trans
    first second third

/-- Output combining the physical finite kernel family with the canonical C1
unitary trivialization of its orthogonal complements. -/
structure GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) where
  physical : GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
    period hPeriod input
  complementFrame : ∀ parameter,
    (input.familyIndex.baseFamily.actualOperator 0).kerᗮ ≃ₗᵢ[Real]
      (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ
  complementTransport : ∀ first second,
    (input.familyIndex.baseFamily.actualOperator first).kerᗮ ≃ₗᵢ[Real]
      (input.familyIndex.baseFamily.actualOperator second).kerᗮ
  complementTransport_trans : ∀ first second third,
    (complementTransport first second).trans
        (complementTransport second third) =
      complementTransport first third
  complementFrame_zero : complementFrame 0 =
    LinearIsometryEquiv.refl Real _
  complementFrame_cocycle : ∀ first second third,
    let firstSecond :
      (input.familyIndex.baseFamily.actualOperator first).kerᗮ ≃ₗᵢ[Real]
        (input.familyIndex.baseFamily.actualOperator second).kerᗮ :=
      unitary.kernelComplementTransport period hPeriod input natural first second
    let secondThird :
      (input.familyIndex.baseFamily.actualOperator second).kerᗮ ≃ₗᵢ[Real]
        (input.familyIndex.baseFamily.actualOperator third).kerᗮ :=
      unitary.kernelComplementTransport period hPeriod input natural second third
    firstSecond.trans secondThird =
      unitary.kernelComplementTransport period hPeriod input natural first third
  complement_vector_differentiable : ∀
      vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ,
    Differentiable Real
      (fun parameter : Real => (complementFrame parameter vector).1)

/-- Construct the complete unitary Fredholm frame output. -/
def toUnitaryFredholmFrameOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input natural unitary where
  physical := unitary.physicalKernelContinuation period hPeriod input natural
  complementFrame := fun parameter =>
    unitary.kernelComplementTransport period hPeriod input natural 0 parameter
  complementTransport :=
    unitary.kernelComplementTransport period hPeriod input natural
  complementTransport_trans :=
    unitary.kernelComplementTransport_trans period hPeriod input natural
  complementFrame_zero :=
    (unitary.ambientTransport period hPeriod input natural).kernelComplementTransport_self 0
  complementFrame_cocycle := by
    intro first second third
    exact unitary.kernelComplementTransport_trans period hPeriod input natural
      first second third
  complement_vector_differentiable :=
    unitary.complement_vector_differentiable

/-- Public unitary Candidate-A Fredholm-frame checkpoint. -/
theorem global_hessian_preferred_five_sector_unitary_fredholm_frame_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural) :
    let output := unitary.toUnitaryFredholmFrameOutput period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      ‖output.complementFrame parameter vector‖ = ‖vector‖) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          (output.complementFrame parameter vector).1)) := by
  dsimp only
  let output := unitary.toUnitaryFredholmFrameOutput period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      fun parameter vector => (output.complementFrame parameter).norm_map vector,
      output.complement_vector_differentiable⟩

end GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D
end JanusFormal
