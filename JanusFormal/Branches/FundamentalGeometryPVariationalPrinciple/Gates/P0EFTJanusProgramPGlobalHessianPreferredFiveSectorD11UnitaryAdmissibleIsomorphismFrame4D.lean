import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D

/-!
# Candidate-A unitary Fredholm frame from D11 admissible isomorphisms

This file closes the architectural route from represented D11 geometry to one
C1 Fredholm splitting of the genuine Candidate-A family.  The represented
basepoint admissible isomorphisms provide a unitary frame `F_a`; D11 naturality
intertwines the actual Hessians and the previously established sector covariance
commutes with all five physical projectors.

Two C1 statements remain as the family-regularity input:

* `a ↦ F_a e_i(0)` for each exact H12 zero mode;
* `a ↦ F_a v` for each fixed `v ∈ (ker H_0)ᗮ`.

The output contains the globally sector-pure physical kernel family and the
unitary C1 trivialization of the canonical orthogonal complements, with the same
operator and family-index data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D

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
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D.GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Unitary represented D11 basepoint frame together with C1 control on the
finite zero modes and every fixed vector of the H12 kernel complement. -/
structure GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  unitaryFrame :
    UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      (operator := input.familyIndex.baseFamily.actualOperator)
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  kernel_vector_differentiable : ∀ mode,
    Differentiable Real
      (fun parameter : Real =>
        unitaryFrame.frame
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback parameter
          (input.kernels.basis 0 mode).1)
  complement_vector_differentiable : ∀
      vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ,
    Differentiable Real
      (fun parameter : Real =>
        unitaryFrame.frame
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback parameter vector.1)

namespace GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D

/-- Upgrade the represented D11 unitary frame to the complete Candidate-A
unitary ambient-frame packet. -/
def toUnitaryAmbientFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
      period hPeriod input natural where
  frameData := d11Unitary.unitaryFrame.toFiniteUnitaryIntertwiningOperatorFrame
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback
  frame_commutes_sector :=
    d11Unitary.unitaryFrame.frame_commutes_sectorProjector
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback
  kernel_vector_differentiable :=
    d11Unitary.kernel_vector_differentiable
  complement_vector_differentiable := by
    intro vector
    convert d11Unitary.complement_vector_differentiable vector using 1
    funext parameter
    exact (d11Unitary.unitaryFrame.toFiniteUnitaryIntertwiningOperatorFrame
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback).kernelComplementFrame_apply_val parameter vector

/-- Route-independent C1 unitary Fredholm-frame output generated by D11. -/
def toUnitaryFredholmFrameOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input natural
        (d11Unitary.toUnitaryAmbientFrame period hPeriod input natural) :=
  (d11Unitary.toUnitaryAmbientFrame period hPeriod input natural).toUnitaryFredholmFrameOutput
    period hPeriod input natural

/-- The globally sector-resolved physical named-kernel closure. -/
def physicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :=
  (d11Unitary.toUnitaryFredholmFrameOutput period hPeriod input natural).physical.closure

/-- Public Candidate-A D11 unitary Fredholm-frame checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_unitary_admissible_isomorphism_frame_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    let output :=
      d11Unitary.toUnitaryFredholmFrameOutput period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      ‖output.complementTransport 0 parameter vector‖ = ‖vector‖) ∧
    (∀ first second third,
      (output.complementTransport first second).trans
          (output.complementTransport second third) =
        output.complementTransport first third) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          (output.complementTransport 0 parameter vector).1)) := by
  dsimp only
  let output :=
    d11Unitary.toUnitaryFredholmFrameOutput period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      fun parameter vector =>
        (output.complementTransport 0 parameter).norm_map vector,
      output.complementTransport_trans,
      output.complement_vector_differentiable⟩

end GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
end JanusFormal
