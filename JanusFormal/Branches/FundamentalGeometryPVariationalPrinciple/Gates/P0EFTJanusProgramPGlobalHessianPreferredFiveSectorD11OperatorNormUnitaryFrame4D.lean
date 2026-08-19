import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D

/-!
# Candidate-A D11 unitary frame with operator-norm regularity

The preceding Candidate-A D11 frame stored two separate C1 premises:

```text
a ↦ F_a e_i(0),
a ↦ F_a v,  v ∈ (ker H_0)ᗮ.
```

For connection geometry the natural datum is stronger and simpler:

```text
a ↦ F_a
```

is differentiable in the normed space of continuous linear endomorphisms of
the fixed Candidate-A Hilbert space.

Evaluation of a differentiable operator-valued family at any fixed vector is
differentiable.  Hence one operator-norm certificate generates both old C1
premises, the complete unitary D11 Fredholm frame, and the concrete H14
Fredholm--Green closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D

set_option autoImplicit false
set_option maxHeartbeats 158000000
set_option synthInstance.maxHeartbeats 79000000
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
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelCompleteSpace
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

private def representedUnitaryFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (unitary : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback) :=
  unitary.frame
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback

/-- One represented D11 unitary frame plus one operator-norm C1 certificate. -/
structure GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  unitaryFrame : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback
  operatorRegularity : OperatorNormDifferentiableUnitaryFrameData
    (representedUnitaryFrame period hPeriod input natural unitaryFrame)

namespace GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D

/-- Operator-norm regularity automatically supplies the older vectorwise C1
D11 frame interface. -/
def toD11UnitaryAdmissibleIsomorphismFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
      period hPeriod input natural where
  unitaryFrame := frame.unitaryFrame
  kernel_vector_differentiable := by
    intro mode
    exact frame.operatorRegularity.differentiable_apply
      (input.kernels.basis 0 mode).1
  complement_vector_differentiable := by
    intro vector
    exact frame.operatorRegularity.differentiable_apply vector.1

/-- The complete concrete H14--D11 Fredholm--Green closure generated from the
operator-norm frame. -/
def toConcreteH14D11UnitaryFredholmGreenClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural :=
  concreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural
    (frame.toD11UnitaryAdmissibleIsomorphismFrame period hPeriod input natural)

/-- Public operator-norm D11 frame checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_operator_norm_unitary_frame_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :
    Nonempty
      (GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
        period hPeriod input natural) :=
  ⟨frame.toConcreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
end JanusFormal
