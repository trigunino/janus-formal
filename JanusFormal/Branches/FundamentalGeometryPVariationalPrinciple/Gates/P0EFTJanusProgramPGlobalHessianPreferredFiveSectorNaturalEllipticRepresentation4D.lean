import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D

/-!
# D11 natural elliptic representation of the preferred Candidate-A Hessian

This is the operator-level bridge missing from the earlier geometric status
interface.  A D11 natural elliptic family is represented on the exact ambient
Candidate-A Hilbert space, and its conjugated operator is required to equal the
same `actualOperator` already used by H12/H14, the kernel family and the
Bismut--Freed construction.

No second Hessian is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D

set_option autoImplicit false
set_option maxHeartbeats 34000000
set_option synthInstance.maxHeartbeats 17000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusNaturalSymbolCalculus
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance effectiveQuotientChartedSpace : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientMeasurableSpace : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpace : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable {measure : Measure (EffectiveQuotient period hPeriod)}

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D period hPeriod configuration data analysis
      (measure := measure)
      (diracGreenClosureMatterRealization period hPeriod couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- Exact D11 realization data for the already selected Candidate-A Hessian
family. -/
structure GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  immersionCategory : SpinCImmersionCategory
  naturalFamily : NaturalEllipticOperatorFamily immersionCategory
  representation : NaturalEllipticOperatorRepresentationData
    immersionCategory naturalFamily
    (fun parameter state => input.familyIndex.baseFamily.actualOperator parameter state)

namespace GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D

/-- The represented D11 operator is pointwise the genuine Candidate-A Hessian
used everywhere else in the preferred route. -/
theorem representedNaturalOperator_eq_actual
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (parameter : Real) :
    bridge.representation.representedNaturalOperator parameter =
      fun state => input.familyIndex.baseFamily.actualOperator parameter state :=
  bridge.representation.representedNaturalOperator_eq parameter

/-- Candidate-A Hessian inherits the D11 naturality equation through the exact
representation bridge. -/
theorem actualOperator_naturality
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    {first second : Real}
    (morphism : AdmissibleMorphism bridge.immersionCategory
      (bridge.representation.objectAt first)
      (bridge.representation.objectAt second))
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis) :
    bridge.representation.representedTargetPullback morphism
        (input.familyIndex.baseFamily.actualOperator second state) =
      input.familyIndex.baseFamily.actualOperator first
        (bridge.representation.representedSourcePullback morphism state) :=
  bridge.representation.representedOperator_naturality morphism state

/-- Candidate-A Hessian depends only on the finite jet selected by the exact D11
natural family. -/
theorem actualOperator_depends_only_on_D11_jet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (parameter : Real)
    (first second : GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis)
    (hJet : bridge.representation.RepresentedSameJetThrough parameter first second) :
    input.familyIndex.baseFamily.actualOperator parameter first =
      input.familyIndex.baseFamily.actualOperator parameter second :=
  bridge.representation.representedOperator_depends_only_on_jet
    parameter first second hJet

/-- Public exact D11/Candidate-A operator representation checkpoint. -/
theorem global_hessian_preferred_five_sector_natural_elliptic_representation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input) :
    (∀ parameter,
      bridge.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ parameter first second,
      bridge.representation.RepresentedSameJetThrough parameter first second →
        input.familyIndex.baseFamily.actualOperator parameter first =
          input.familyIndex.baseFamily.actualOperator parameter second) ∧
    IsElliptic bridge.immersionCategory bridge.naturalFamily.symbolFamily :=
  ⟨bridge.representedNaturalOperator_eq_actual period hPeriod input,
    bridge.actualOperator_depends_only_on_D11_jet period hPeriod input,
    bridge.naturalFamily.elliptic⟩

end GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
end JanusFormal
