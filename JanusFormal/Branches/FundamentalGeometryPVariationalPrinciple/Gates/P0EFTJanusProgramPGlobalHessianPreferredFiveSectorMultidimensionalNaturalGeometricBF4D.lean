import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalGeometricBismutFreedBaseFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D

/-!
# Genuine multidimensional natural-geometric BF frontier for Candidate-A

This is the preferred replacement for the old abstract higher-dimensional BF
status.  It asks for one explicit normed parameter space `Base` and one literal
ambient Candidate-A Hessian family

`H : Base → CandidateAHilbert →L CandidateAHilbert`

which is simultaneously

* a five-sector D11 natural elliptic family;
* the source of the genuine varying kernel complements and Green family;
* the source of the intrinsic BF trace one-form and its derived curvature.

A differentiable path through `Base` is required to restrict `H` to the already
constructed one-parameter Candidate-A `actualOperator`.  The geometric BF
one-form on that path must equal the already constructed one-parameter
operator-trace coefficient.  Thus the multidimensional family extends the
existing result rather than replacing it.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBF4D

set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option synthInstance.maxHeartbeats 24000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPFiveSectorNaturalGeometricBismutFreedBaseFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusNaturalEllipticFamilyExistence
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
    {fold : Fold} {Index Base : Type*}
    [NormedAddCommGroup Base] [NormedSpace Real Base]

private abbrev CandidateAHilbert :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod
    configuration data analysis

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Preferred genuine multidimensional Candidate-A frontier. -/
structure GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base : Type*) [NormedAddCommGroup Base] [NormedSpace Real Base] where
  immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory
  naturalFamily : NaturalEllipticOperatorFamily immersionCategory
  ambientOperator : Base → CandidateAHilbert period hPeriod →L[Real]
    CandidateAHilbert period hPeriod
  anchor : Base
  reference : Base →
    SelfAdjointKernelComplement (ambientOperator anchor) →L[Real]
      SelfAdjointKernelComplement (ambientOperator anchor)
  multidimensional : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
    (family := naturalFamily) ambientOperator (Coordinates period hPeriod input)
      reference anchor
  path : DifferentiableGeometricFamilyPathData Base
  ambient_operator_restriction : ∀ parameter,
    ambientOperator (path.point parameter) =
      input.familyIndex.baseFamily.actualOperator parameter
  path_bismutFreed_restriction : ∀ parameter,
    pulledLinearGeometricCoefficient
        multidimensional.bismutFreed.geometric.geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter

namespace GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D

/-- The multidimensional ambient family is sector-preserving everywhere. -/
theorem ambientOperator_commutes_sectorProjector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
      period hPeriod input Base)
    (base : Base) (sector : FivePhysicalSector)
    (state : CandidateAHilbert period hPeriod) :
    closure.ambientOperator base
        ((Coordinates period hPeriod input).sectorProjector sector state) =
      (Coordinates period hPeriod input).sectorProjector sector
        (closure.ambientOperator base state) :=
  closure.multidimensional.operator_commutes_sectorProjector base sector state

/-- Restriction of the multidimensional Hessian is literally the existing
Candidate-A family. -/
theorem ambientOperator_on_path
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
      period hPeriod input Base)
    (parameter : Real) :
    closure.ambientOperator (closure.path.point parameter) =
      input.familyIndex.baseFamily.actualOperator parameter :=
  closure.ambient_operator_restriction parameter

/-- Restriction of the multidimensional geometric BF one-form is exactly the
existing one-parameter trace connection. -/
theorem bismutFreed_on_path
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
      period hPeriod input Base)
    (parameter : Real) :
    pulledLinearGeometricCoefficient
        closure.multidimensional.bismutFreed.geometric.geometry closure.path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter :=
  closure.path_bismutFreed_restriction parameter

/-- The higher-dimensional local index two-form is not independent of BF
curvature; it equals the curvature derived from the same ambient Hessian's
intrinsic trace connection. -/
theorem localIndex_eq_operatorTraceCurvature
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
      period hPeriod input Base)
    (base first second : Base) :
    closure.multidimensional.bismutFreed.localIndex.twoForm base first second =
      ((closure.multidimensional.bismutFreed.analytic.trace.
        bismutFreedTraceCurvature base first second : Real) : Complex) :=
  closure.multidimensional.localIndex_eq_operatorTraceCurvature base first second

/-- Public genuine multidimensional Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_multidimensional_natural_geometric_BF_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D
      period hPeriod input Base) :
    (∀ parameter,
      closure.ambientOperator (closure.path.point parameter) =
        input.familyIndex.baseFamily.actualOperator parameter) ∧
    (∀ base sector state,
      closure.ambientOperator base
          ((Coordinates period hPeriod input).sectorProjector sector state) =
        (Coordinates period hPeriod input).sectorProjector sector
          (closure.ambientOperator base state)) ∧
    (∀ parameter,
      pulledLinearGeometricCoefficient
          closure.multidimensional.bismutFreed.geometric.geometry closure.path
          parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      closure.multidimensional.bismutFreed.localIndex.twoForm base first second =
        ((closure.multidimensional.bismutFreed.analytic.trace.
          bismutFreedTraceCurvature base first second : Real) : Complex)) :=
  ⟨closure.ambientOperator_on_path period hPeriod input,
    closure.ambientOperator_commutes_sectorProjector period hPeriod input,
    closure.bismutFreed_on_path period hPeriod input,
    closure.localIndex_eq_operatorTraceCurvature period hPeriod input⟩

end GlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBFData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMultidimensionalNaturalGeometricBF4D
end JanusFormal
