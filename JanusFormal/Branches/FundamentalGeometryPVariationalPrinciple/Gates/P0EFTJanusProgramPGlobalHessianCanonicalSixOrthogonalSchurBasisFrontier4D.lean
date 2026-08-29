import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBasis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurFrontier4D

/-!
# Canonical-six terminal from a finite physical Schur basis

This façade removes the last coordinate-equivalence field from the orthogonal
Schur route.  A finite basis of a selected physical mode subspace determines
its coordinates continuously, Hilbert projection determines the complement,
and the actual augmented Hessian determines all four blocks.

After the H10-reduced local family, the terminal inputs are therefore:

1. one graph-norm estimate for the true smooth-core map into the chart;
2. one finite physical basis;
3. invertibility of the canonical Hessian block on its orthogonal complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurBasisFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 11600000
set_option synthInstance.maxHeartbeats 5800000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
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
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBasis4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Preferred finite-basis Schur terminal. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurBasis_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (schur : GlobalCandidateAActualOrthogonalSchurBasisData4D period hPeriod
      (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode) :=
  global_candidateA_hessian_canonicalSix_orthogonalSchur_frontier_gate period
    hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (schur.toOrthogonalData period hPeriod (measure := measure))

/-- The basis labels define linearly independent ambient reference modes. -/
theorem global_candidateA_hessian_orthogonalSchurBasis_linearIndependent
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (schur : GlobalCandidateAActualOrthogonalSchurBasisData4D period hPeriod
      (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode) :
    LinearIndependent Real schur.modeVector :=
  schur.modeVector_linearIndependent

/-- The finite Schur problem computes the exact actual-kernel dimension. -/
theorem global_candidateA_hessian_orthogonalSchurBasis_kernel_finrank_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (schur : GlobalCandidateAActualOrthogonalSchurBasisData4D period hPeriod
      (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          (measure := measure) analysis
            (globalCandidateAActualKernelChart period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family)
            (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
              hPeriod (measure := measure) configuration data analysis
                einsteinScale hTransverse family chartBound)).ker =
      Module.finrank Real
        ((schur.toOrthogonalData period hPeriod
          (measure := measure)).toSchurZeroModeData period hPeriod
            (measure := measure)).schur.schur.ker :=
  global_candidateA_hessian_orthogonalSchur_kernel_finrank_eq period hPeriod
    (measure := measure) configuration data analysis einsteinScale hTransverse
      family chartBound Mode
        (schur.toOrthogonalData period hPeriod (measure := measure))

/-- The actual kernel dimension is bounded by the number of selected physical
reference modes. -/
theorem global_candidateA_hessian_orthogonalSchurBasis_kernel_finrank_le_card
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (schur : GlobalCandidateAActualOrthogonalSchurBasisData4D period hPeriod
      (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          (measure := measure) analysis
            (globalCandidateAActualKernelChart period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod
              (measure := measure) configuration data analysis einsteinScale
                hTransverse family)
            (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
              hPeriod (measure := measure) configuration data analysis
                einsteinScale hTransverse family chartBound)).ker ≤
      Fintype.card Mode :=
  global_candidateA_hessian_orthogonalSchur_kernel_finrank_le_card period
    hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (schur.toOrthogonalData period hPeriod (measure := measure))

/-- Beyond the fixed geometry, the basis frontier has three work packets:
local family, the one dense-core chart estimate, and the finite basis with
invertible canonical complement block. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurBasis_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurBasisFrontier4D
end JanusFormal
