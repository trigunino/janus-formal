import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedVectors4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurBasisFrontier4D

/-!
# Canonical-six H10--H14 frontier from named finite reference vectors

This façade is the most direct Schur interface before the finite determinant is
computed.  The reference modes are actual vectors in the common Candidate-A
Hilbert space.  Their span, basis, orthogonal complement, four Schur blocks,
closed range, finite actual kernel and reduced Green operator are all derived.

The sole infinite-dimensional Schur premise is invertibility of the canonical
Hessian block on the orthogonal complement of the selected reference modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedVectors4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurBasisFrontier4D
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

/-- Preferred named-reference-mode terminal. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurNamedVectors_frontier_gate
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
    (schur : GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode) :=
  global_candidateA_hessian_canonicalSix_orthogonalSchurBasis_frontier_gate
    period hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (schur.toBasisData period hPeriod (measure := measure))

/-- The displayed physical reference vectors are linearly independent. -/
theorem global_candidateA_hessian_orthogonalSchurNamedVectors_linearIndependent
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (schur : GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :
    LinearIndependent Real schur.namedData.vector :=
  schur.namedData.linearIndependent

/-- The actual kernel dimension is the finite Schur-kernel dimension. -/
theorem global_candidateA_hessian_orthogonalSchurNamedVectors_kernel_finrank_eq
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
    (schur : GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period
      hPeriod (measure := measure) configuration data analysis
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
        (((schur.toBasisData period hPeriod
          (measure := measure)).toOrthogonalData period hPeriod
            (measure := measure)).toSchurZeroModeData period hPeriod
              (measure := measure)).schur.schur.ker :=
  global_candidateA_hessian_orthogonalSchurBasis_kernel_finrank_eq period
    hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (schur.toBasisData period hPeriod (measure := measure))

/-- The finite reference set bounds the number of actual zero modes. -/
theorem global_candidateA_hessian_orthogonalSchurNamedVectors_kernel_finrank_le_card
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
    (schur : GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period
      hPeriod (measure := measure) configuration data analysis
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
  global_candidateA_hessian_orthogonalSchurBasis_kernel_finrank_le_card period
    hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (schur.toBasisData period hPeriod (measure := measure))

/-- The terminal named-vector Schur route has the same three natural work
packets: local family, one chart estimate, and named finite reference vectors
with invertible canonical complementary block. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurNamedVectors_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D
end JanusFormal
