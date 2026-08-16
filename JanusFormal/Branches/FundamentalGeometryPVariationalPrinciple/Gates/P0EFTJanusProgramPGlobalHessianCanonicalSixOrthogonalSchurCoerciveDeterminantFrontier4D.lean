import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoercivityFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedDeterminantFrontier4D

/-!
# Zero-mode-free H10--H14 from complementary coercivity and a determinant

Concrete reference vectors define the finite Schur subspace.  Coercivity on its
canonical orthogonal complement constructs the inverse of the infinite block
`D`.  Nonvanishing of the resulting finite Schur determinant then proves that
the complete augmented Candidate-A Hessian is bijective.

Thus the zero-mode-free stratum requires no supplied complement inverse, kernel
basis, projector or parametrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveDeterminantFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 16200000
set_option synthInstance.maxHeartbeats 8100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoercivity4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedDeterminantFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoercivityFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Coercive named-reference-mode data plus nonvanishing of its finite Schur
determinant. -/
structure GlobalCandidateAActualOrthogonalSchurCoerciveDeterminantData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode] : Prop where
  coercive : GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D period
    hPeriod configuration data analysis chart sameAction physical Mode
  determinant_ne_zero :
    globalCandidateAHessianNamedOrthogonalSchurDeterminant
      (coercive.toNamedVectorsData period hPeriod) ≠ 0

/-- Convert the coercive packet to the preceding named determinant packet. -/
def GlobalCandidateAActualOrthogonalSchurCoerciveDeterminantData4D.toNamedDeterminantData
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
    (determinantData :
      GlobalCandidateAActualOrthogonalSchurCoerciveDeterminantData4D period
        hPeriod configuration data analysis chart sameAction physical Mode) :
    GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
      configuration data analysis chart sameAction physical Mode where
  namedVectors := determinantData.coercive.toNamedVectorsData period hPeriod
  determinant_ne_zero := determinantData.determinant_ne_zero

/-- Preferred zero-mode-free terminal: H11 chart control, concrete reference
vectors, complementary coercivity and one finite determinant. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurCoerciveDeterminant_frontier_gate
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (determinantData :
      GlobalCandidateAActualOrthogonalSchurCoerciveDeterminantData4D period
        hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode) :=
  let namedDeterminant := determinantData.toNamedDeterminantData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_namedOrthogonalSchurDeterminant_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode namedDeterminant
  (terminal,
    determinantData.coercive.namedCoercivity.constant,
    determinantData.coercive.namedCoercivity.constant_pos,
    determinantData.determinant_ne_zero,
    global_candidateA_hessian_namedOrthogonalSchurDeterminant_kernel_zero
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode namedDeterminant)

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveDeterminantFrontier4D
end JanusFormal
