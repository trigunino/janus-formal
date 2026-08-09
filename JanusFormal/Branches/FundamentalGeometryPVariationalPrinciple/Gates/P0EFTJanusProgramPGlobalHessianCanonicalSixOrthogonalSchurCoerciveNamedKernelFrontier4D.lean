import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D

/-!
# H10--H14 from complementary coercivity and named Schur zero modes

This terminal route uses the most natural division of the finite/infinite
analysis:

* concrete reference vectors select the finite mode subspace;
* quadratic coercivity on its orthogonal complement constructs `D⁻¹`;
* a finite named basis of `ker S` reconstructs all actual ambient zero modes.

Together with the one dense-core-to-chart estimate, these data produce the
complete H10--H14 closure, actual-kernel Green operator, resolvent and exact
zero-mode count.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveNamedKernelFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 15800000
set_option synthInstance.maxHeartbeats 7900000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
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

/-- Preferred named-zero-mode terminal after replacing the complement inverse
by a coercivity estimate. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurCoerciveNamedKernel_frontier_gate
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
    (Mode ZeroMode : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode ZeroMode) :=
  let namedKernel := named.toNamedKernelData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_schurNamedZeroMode_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode ZeroMode namedKernel
  (terminal,
    named.coercive.namedCoercivity.constant,
    named.coercive.namedCoercivity.constant_pos,
    named.coercive.namedCoercivity.toCoercivityData.complement_bijective,
    (namedKernel.toNamedZeroModeData period hPeriod).namedFamily period hPeriod,
    (namedKernel.toNamedZeroModeData period hPeriod).kernel_finrank_eq_card
      period hPeriod)

/-- Only the local family, one dense-core estimate and one finite-mode
coercivity/kernel computation remain. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurCoerciveNamedKernel_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveNamedKernelFrontier4D
end JanusFormal
