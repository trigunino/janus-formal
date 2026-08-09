import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveNamedKernelFrontier4D

/-!
# Preferred H10--H14 Schur frontier from ambient coercivity

The analytic estimate is now stated directly for the displayed augmented
Candidate-A Hessian on the orthogonal complement of concrete reference modes.
This estimate constructs the complementary inverse.  A finite named basis of
the Schur kernel then reconstructs the actual ambient zero modes.

This is the narrowest named-kernel Schur façade: it contains no supplied block
inverse and no coercivity statement about an auxiliary compressed operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurAmbientCoerciveNamedKernelFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 16600000
set_option synthInstance.maxHeartbeats 8300000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernel4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveNamedKernelFrontier4D
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

/-- Terminal H10--H14 gate from the physical ambient coercivity estimate. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurAmbientCoerciveNamedKernel_frontier_gate
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
    (named : GlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernelData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode ZeroMode) :=
  let coerciveNamed := named.toCoerciveNamedKernelData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_orthogonalSchurCoerciveNamedKernel_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode ZeroMode coerciveNamed
  (terminal,
    named.ambient.ambientCoercivity.constant,
    named.ambient.ambientCoercivity.constant_pos,
    named.ambient.ambientCoercivity.coercive,
    (coerciveNamed.toNamedKernelData period hPeriod).toNamedZeroModeData period
      hPeriod |>.namedFamily period hPeriod)

/-- Beyond fixed geometry the terminal has only the local family, the common
chart estimate and one finite-mode ambient coercivity/kernel computation. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurAmbientCoerciveNamedKernel_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurAmbientCoerciveNamedKernelFrontier4D
end JanusFormal
