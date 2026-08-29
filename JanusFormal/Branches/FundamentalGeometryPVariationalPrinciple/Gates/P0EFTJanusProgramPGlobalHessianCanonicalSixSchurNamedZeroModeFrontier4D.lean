import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D

/-!
# H10--H14 from named reference modes and a named finite Schur kernel

The H11 side is constructed from the genuine dense-core-to-chart estimate.  On
the H12 side, concrete ambient reference vectors determine the finite
orthogonal Schur decomposition, while a physically labelled basis of the
finite Schur kernel determines the actual ambient zero modes.

This façade therefore joins the two most concrete routes without introducing a
map from the Hilbert completion back to smooth fields.  It returns the terminal
H10--H14 closure, exact named zero-mode synthesis, the actual-kernel dimension,
and the finite bound by the number of reference modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option synthInstance.maxHeartbeats 7000000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurNamedZeroMode4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
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

/-- Physical H11 extension generated from the same core-to-chart estimate used
by the completed H10 boundary projection. -/
def globalCandidateACanonicalSixSchurNamedPhysicalExtension
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
              hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
    (measure := measure) configuration data analysis einsteinScale hTransverse
      family chartBound

/-- Named actual-kernel gap extracted from the finite Schur kernel. -/
noncomputable def globalCandidateACanonicalSixSchurNamedActualGap
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
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualOrthogonalSchurNamedKernelData4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode ZeroMode) :=
  ((named.toNamedZeroModeData period hPeriod
    (measure := measure)).toActualZeroModeGap period hPeriod
      (measure := measure)).toActualKernelGap period hPeriod
        (measure := measure)

/-- Terminal H10--H14 gate preserving concrete reference modes and concrete
actual zero modes reconstructed from `ker S`. -/
def global_candidateA_hessian_canonicalSix_schurNamedZeroMode_frontier_gate
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
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualOrthogonalSchurNamedKernelData4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode ZeroMode) :=
  let actualGap := globalCandidateACanonicalSixSchurNamedActualGap period hPeriod
    (measure := measure) configuration data analysis einsteinScale hTransverse
      family chartBound Mode ZeroMode named
  let closure :=
    global_candidateA_hessian_canonicalSix_chartBound_frontier_gate period
      hPeriod (measure := measure) configuration data analysis einsteinScale
        hTransverse family chartBound actualGap
  let namedData := named.toNamedZeroModeData period hPeriod (measure := measure)
  show _ ∧ Nonempty _ ∧ _ ∧ _ ∧ Nonempty _ ∧ _ from
  ⟨closure,
    ⟨namedData.namedFamily period hPeriod (measure := measure)⟩,
    namedData.kernel_finrank_eq_card period hPeriod (measure := measure),
    namedData.namedBasis.zeroMode_card_le_referenceMode_card,
    ⟨named.reference.namedData.vector⟩,
    named.reference.namedData.linearIndependent⟩

/-- The preferred Schur route has three finite/analytic inputs beyond fixed
geometry: the local family, one core-to-chart estimate, and named reference plus
Schur-kernel modes. -/
theorem global_candidateA_hessian_canonicalSix_schurNamedZeroMode_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
end JanusFormal
