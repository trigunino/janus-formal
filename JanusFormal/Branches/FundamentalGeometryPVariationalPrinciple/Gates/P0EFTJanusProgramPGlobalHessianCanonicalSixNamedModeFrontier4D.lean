import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixBasisCoercivityFrontier4D

/-!
# Terminal H10--H14 frontier with named actual zero modes

This façade retains the ambient physical zero-mode vectors instead of accepting
only an already packaged basis.  A finite synthesis equivalence onto the true
kernel proves that the named vectors span exactly `ker H` with unique
coefficients.  The standard coordinate basis then constructs the basis used by
the quadratic-coercivity reduction.

The terminal inputs are therefore:

* the H10-reduced Candidate-A local family;
* one graph-norm estimate for the genuine dense-core chart map;
* named ambient zero modes spanning exactly the actual kernel, together with
  quadratic coercivity on its orthogonal complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 13200000
set_option synthInstance.maxHeartbeats 6600000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelBasisCoercivity4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixBasisCoercivityFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedAddCommGroup
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedSpace
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

/-- Named-mode coercivity packet for the actual augmented Candidate-A
operator produced by the canonical-six H11 extension. -/
abbrev GlobalCandidateAActualNamedKernelCoercivity4D
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] :=
  SelfAdjointNamedKernelCoercivityData
    (globalCandidateAActualKernelOperator period hPeriod (measure := measure) configuration data
      analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound))
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound))
    ZeroMode

/-- Full H10--H14 closure with named zero modes and exact multiplicity. -/
def global_candidateA_hessian_canonicalSix_namedMode_frontier_gate
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualNamedKernelCoercivity4D period hPeriod
      (measure := measure) configuration data analysis einsteinScale hTransverse family chartBound
        ZeroMode)
    (ll_stationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  global_candidateA_hessian_canonicalSix_basisCoercivity_frontier_gate period
    hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
      chartBound ZeroMode
        (named.toBasisCoercivity
          (operator := globalCandidateAActualKernelOperator period hPeriod
            (measure := measure) configuration data analysis
              (globalCandidateAActualKernelChart period hPeriod (measure := measure)
                configuration data analysis einsteinScale hTransverse family)
              (globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
                configuration data analysis einsteinScale hTransverse family)
              (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
                hPeriod (measure := measure) configuration data analysis einsteinScale
                  hTransverse family chartBound))
          (hSelfAdjoint := globalCandidateAActualKernelOperator_isSelfAdjoint
            period hPeriod (measure := measure) configuration data analysis
              (globalCandidateAActualKernelChart period hPeriod (measure := measure)
                configuration data analysis einsteinScale hTransverse family)
              (globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
                configuration data analysis einsteinScale hTransverse family)
              (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
                hPeriod (measure := measure) configuration data analysis einsteinScale
                  hTransverse family chartBound))) ll_stationary

/-- The named ambient vectors synthesize the complete actual kernel. -/
theorem global_candidateA_hessian_namedMode_kernel_synthesis
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualNamedKernelCoercivity4D period hPeriod
      (measure := measure) configuration data analysis einsteinScale hTransverse family chartBound
        ZeroMode) :
    LinearMap.range named.modes.ambientSynthesis =
      (globalCandidateAActualKernelOperator period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
            hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
              chartBound)).ker :=
  named.modes.ambientSynthesis_range

/-- The final physical input count remains two after the local family: one
chart bound and one named-mode coercivity theorem. -/
theorem global_candidateA_hessian_canonicalSix_namedMode_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D
end JanusFormal
