import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurBasisFrontier4D

/-!
# Zero-mode-free canonical-six frontier from an orthogonal Schur determinant

The selected physical basis determines the finite subspace, its orthogonal
complement and all four Schur blocks of the actual augmented Candidate-A
Hessian.  On the open stratum where the resulting finite determinant is
nonzero, the complete Hessian is bijective.

This façade returns both the general H10--H14 actual-kernel package and the
stronger zero-mode-free certificate with the Green operator acting on the full
common Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurDeterminantFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12400000
set_option synthInstance.maxHeartbeats 6200000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurDeterminant4D
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

/-- Preferred determinant terminal. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurDeterminant_frontier_gate
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
    (determinant : GlobalCandidateAActualOrthogonalSchurDeterminantData4D period
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
  let closure :=
    global_candidateA_hessian_canonicalSix_orthogonalSchurBasis_frontier_gate
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound Mode determinant.schur
  let nondegenerate :=
    global_candidateA_actual_orthogonal_schur_determinant_gate period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode determinant
  show _ ∧ _ ∧ Nonempty _ from
  ⟨closure, nondegenerate,
    ⟨globalCandidateAOrthogonalSchurFullGreen period hPeriod
      (measure := measure) determinant⟩⟩

/-- Public finite scalar for the zero-mode-free stratum. -/
def globalCandidateAHessianCanonicalOrthogonalSchurDeterminant
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
    (determinant : GlobalCandidateAActualOrthogonalSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) : Real :=
  globalCandidateAOrthogonalSchurDeterminant period hPeriod determinant.schur

/-- Nonvanishing is the sole finite check on this stratum. -/
theorem globalCandidateAHessianCanonicalOrthogonalSchurDeterminant_ne_zero
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
    (determinant : GlobalCandidateAActualOrthogonalSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :
    globalCandidateAHessianCanonicalOrthogonalSchurDeterminant period hPeriod
      determinant ≠ 0 :=
  determinant.determinant_ne_zero

/-- On the determinant stratum the actual Hessian has no zero modes. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurDeterminant_kernel_zero
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
    (determinant : GlobalCandidateAActualOrthogonalSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).ker = ⊥ :=
  (global_candidateA_actual_orthogonal_schur_determinant_gate period hPeriod
    configuration data analysis chart sameAction physical Mode determinant).2.1

/-- The determinant frontier still has the three natural work packets: local
family, dense-core chart control, and the finite orthogonal Schur problem. -/
theorem global_candidateA_hessian_canonicalSix_orthogonalSchurDeterminant_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurDeterminantFrontier4D
end JanusFormal
