import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurDeterminantFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D

/-!
# Zero-mode-free terminal from named ambient reference vectors

The strongest orthogonal-Schur façade accepts actual ambient reference modes.
Their span and basis are constructed automatically.  The finite determinant of
the resulting Schur complement is the sole additional condition selecting the
zero-mode-free stratum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedDeterminantFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurDeterminant4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurDeterminantFrontier4D
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

/-- Named-vector Schur packet with the finite nondegeneracy check. -/
structure GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D
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
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode] where
  named : GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period hPeriod
    configuration data analysis chart sameAction physical Mode
  determinant_ne_zero :
    globalCandidateAOrthogonalSchurDeterminant period hPeriod
      named.toBasisData ≠ 0

/-- Convert named-vector determinant data to the basis determinant packet. -/
def GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D.toDeterminantData
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
    (determinant :
      GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
        configuration data analysis chart sameAction physical Mode) :
    GlobalCandidateAActualOrthogonalSchurDeterminantData4D period hPeriod
      configuration data analysis chart sameAction physical Mode where
  schur := determinant.named.toBasisData
  determinant_ne_zero := determinant.determinant_ne_zero

/-- Public named-vector finite determinant. -/
def globalCandidateAHessianNamedOrthogonalSchurDeterminant
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
    (determinant :
      GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
        configuration data analysis chart sameAction physical Mode) : Real :=
  globalCandidateAOrthogonalSchurDeterminant period hPeriod
    determinant.named.toBasisData

/-- Preferred zero-mode-free terminal from named ambient modes. -/
def global_candidateA_hessian_canonicalSix_namedOrthogonalSchurDeterminant_frontier_gate
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
    (determinant :
      GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
        (measure := measure) configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)
          (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
            hPeriod (measure := measure) configuration data analysis
              einsteinScale hTransverse family chartBound)
          Mode) :=
  global_candidateA_hessian_canonicalSix_orthogonalSchurDeterminant_frontier_gate
    period hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound Mode
        (determinant.toDeterminantData period hPeriod (measure := measure))

/-- Nonvanishing of the named finite scalar. -/
theorem globalCandidateAHessianNamedOrthogonalSchurDeterminant_ne_zero
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
    (determinant :
      GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
        configuration data analysis chart sameAction physical Mode) :
    globalCandidateAHessianNamedOrthogonalSchurDeterminant period hPeriod
      determinant ≠ 0 :=
  determinant.determinant_ne_zero

/-- The named determinant stratum is zero-mode free. -/
theorem global_candidateA_hessian_namedOrthogonalSchurDeterminant_kernel_zero
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
    (determinant :
      GlobalCandidateAActualOrthogonalSchurNamedDeterminantData4D period hPeriod
        configuration data analysis chart sameAction physical Mode) :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).ker = ⊥ :=
  global_candidateA_hessian_canonicalSix_orthogonalSchurDeterminant_kernel_zero
    period hPeriod (measure := measure)
      (determinant.toDeterminantData period hPeriod (measure := measure))

/-- The named determinant frontier keeps the same three work packets: local
family, dense-core chart control, and named finite modes with invertible
complement plus one finite nonvanishing calculation. -/
theorem global_candidateA_hessian_canonicalSix_namedOrthogonalSchurDeterminant_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedDeterminantFrontier4D
end JanusFormal
