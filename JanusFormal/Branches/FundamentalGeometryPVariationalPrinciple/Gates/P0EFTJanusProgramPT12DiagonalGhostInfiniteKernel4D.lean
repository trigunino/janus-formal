import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D

/-! For positive period, shared-ghost cancellation gives an infinite-dimensional actual augmented kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalGhostInfiniteKernel4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPT12DiagonalGhostCancellation4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
set_option backward.isDefEq.respectTransparency false

open P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D
open P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D

variable [Fact (0 < period)]
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
  NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
  hPeriod configuration data analysis chart sameAction)

/-- H11 does not restore a finite kernel in the equal-metric, opposite-weight
regime. The infinitude is proved for the actual smooth ghosts. -/
theorem diagonalGhost_augmented_kernel_not_finiteDimensional
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0) :
    ¬ FiniteDimensional Real
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker := by
  intro hFinite
  letI := hFinite
  obtain ⟨inclusion, hInjective⟩ := diagonalGhost_injects_into_augmented_kernel
    period hPeriod configuration data analysis chart sameAction physical hMetric hWeights
  exact smoothDiffeomorphismGhost_not_finiteDimensional period hPeriod
    (FiniteDimensional.of_injective inclusion hInjective)

/-- An injective linear transport of this kernel into a finite-dimensional
reference kernel is impossible. -/
theorem diagonalGhost_no_finite_kernel_transport
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    {F : Type*} [AddCommGroup F] [Module Real F] [FiniteDimensional Real F] :
    ¬ ∃ transport :
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker →ₗ[Real] F,
      Function.Injective transport := by
  rintro ⟨transport, hInjective⟩
  exact diagonalGhost_augmented_kernel_not_finiteDimensional period hPeriod
    configuration data analysis chart sameAction physical hMetric hWeights
    (FiniteDimensional.of_injective transport hInjective)

end
end P0EFTJanusProgramPT12DiagonalGhostInfiniteKernel4D
end JanusFormal
