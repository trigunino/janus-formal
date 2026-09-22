import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullQuotient4D

/-! The closed ghost--antighost quotient of the actual Hilbert space, with exact augmented pairing and residual kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D

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
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

abbrev SharedGhostPair := GlobalDiffeomorphismGhostField period hPeriod ×
  GlobalDiffeomorphismAntighostField period hPeriod

/-- The shared ghost and antighost, with zero metric and auxiliary slots. -/
def diagonalGhostPairState : SharedGhostPair period hPeriod →ₗ[Real]
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun pair := ⟨0, ⟨pair.1, pair.2, ⟨0⟩⟩⟩
  map_add' _ _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (zero_add _).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · rfl
      · rfl
      · exact (zero_add _).symm
  map_smul' scalar _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (smul_zero scalar).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · rfl
      · rfl
      · exact (smul_zero scalar).symm

def ghostPairCoreMap : SharedGhostPair period hPeriod →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (LinearMap.inl Real _ _).comp (diagonalGhostPairState period hPeriod)

/-- The actual embedding of the shared smooth ghost--antighost columns. -/
def actualGhostEmbedding : SharedGhostPair period hPeriod →ₗ[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis).comp
      (ghostPairCoreMap period hPeriod configuration analysis)

/-- Closure is necessary for a separated Hilbert quotient. -/
def closedGhostSubspace : Submodule Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (actualGhostEmbedding period hPeriod configuration data analysis).range.topologicalClosure

instance closedGhostSubspace_isClosed :
    IsClosed (closedGhostSubspace period hPeriod configuration data analysis :
      Set (CommonAugmentedHilbert period hPeriod configuration data analysis)) :=
  Submodule.isClosed_topologicalClosure _

abbrev ActualGhostQuotient :=
  CommonAugmentedHilbert period hPeriod configuration data analysis ⧸
    closedGhostSubspace period hPeriod configuration data analysis

def quotientGhostCoreMap :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
      ActualGhostQuotient period hPeriod configuration data analysis :=
  (closedGhostSubspace period hPeriod configuration data analysis).mkQ.comp
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)

theorem quotientGhostCoreMap_denseRange :
    DenseRange (quotientGhostCoreMap period hPeriod configuration data analysis) := by
  exact ((closedGhostSubspace period hPeriod configuration data analysis).mkQ_surjective.denseRange).comp
    (diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (closedGhostSubspace period hPeriod configuration data analysis).mkQL.continuous

theorem quotientGhostCoreMap_ghostPair_zero
    (pair : SharedGhostPair period hPeriod) :
    quotientGhostCoreMap period hPeriod configuration data analysis
      (ghostPairCoreMap period hPeriod configuration analysis pair) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.le_topologicalClosure _ ⟨pair, rfl⟩

variable (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
  NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
  hPeriod configuration data analysis chart sameAction)
variable (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
  globalCandidateAMetricBySector period hPeriod data .minus)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)

include hMetric hWeights in
theorem ghostPair_augmented_pairing_zero
    (pair : SharedGhostPair period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod
      configuration data analysis chart sameAction physical
      (actualGhostEmbedding period hPeriod configuration data analysis pair)
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis test) = 0 := by
  have hPhysical : diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
      period hPeriod configuration data analysis chart sameAction.chartBridge
      (ghostPairCoreMap period hPeriod configuration analysis pair) test = 0 := by
    unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
    have hTangent := diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero
      period hPeriod configuration data analysis (diagonalGhostPairState period hPeriod pair).nonminimal
    change diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis (ghostPairCoreMap period hPeriod configuration analysis pair) = 0 at hTangent
    rw [hTangent]
    simp
  have hDiagonal : globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
      couplings (globalCandidateAMetricBySector period hPeriod data)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) (diagonalGhostPairState period hPeriod pair))
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) test.1) = 0 := by
    rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
    simp only [globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
      globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]
    simp [globalDiffeomorphismOffShellHessian_apply,
      globalCandidateADiagonalDiffeomorphismSectorStateLinearMap,
      diagonalGhostPairState, hMetric, ← add_mul, hWeights]
  change globalCandidateACommonAugmentedHessian period hPeriod
    configuration data analysis chart sameAction physical
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
      (ghostPairCoreMap period hPeriod configuration analysis pair)) _ = 0
  rw [globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed,
    diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical, hPhysical, add_zero]
  simpa [diagonalExtendedBulkGraphHessianOnCore, diagonalExtendedBulkHessian_apply,
    ghostPairCoreMap] using hDiagonal

include hMetric hWeights in
theorem ghostPair_augmented_riesz_zero (pair : SharedGhostPair period hPeriod) :
    globalCandidateACommonAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical
      (actualGhostEmbedding period hPeriod configuration data analysis pair) = 0 := by
  have hRow : (globalCandidateACommonAugmentedHessian period hPeriod
      configuration data analysis chart sameAction physical
      (actualGhostEmbedding period hPeriod configuration data analysis pair) : _ → Real) = fun _ => 0 := by
    apply (diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis).equalizer
      (globalCandidateACommonAugmentedHessian period hPeriod
        configuration data analysis chart sameAction physical _).continuous continuous_const
    funext test
    exact ghostPair_augmented_pairing_zero period hPeriod configuration data analysis
      chart sameAction physical hMetric hWeights pair test
  apply ext_inner_right Real
  intro test
  rw [inner_zero_left, globalCandidateACommonAugmentedRieszOperator_pairing]
  exact congrFun hRow test

include hMetric hWeights in
/-- Continuity kills the entire closed ghost subspace, not only smooth ghosts. -/
theorem closedGhostSubspace_le_kernel :
    closedGhostSubspace period hPeriod configuration data analysis ≤
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro vector ⟨ghost, rfl⟩
    exact ghostPair_augmented_riesz_zero period hPeriod configuration
      data analysis chart sameAction physical hMetric hWeights ghost
  · exact ContinuousLinearMap.isClosed_ker _

/-- Descent of the same augmented Riesz through the closed ghost quotient. -/
def ghostQuotientRiesz :
    ActualGhostQuotient period hPeriod configuration data analysis →L[Real]
      ActualGhostQuotient period hPeriod configuration data analysis :=
  closedNullQuotientOperator
    (globalCandidateACommonAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical)
    (closedGhostSubspace period hPeriod configuration data analysis)
    (closedGhostSubspace_le_kernel period hPeriod configuration data analysis
      chart sameAction physical hMetric hWeights)

/-- Concrete intertwining by the quotient map; it is not injective on ghosts. -/
theorem ghostQuotientRiesz_mk
    (vector : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    ghostQuotientRiesz period hPeriod configuration data analysis
      chart sameAction physical hMetric hWeights
      ((closedGhostSubspace period hPeriod configuration data analysis).mkQ vector) =
      (closedGhostSubspace period hPeriod configuration data analysis).mkQ
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical vector) := rfl

theorem ghostQuotientRiesz_isSelfAdjoint :
    IsSelfAdjoint (ghostQuotientRiesz period hPeriod configuration data analysis
      chart sameAction physical hMetric hWeights) :=
  closedNullQuotientOperator_isSelfAdjoint _
    (globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical) _ _

/-- All augmented pairings, including H11, are unchanged on quotient classes. -/
theorem ghostQuotientRiesz_pairing
    (first second : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real
      (ghostQuotientRiesz period hPeriod configuration data analysis
        chart sameAction physical hMetric hWeights
        ((closedGhostSubspace period hPeriod configuration data analysis).mkQ first))
      ((closedGhostSubspace period hPeriod configuration data analysis).mkQ second) =
      globalCandidateACommonAugmentedHessian period hPeriod
        configuration data analysis chart sameAction physical first second := by
  rw [ghostQuotientRiesz, closedNullQuotientOperator_pairing _
    (globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)]
  exact globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
    configuration data analysis chart sameAction physical first second

theorem ghostQuotientRiesz_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    inner Real
      (ghostQuotientRiesz period hPeriod configuration data analysis
        chart sameAction physical hMetric hWeights
        (quotientGhostCoreMap period hPeriod configuration data analysis first))
      (quotientGhostCoreMap period hPeriod configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second := by
  rw [quotientGhostCoreMap, LinearMap.comp_apply, LinearMap.comp_apply,
    ghostQuotientRiesz_pairing]
  exact globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period hPeriod
    configuration data analysis chart sameAction physical first second

/-- Other zero modes remain visible after the ghost reduction. -/
theorem ghostQuotientRiesz_kernel :
    (ghostQuotientRiesz period hPeriod configuration data analysis
      chart sameAction physical hMetric hWeights).ker =
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker.map
          (closedGhostSubspace period hPeriod configuration data analysis).mkQ :=
  closedNullQuotientOperator_kernel _
    (globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical) _ _

end
end P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D
end JanusFormal
