import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D

/-! The completed Abelian factor survives the joint null quotient isometrically. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
  P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D.programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

set_option backward.isDefEq.respectTransparency false
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D
open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D

open P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
open P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D

abbrev ActualAbelianHilbert := GlobalPairedAbelianOffShellGraphHilbert period hPeriod
  (globalCandidateAMetricBySector period hPeriod data)

def actualAbelianReadout : CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
    ActualAbelianHilbert period hPeriod configuration data :=
  (WithLp.fstL 2 Real _ _).comp (WithLp.sndL 2 Real _ _)

def actualAbelianInclusion : ActualAbelianHilbert period hPeriod configuration data →ₗᵢ[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis where
  toFun vector := WithLp.toLp 2 (0, WithLp.toLp 2 (vector, 0))
  map_add' first second := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (first + second, 0)) =
      WithLp.toLp 2 (0 + 0, WithLp.toLp 2 (first + second, 0 + 0))
    rw [zero_add, zero_add]
  map_smul' scalar vector := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (scalar • vector, 0)) =
      WithLp.toLp 2 (scalar • 0, WithLp.toLp 2 (scalar • vector, scalar • 0))
    rw [smul_zero, smul_zero]
  norm_map' vector :=
    (WithLp.norm_toLp_snd 2 _ _ _).trans (WithLp.norm_toLp_fst 2 _ _ vector)

@[simp] theorem actualAbelianReadout_inclusion
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    actualAbelianReadout period hPeriod configuration data analysis
      (actualAbelianInclusion period hPeriod configuration data analysis vector) = vector := rfl

theorem actualAbelianInclusion_inner
    (vector : ActualAbelianHilbert period hPeriod configuration data)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (actualAbelianInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (actualAbelianReadout period hPeriod configuration data analysis test) := by
  change inner Real (WithLp.toLp 2 (0, WithLp.toLp 2 (vector, 0))) test = _
  simp only [WithLp.prod_inner_apply, inner_zero_left, zero_add, add_zero]
  rfl

/-- Both discarded sectors have zero completed Abelian coordinate, including their closures. -/
theorem jointNull_le_abelianReadout_kernel :
    jointGhostLLNullSpace period hPeriod configuration data analysis ≤
      (actualAbelianReadout period hPeriod configuration data analysis).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨aux, rfl⟩
        change globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) 0 = 0
        exact map_zero _
      · exact ContinuousLinearMap.isClosed_ker _
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨pair, rfl⟩
        change globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) 0 = 0
        exact map_zero _
      · exact ContinuousLinearMap.isClosed_ker _
  · exact ContinuousLinearMap.isClosed_ker _

def quotientAbelianReadout : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    ActualAbelianHilbert period hPeriod configuration data :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).liftQL
    (actualAbelianReadout period hPeriod configuration data analysis)
    (jointNull_le_abelianReadout_kernel period hPeriod configuration data analysis)

@[simp] theorem quotientAbelianReadout_mk
    (vector : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    quotientAbelianReadout period hPeriod configuration data analysis
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ vector) =
        actualAbelianReadout period hPeriod configuration data analysis vector := rfl

theorem actualAbelianInclusion_mem_orthogonal
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    actualAbelianInclusion period hPeriod configuration data analysis vector ∈
      (jointGhostLLNullSpace period hPeriod configuration data analysis)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro test hTest
  rw [actualAbelianInclusion_inner]
  have hZero : actualAbelianReadout period hPeriod configuration data analysis test = 0 :=
    jointNull_le_abelianReadout_kernel period hPeriod configuration data analysis hTest
  rw [hZero, inner_zero_right]

/-- The inclusion is an isometry, not merely an algebraic map into the quotient. -/
def quotientAbelianInclusion : ActualAbelianHilbert period hPeriod configuration data →ₗᵢ[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis where
  toLinearMap := (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ.comp
    (actualAbelianInclusion period hPeriod configuration data analysis).toLinearMap
  norm_map' vector := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact (inner_mk_of_left_orthogonal _ _ _
      (actualAbelianInclusion_mem_orthogonal period hPeriod configuration data analysis vector)).trans
        ((actualAbelianInclusion period hPeriod configuration data analysis).inner_map_map vector vector)

@[simp] theorem quotientAbelianReadout_inclusion
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    quotientAbelianReadout period hPeriod configuration data analysis
      (quotientAbelianInclusion period hPeriod configuration data analysis vector) = vector := rfl

theorem quotientAbelianReadout_surjective : Function.Surjective
    (quotientAbelianReadout period hPeriod configuration data analysis) :=
  fun vector => ⟨quotientAbelianInclusion period hPeriod configuration data analysis vector, rfl⟩

theorem quotientAbelianInclusion_inner
    (vector : ActualAbelianHilbert period hPeriod configuration data)
    (test : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real (quotientAbelianInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (quotientAbelianReadout period hPeriod configuration data analysis test) := by
  obtain ⟨test, rfl⟩ :=
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ_surjective test
  exact (inner_mk_of_left_orthogonal _ _ _
    (actualAbelianInclusion_mem_orthogonal period hPeriod configuration data analysis vector)).trans
      (actualAbelianInclusion_inner period hPeriod configuration data analysis vector test)

end
end
end P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
end JanusFormal
