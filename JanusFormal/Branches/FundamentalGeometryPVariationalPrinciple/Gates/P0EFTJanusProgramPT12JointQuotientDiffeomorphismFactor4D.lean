import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D

/-! The diagonal diffeomorphism factor modulo its closed shared ghost subspace. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
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

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismCompleteSpace

abbrev ActualDiffeomorphismHilbert := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
  period hPeriod (globalCandidateAMetricBySector period hPeriod data)

def actualDiffeomorphismReadout : CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
    ActualDiffeomorphismHilbert period hPeriod configuration data := WithLp.fstL 2 Real _ _

def actualDiffeomorphismInclusion : ActualDiffeomorphismHilbert period hPeriod configuration data →ₗᵢ[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis where
  toFun vector := WithLp.toLp 2 (vector, 0)
  map_add' first second := by
    change WithLp.toLp 2 (first + second, 0) = WithLp.toLp 2 (first + second, 0 + 0)
    rw [zero_add]
  map_smul' scalar vector := by
    change WithLp.toLp 2 (scalar • vector, 0) = WithLp.toLp 2 (scalar • vector, scalar • 0)
    rw [smul_zero]
  norm_map' vector := WithLp.norm_toLp_fst 2 _ _ vector

theorem actualDiffeomorphismInclusion_inner
    (vector : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (actualDiffeomorphismInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (actualDiffeomorphismReadout period hPeriod configuration data analysis test) := by
  change inner Real (WithLp.toLp 2 (vector, 0)) test = _
  simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero]
  rfl

def diffeomorphismGhostEmbedding : SharedGhostPair period hPeriod →ₗ[Real]
    ActualDiffeomorphismHilbert period hPeriod configuration data :=
  (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)).comp (diagonalGhostPairState period hPeriod)

def diffeomorphismGhostNullSpace : Submodule Real (ActualDiffeomorphismHilbert period hPeriod configuration data) :=
  (diffeomorphismGhostEmbedding period hPeriod configuration data).range.topologicalClosure

instance diffeomorphismGhostNullSpace_isClosed :
    IsClosed (diffeomorphismGhostNullSpace period hPeriod configuration data :
      Set (ActualDiffeomorphismHilbert period hPeriod configuration data)) :=
  Submodule.isClosed_topologicalClosure _

abbrev ReducedDiffeomorphismHilbert := ActualDiffeomorphismHilbert period hPeriod configuration data ⧸
  diffeomorphismGhostNullSpace period hPeriod configuration data

theorem actualDiffeomorphismInclusion_ghost (pair : SharedGhostPair period hPeriod) :
    actualDiffeomorphismInclusion period hPeriod configuration data analysis
      (diffeomorphismGhostEmbedding period hPeriod configuration data pair) =
      actualGhostEmbedding period hPeriod configuration data analysis pair := by
  change WithLp.toLp 2 (_, 0) = WithLp.toLp 2 (_, WithLp.toLp 2
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) 0,
      WithLp.toLp 2
        ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared).symm
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod couplings.matterMassSquared 0),
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis 0)))
  simp only [map_zero]
  rfl

theorem diffeomorphismNull_le_jointInclusion_kernel :
    diffeomorphismGhostNullSpace period hPeriod configuration data ≤
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.comp
        (actualDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro vector ⟨pair, rfl⟩
    change (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualDiffeomorphismInclusion period hPeriod configuration data analysis
        (diffeomorphismGhostEmbedding period hPeriod configuration data pair)) = 0
    rw [actualDiffeomorphismInclusion_ghost]
    exact jointGhostLLCoreMap_ghostPair_zero period hPeriod configuration data analysis pair
  · exact ContinuousLinearMap.isClosed_ker _

theorem jointNull_le_reducedDiffeomorphismReadout_kernel :
    jointGhostLLNullSpace period hPeriod configuration data analysis ≤
      ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQL.comp
        (actualDiffeomorphismReadout period hPeriod configuration data analysis)).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨aux, rfl⟩
        change (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ
          (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) 0) = 0
        rw [map_zero, map_zero]
      · exact ContinuousLinearMap.isClosed_ker _
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨pair, rfl⟩
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact Submodule.le_topologicalClosure _ ⟨pair, rfl⟩
      · exact ContinuousLinearMap.isClosed_ker _
  · exact ContinuousLinearMap.isClosed_ker _

def quotientDiffeomorphismReadout : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    ReducedDiffeomorphismHilbert period hPeriod configuration data :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).liftQL
    ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQL.comp
      (actualDiffeomorphismReadout period hPeriod configuration data analysis))
    (jointNull_le_reducedDiffeomorphismReadout_kernel period hPeriod configuration data analysis)

def quotientDiffeomorphismInclusionMap : ReducedDiffeomorphismHilbert period hPeriod configuration data →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  (diffeomorphismGhostNullSpace period hPeriod configuration data).liftQL
    ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.comp
      (actualDiffeomorphismInclusion period hPeriod configuration data analysis).toContinuousLinearMap)
    (diffeomorphismNull_le_jointInclusion_kernel period hPeriod configuration data analysis)

theorem actualDiffeomorphismInclusion_mem_orthogonal
    (vector : ActualDiffeomorphismHilbert period hPeriod configuration data)
    (hVector : vector ∈ (diffeomorphismGhostNullSpace period hPeriod configuration data)ᗮ) :
    actualDiffeomorphismInclusion period hPeriod configuration data analysis vector ∈
      (jointGhostLLNullSpace period hPeriod configuration data analysis)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro test hTest
  rw [actualDiffeomorphismInclusion_inner]
  exact ((diffeomorphismGhostNullSpace period hPeriod configuration data).mem_orthogonal' vector).mp
    hVector _ ((Submodule.Quotient.mk_eq_zero _).mp
      (jointNull_le_reducedDiffeomorphismReadout_kernel period hPeriod configuration data analysis hTest))

/-- The intrinsic ghost quotient is an isometric factor of the joint quotient. -/
def quotientDiffeomorphismInclusion : ReducedDiffeomorphismHilbert period hPeriod configuration data →ₗᵢ[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis where
  toLinearMap := (quotientDiffeomorphismInclusionMap period hPeriod configuration data analysis).toLinearMap
  norm_map' vector := by
    let nullSpace := diffeomorphismGhostNullSpace period hPeriod configuration data
    let representative := nullSpace.quotientEquivOrthogonal vector
    have hSame : nullSpace.mkQ (representative : ActualDiffeomorphismHilbert period hPeriod configuration data) = vector :=
      (nullSpace.quotientEquivOrthogonal_symm_eq_mk representative.1 representative.2).symm.trans
        (nullSpace.quotientEquivOrthogonal.symm_apply_apply vector)
    rw [← hSame]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact (inner_mk_of_left_orthogonal _ _ _
      (actualDiffeomorphismInclusion_mem_orthogonal period hPeriod configuration data analysis _ representative.2)).trans
      (((actualDiffeomorphismInclusion period hPeriod configuration data analysis).inner_map_map _ _).trans
        (inner_mk_of_left_orthogonal nullSpace _ _ representative.2).symm)

@[simp] theorem quotientDiffeomorphismInclusion_mk
    (vector : ActualDiffeomorphismHilbert period hPeriod configuration data) :
    quotientDiffeomorphismInclusion period hPeriod configuration data analysis
      ((diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ vector) =
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualDiffeomorphismInclusion period hPeriod configuration data analysis vector) := rfl

@[simp] theorem quotientDiffeomorphismReadout_inclusion
    (vector : ReducedDiffeomorphismHilbert period hPeriod configuration data) :
    quotientDiffeomorphismReadout period hPeriod configuration data analysis
      (quotientDiffeomorphismInclusion period hPeriod configuration data analysis vector) = vector := by
  obtain ⟨vector, rfl⟩ := (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ_surjective vector
  rfl

theorem quotientDiffeomorphismReadout_surjective : Function.Surjective
    (quotientDiffeomorphismReadout period hPeriod configuration data analysis) :=
  fun vector => ⟨quotientDiffeomorphismInclusion period hPeriod configuration data analysis vector,
    quotientDiffeomorphismReadout_inclusion period hPeriod configuration data analysis vector⟩

theorem quotientDiffeomorphismInclusion_inner
    (vector : ReducedDiffeomorphismHilbert period hPeriod configuration data)
    (test : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real (quotientDiffeomorphismInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (quotientDiffeomorphismReadout period hPeriod configuration data analysis test) := by
  let nullSpace := diffeomorphismGhostNullSpace period hPeriod configuration data
  let representative := nullSpace.quotientEquivOrthogonal vector
  have hSame : nullSpace.mkQ (representative : ActualDiffeomorphismHilbert period hPeriod configuration data) = vector :=
    (nullSpace.quotientEquivOrthogonal_symm_eq_mk representative.1 representative.2).symm.trans
      (nullSpace.quotientEquivOrthogonal.symm_apply_apply vector)
  rw [← hSame]
  obtain ⟨test, rfl⟩ := (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ_surjective test
  exact (inner_mk_of_left_orthogonal _ _ _
    (actualDiffeomorphismInclusion_mem_orthogonal period hPeriod configuration data analysis _ representative.2)).trans
    ((actualDiffeomorphismInclusion_inner period hPeriod configuration data analysis _ test).trans
      (inner_mk_of_left_orthogonal nullSpace _ _ representative.2).symm)

end
end
end P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
end JanusFormal
