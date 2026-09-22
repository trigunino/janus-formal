import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullFactorIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D

/-! The completed matter--LL graph factor modulo the closed LL auxiliary/measure subspace. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
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

abbrev ActualMatterLLHilbert := ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis

def actualMatterLLReadout : CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
    ActualMatterLLHilbert period hPeriod configuration data analysis :=
  (WithLp.sndL 2 Real _ _).comp (WithLp.sndL 2 Real _ _)

def actualMatterLLInclusion : ActualMatterLLHilbert period hPeriod configuration data analysis →ₗᵢ[Real]
    CommonAugmentedHilbert period hPeriod configuration data analysis where
  toFun vector := WithLp.toLp 2 (0, WithLp.toLp 2 (0, vector))
  map_add' first second := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (0, first + second)) =
      WithLp.toLp 2 (0 + 0, WithLp.toLp 2 (0 + 0, first + second))
    rw [zero_add, zero_add]
  map_smul' scalar vector := by
    change WithLp.toLp 2 (0, WithLp.toLp 2 (0, scalar • vector)) =
      WithLp.toLp 2 (scalar • 0, WithLp.toLp 2 (scalar • 0, scalar • vector))
    rw [smul_zero, smul_zero]
  norm_map' vector := (WithLp.norm_toLp_snd 2 _ _ _).trans (WithLp.norm_toLp_snd 2 _ _ vector)

theorem actualMatterLLInclusion_inner
    (vector : ActualMatterLLHilbert period hPeriod configuration data analysis)
    (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (actualMatterLLInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (actualMatterLLReadout period hPeriod configuration data analysis test) := by
  change inner Real (WithLp.toLp 2 (0, WithLp.toLp 2 (0, vector))) test = _
  simp only [WithLp.prod_inner_apply, inner_zero_left, zero_add]
  rfl

def matterLLAuxEmbedding : GlobalLLAuxMeasureSmooth period hPeriod →ₗ[Real]
    ActualMatterLLHilbert period hPeriod configuration data analysis :=
  (actualMatterLLReadout period hPeriod configuration data analysis).toLinearMap.comp
    (actualAuxLLEmbedding period hPeriod configuration data analysis)

def matterLLAuxNullSpace : Submodule Real (ActualMatterLLHilbert period hPeriod configuration data analysis) :=
  (matterLLAuxEmbedding period hPeriod configuration data analysis).range.topologicalClosure

instance matterLLAuxNullSpace_isClosed :
    IsClosed (matterLLAuxNullSpace period hPeriod configuration data analysis :
      Set (ActualMatterLLHilbert period hPeriod configuration data analysis)) :=
  Submodule.isClosed_topologicalClosure _

abbrev ReducedMatterLLHilbert := ActualMatterLLHilbert period hPeriod configuration data analysis ⧸
  matterLLAuxNullSpace period hPeriod configuration data analysis

theorem actualMatterLLInclusion_aux (aux : GlobalLLAuxMeasureSmooth period hPeriod) :
    actualMatterLLInclusion period hPeriod configuration data analysis
      (matterLLAuxEmbedding period hPeriod configuration data analysis aux) =
      actualAuxLLEmbedding period hPeriod configuration data analysis aux := by
  change WithLp.toLp 2 (0, WithLp.toLp 2 (0, _)) =
    WithLp.toLp 2
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) 0,
      WithLp.toLp 2
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) 0, _))
  simp only [map_zero]
  rfl

theorem matterLLNull_le_jointInclusion_kernel :
    matterLLAuxNullSpace period hPeriod configuration data analysis ≤
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.comp
        (actualMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro vector ⟨aux, rfl⟩
    change (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualMatterLLInclusion period hPeriod configuration data analysis
        (matterLLAuxEmbedding period hPeriod configuration data analysis aux)) = 0
    rw [actualMatterLLInclusion_aux]
    exact jointGhostLLCoreMap_auxLL_zero period hPeriod configuration data analysis aux
  · exact ContinuousLinearMap.isClosed_ker _

theorem jointNull_le_reducedMatterLLReadout_kernel :
    jointGhostLLNullSpace period hPeriod configuration data analysis ≤
      ((matterLLAuxNullSpace period hPeriod configuration data analysis).mkQL.comp
        (actualMatterLLReadout period hPeriod configuration data analysis)).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨aux, rfl⟩
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact Submodule.le_topologicalClosure _ ⟨aux, rfl⟩
      · exact ContinuousLinearMap.isClosed_ker _
    · apply Submodule.topologicalClosure_minimal
      · rintro vector ⟨pair, rfl⟩
        change (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ
          (WithLp.toLp 2
            ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod couplings.matterMassSquared).symm
              (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod couplings.matterMassSquared 0),
            globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis 0)) = 0
        simp only [map_zero]
        exact map_zero _
      · exact ContinuousLinearMap.isClosed_ker _
  · exact ContinuousLinearMap.isClosed_ker _
def quotientMatterLLReadout : JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
    ReducedMatterLLHilbert period hPeriod configuration data analysis :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).liftQL
    ((matterLLAuxNullSpace period hPeriod configuration data analysis).mkQL.comp
      (actualMatterLLReadout period hPeriod configuration data analysis))
    (jointNull_le_reducedMatterLLReadout_kernel period hPeriod configuration data analysis)

def quotientMatterLLInclusionMap : ReducedMatterLLHilbert period hPeriod configuration data analysis →L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  (matterLLAuxNullSpace period hPeriod configuration data analysis).liftQL
    ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL.comp
      (actualMatterLLInclusion period hPeriod configuration data analysis).toContinuousLinearMap)
    (matterLLNull_le_jointInclusion_kernel period hPeriod configuration data analysis)

theorem actualMatterLLInclusion_mem_orthogonal
    (vector : ActualMatterLLHilbert period hPeriod configuration data analysis)
    (hVector : vector ∈ (matterLLAuxNullSpace period hPeriod configuration data analysis)ᗮ) :
    actualMatterLLInclusion period hPeriod configuration data analysis vector ∈
      (jointGhostLLNullSpace period hPeriod configuration data analysis)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro test hTest
  rw [actualMatterLLInclusion_inner]
  exact ((matterLLAuxNullSpace period hPeriod configuration data analysis).mem_orthogonal' vector).mp
    hVector _ ((Submodule.Quotient.mk_eq_zero _).mp
      (jointNull_le_reducedMatterLLReadout_kernel period hPeriod configuration data analysis hTest))

/-- The intrinsic matter--LL graph quotient is an isometric factor of the joint quotient. -/
def quotientMatterLLInclusion : ReducedMatterLLHilbert period hPeriod configuration data analysis →ₗᵢ[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  P0EFTJanusProgramPT12ClosedNullFactorIsometry4D.quotientFactorInclusion
    (actualMatterLLInclusion period hPeriod configuration data analysis)
    (matterLLAuxNullSpace period hPeriod configuration data analysis)
    (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (matterLLNull_le_jointInclusion_kernel period hPeriod configuration data analysis)
    (actualMatterLLInclusion_mem_orthogonal period hPeriod configuration data analysis)
@[simp] theorem quotientMatterLLInclusion_mk
    (vector : ActualMatterLLHilbert period hPeriod configuration data analysis) :
    quotientMatterLLInclusion period hPeriod configuration data analysis
      ((matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ vector) =
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualMatterLLInclusion period hPeriod configuration data analysis vector) := rfl

@[simp] theorem quotientMatterLLReadout_inclusion
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis) :
    quotientMatterLLReadout period hPeriod configuration data analysis
      (quotientMatterLLInclusion period hPeriod configuration data analysis vector) = vector := by
  obtain ⟨vector, rfl⟩ := (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  rfl

theorem quotientMatterLLReadout_surjective : Function.Surjective
    (quotientMatterLLReadout period hPeriod configuration data analysis) :=
  fun vector => ⟨quotientMatterLLInclusion period hPeriod configuration data analysis vector,
    quotientMatterLLReadout_inclusion period hPeriod configuration data analysis vector⟩

theorem quotientMatterLLInclusion_inner
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis)
    (test : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real (quotientMatterLLInclusion period hPeriod configuration data analysis vector) test =
      inner Real vector (quotientMatterLLReadout period hPeriod configuration data analysis test) :=
  P0EFTJanusProgramPT12ClosedNullFactorIsometry4D.quotientFactorInclusion_inner
    (actualMatterLLInclusion period hPeriod configuration data analysis)
    (matterLLAuxNullSpace period hPeriod configuration data analysis)
    (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (matterLLNull_le_jointInclusion_kernel period hPeriod configuration data analysis)
    (actualMatterLLInclusion_mem_orthogonal period hPeriod configuration data analysis)
    (actualMatterLLReadout period hPeriod configuration data analysis)
    (jointNull_le_reducedMatterLLReadout_kernel period hPeriod configuration data analysis)
    (actualMatterLLInclusion_inner period hPeriod configuration data analysis) vector test

end
end
end P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
end JanusFormal
