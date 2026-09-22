import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianFactor4D

/-! Concrete orthogonal decomposition of every joint quotient vector into its three reduced sectors. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D
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

open P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12JointQuotientAbelianFactor4D

private theorem inner_three {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
    (first second third test : H) :
    inner Real (first + second + third) test =
      inner Real first test + inner Real second test + inner Real third test := by
  rw [inner_add_left, inner_add_left]

@[simp] theorem diffeomorphismReadout_abelianInclusion
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    quotientDiffeomorphismReadout period hPeriod configuration data analysis
      (quotientAbelianInclusion period hPeriod configuration data analysis vector) = 0 :=
  map_zero (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ

@[simp] theorem diffeomorphismReadout_matterLLInclusion
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis) :
    quotientDiffeomorphismReadout period hPeriod configuration data analysis
      (quotientMatterLLInclusion period hPeriod configuration data analysis vector) = 0 := by
  obtain ⟨vector, rfl⟩ := (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  exact map_zero (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ

@[simp] theorem abelianReadout_diffeomorphismInclusion
    (vector : ReducedDiffeomorphismHilbert period hPeriod configuration data) :
    quotientAbelianReadout period hPeriod configuration data analysis
      (quotientDiffeomorphismInclusion period hPeriod configuration data analysis vector) = 0 := by
  obtain ⟨vector, rfl⟩ := (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ_surjective vector
  rfl

@[simp] theorem abelianReadout_matterLLInclusion
    (vector : ReducedMatterLLHilbert period hPeriod configuration data analysis) :
    quotientAbelianReadout period hPeriod configuration data analysis
      (quotientMatterLLInclusion period hPeriod configuration data analysis vector) = 0 := by
  obtain ⟨vector, rfl⟩ := (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  rfl

@[simp] theorem matterLLReadout_diffeomorphismInclusion
    (vector : ReducedDiffeomorphismHilbert period hPeriod configuration data) :
    quotientMatterLLReadout period hPeriod configuration data analysis
      (quotientDiffeomorphismInclusion period hPeriod configuration data analysis vector) = 0 := by
  obtain ⟨vector, rfl⟩ := (diffeomorphismGhostNullSpace period hPeriod configuration data).mkQ_surjective vector
  exact map_zero (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ

@[simp] theorem matterLLReadout_abelianInclusion
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    quotientMatterLLReadout period hPeriod configuration data analysis
      (quotientAbelianInclusion period hPeriod configuration data analysis vector) = 0 :=
  map_zero (matterLLAuxNullSpace period hPeriod configuration data analysis).mkQ

/-- No quotient vectors remain outside the three concrete factors. -/
theorem jointQuotient_reconstruct
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    quotientDiffeomorphismInclusion period hPeriod configuration data analysis
      (quotientDiffeomorphismReadout period hPeriod configuration data analysis vector) +
    quotientAbelianInclusion period hPeriod configuration data analysis
      (quotientAbelianReadout period hPeriod configuration data analysis vector) +
    quotientMatterLLInclusion period hPeriod configuration data analysis
      (quotientMatterLLReadout period hPeriod configuration data analysis vector) = vector := by
  obtain ⟨vector, rfl⟩ := (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ_surjective vector
  change (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualDiffeomorphismInclusion period hPeriod configuration data analysis vector.fst) +
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualAbelianInclusion period hPeriod configuration data analysis vector.snd.fst) +
    (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
      (actualMatterLLInclusion period hPeriod configuration data analysis vector.snd.snd) = _
  rw [← map_add, ← map_add]
  apply congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
  change WithLp.toLp 2 (vector.fst + 0 + 0,
    WithLp.toLp 2 (0 + vector.snd.fst + 0, 0 + 0 + vector.snd.snd)) = vector
  simp only [zero_add, add_zero]
  rfl

/-- The quotient inner product is exactly the sum of the three sector inner products. -/
theorem jointQuotient_inner_decomposition
    (first second : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real first second =
      inner Real (quotientDiffeomorphismReadout period hPeriod configuration data analysis first)
        (quotientDiffeomorphismReadout period hPeriod configuration data analysis second) +
      inner Real (quotientAbelianReadout period hPeriod configuration data analysis first)
        (quotientAbelianReadout period hPeriod configuration data analysis second) +
      inner Real (quotientMatterLLReadout period hPeriod configuration data analysis first)
        (quotientMatterLLReadout period hPeriod configuration data analysis second) := by
  calc
    _ = inner Real
      (quotientDiffeomorphismInclusion period hPeriod configuration data analysis
        (quotientDiffeomorphismReadout period hPeriod configuration data analysis first) +
      quotientAbelianInclusion period hPeriod configuration data analysis
        (quotientAbelianReadout period hPeriod configuration data analysis first) +
      quotientMatterLLInclusion period hPeriod configuration data analysis
        (quotientMatterLLReadout period hPeriod configuration data analysis first)) second :=
      congrArg (fun vector => inner Real vector second)
        (jointQuotient_reconstruct period hPeriod configuration data analysis first).symm
    _ = _ := by
      exact (inner_three
        (quotientDiffeomorphismInclusion period hPeriod configuration data analysis
          (quotientDiffeomorphismReadout period hPeriod configuration data analysis first))
        (quotientAbelianInclusion period hPeriod configuration data analysis
          (quotientAbelianReadout period hPeriod configuration data analysis first))
        (quotientMatterLLInclusion period hPeriod configuration data analysis
          (quotientMatterLLReadout period hPeriod configuration data analysis first)) second).trans
        (congrArg₂ (· + ·)
        (congrArg₂ (· + ·)
          (quotientDiffeomorphismInclusion_inner period hPeriod configuration data analysis
            (quotientDiffeomorphismReadout period hPeriod configuration data analysis first) second)
          (quotientAbelianInclusion_inner period hPeriod configuration data analysis
            (quotientAbelianReadout period hPeriod configuration data analysis first) second))
        (quotientMatterLLInclusion_inner period hPeriod configuration data analysis
          (quotientMatterLLReadout period hPeriod configuration data analysis first) second))

theorem jointQuotient_norm_sq_decomposition
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    ‖vector‖ ^ 2 =
      ‖quotientDiffeomorphismReadout period hPeriod configuration data analysis vector‖ ^ 2 +
      ‖quotientAbelianReadout period hPeriod configuration data analysis vector‖ ^ 2 +
      ‖quotientMatterLLReadout period hPeriod configuration data analysis vector‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using
    jointQuotient_inner_decomposition period hPeriod configuration data analysis vector vector

/-- Each coordinate is recovered uniquely from an arbitrary sector reconstruction. -/
theorem jointQuotient_reconstruct_unique
    (diffeomorphism : ReducedDiffeomorphismHilbert period hPeriod configuration data)
    (abelian : ActualAbelianHilbert period hPeriod configuration data)
    (matterLL : ReducedMatterLLHilbert period hPeriod configuration data analysis)
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis)
    (hReconstruct : quotientDiffeomorphismInclusion period hPeriod configuration data analysis diffeomorphism +
      quotientAbelianInclusion period hPeriod configuration data analysis abelian +
      quotientMatterLLInclusion period hPeriod configuration data analysis matterLL = vector) :
    diffeomorphism = quotientDiffeomorphismReadout period hPeriod configuration data analysis vector ∧
    abelian = quotientAbelianReadout period hPeriod configuration data analysis vector ∧
    matterLL = quotientMatterLLReadout period hPeriod configuration data analysis vector := by
  constructor
  · simpa only [map_add, quotientDiffeomorphismReadout_inclusion,
      diffeomorphismReadout_abelianInclusion, diffeomorphismReadout_matterLLInclusion, add_zero] using
      congrArg (quotientDiffeomorphismReadout period hPeriod configuration data analysis) hReconstruct
  constructor
  · simpa only [map_add, quotientAbelianReadout_inclusion,
      abelianReadout_diffeomorphismInclusion, abelianReadout_matterLLInclusion, zero_add, add_zero] using
      congrArg (quotientAbelianReadout period hPeriod configuration data analysis) hReconstruct
  · simpa only [map_add, quotientMatterLLReadout_inclusion,
      matterLLReadout_diffeomorphismInclusion, matterLLReadout_abelianInclusion, zero_add] using
      congrArg (quotientMatterLLReadout period hPeriod configuration data analysis) hReconstruct

end
end
end P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D
end JanusFormal
