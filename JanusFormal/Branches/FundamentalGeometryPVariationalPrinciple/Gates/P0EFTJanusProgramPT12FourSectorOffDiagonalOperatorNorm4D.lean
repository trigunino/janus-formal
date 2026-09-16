import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedFourSectorSelfAdjointResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualPhysicalRieszCoreBound4D

/-! The canonical four-sector pinching is contractive, so its off-diagonal
remainder is bounded by twice the norm of the physical Riesz operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FourSectorOffDiagonalOperatorNorm4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPT12DiagonalExtendedFourSectorSelfAdjointResolution4D

variable {Sector E : Type*} [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The diagonal compression of a bounded operator along a finite resolution. -/
def diagonalCompression
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (F : E →L[Real] E) : E →L[Real] E :=
  ∑ s : Sector, (resolution.projection s).comp
    (F.comp (resolution.projection s))

private theorem sum_projection_norm_mul_le
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (x y : E) :
    (∑ s : Sector, ‖resolution.projection s x‖ *
      ‖resolution.projection s y‖) ≤ ‖x‖ * ‖y‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Sector)
    (fun s => ‖resolution.projection s x‖)
    (fun s => ‖resolution.projection s y‖)
  rw [← resolution.norm_sq_decomposition x,
    ← resolution.norm_sq_decomposition y, ← mul_pow] at h
  exact le_of_sq_le_sq h (mul_nonneg (norm_nonneg x) (norm_nonneg y))

/-- Pinching by symmetric projections does not increase operator norm. -/
theorem diagonalCompression_norm_le
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (F : E →L[Real] E) :
    ‖diagonalCompression resolution F‖ ≤ ‖F‖ := by
  apply (diagonalCompression resolution F).opNorm_le_bound (norm_nonneg F)
  intro x
  let T := diagonalCompression resolution F
  have hinner : ‖T x‖ ^ 2 ≤
      ‖F‖ * ‖x‖ * ‖T x‖ := by
    calc
      ‖T x‖ ^ 2 = inner Real (T x) (T x) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∑ s : Sector,
          inner Real (F (resolution.projection s x))
            (resolution.projection s (T x)) := by
        simp only [T, diagonalCompression, sum_apply,
          ContinuousLinearMap.comp_apply, sum_inner]
        apply Finset.sum_congr rfl
        intro s _
        exact resolution.projection_symmetric s _ _
      _ ≤ ∑ s : Sector,
          ‖F‖ * ‖resolution.projection s x‖ *
            ‖resolution.projection s (T x)‖ := by
        apply Finset.sum_le_sum
        intro s _
        calc
          inner Real (F (resolution.projection s x))
              (resolution.projection s (T x))
              ≤ ‖F (resolution.projection s x)‖ *
                  ‖resolution.projection s (T x)‖ := by
                exact le_trans (le_abs_self _)
                  (by simpa [Real.norm_eq_abs] using
                    (norm_inner_le_norm (𝕜 := Real)
                      (F (resolution.projection s x))
                      (resolution.projection s (T x))))
          _ ≤ (‖F‖ * ‖resolution.projection s x‖) *
                ‖resolution.projection s (T x)‖ := by
              gcongr
              exact F.le_opNorm _
      _ = ‖F‖ * (∑ s : Sector,
          ‖resolution.projection s x‖ *
            ‖resolution.projection s (T x)‖) := by
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]
      _ ≤ ‖F‖ * ‖x‖ * ‖T x‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (sum_projection_norm_mul_le resolution x (T x)) (norm_nonneg F)
  have hnorm : ‖T x‖ ≤ ‖F‖ * ‖x‖ := by
    by_contra h
    have hlt : ‖F‖ * ‖x‖ < ‖T x‖ := lt_of_not_ge h
    have hpos : 0 < ‖T x‖ :=
      lt_of_le_of_lt (mul_nonneg (norm_nonneg F) (norm_nonneg x)) hlt
    have hm := mul_pos (sub_pos.mpr hlt) hpos
    nlinarith
  exact hnorm

/-- The entire off-diagonal remainder has at most twice the operator norm. -/
theorem offDiagonal_norm_le_two
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (F : E →L[Real] E) :
    ‖F - diagonalCompression resolution F‖ ≤ 2 * ‖F‖ := by
  calc
    ‖F - diagonalCompression resolution F‖ ≤
        ‖F‖ + ‖diagonalCompression resolution F‖ := norm_sub_le _ _
    _ ≤ ‖F‖ + ‖F‖ := add_le_add_right
      (diagonalCompression_norm_le resolution F) _
    _ = 2 * ‖F‖ := by ring

section Physical

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPT12ActualPhysicalRieszCoreBound4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace
  diagonalL2DiffeomorphismNormedAddCommGroup
  diagonalL2DiffeomorphismInnerProductSpace
  diagonalL2AbelianInnerProductSpace
  diagonalL2MatterInnerProductSpace
  diagonalL2LLInnerProductSpace
  diagonalL2ExtendedBulkNormedAddCommGroup
  diagonalL2ExtendedBulkInnerProductSpace

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

/-- The physical Riesz operator, viewed on the literal four-factor graph. -/
def physicalRieszOnFourGraph
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis →L[Real]
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis := by
  exact globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
    configuration data analysis chart sameAction
    (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
      configuration data analysis chart sameAction bound)

/-- H11 bounds the physical four-sector off-diagonal operator by twice
its core constant. -/
theorem physicalOffDiagonal_opNorm_le_two_coreConstant
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    let resolution := fourSectorSelfAdjointResolution
      (D := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod (globalCandidateAMetricBySector period hPeriod data))
      (A := GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data))
      (M := ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
        couplings.matterMassSquared)
      (L := GlobalFullLLGraphHilbert period hPeriod data analysis)
    let R := physicalRieszOnFourGraph period hPeriod configuration data analysis
      chart sameAction bound
    ‖R - diagonalCompression resolution R‖ ≤ 2 * bound.constant := by
  dsimp only
  have hR : ‖physicalRieszOnFourGraph period hPeriod configuration data analysis
      chart sameAction bound‖ ≤ bound.constant := by
    change ‖globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
        configuration data analysis chart sameAction bound)‖ ≤ bound.constant
    exact physicalRiesz_opNorm_le_coreConstant period hPeriod
      configuration data analysis chart sameAction bound
  exact le_trans
    (offDiagonal_norm_le_two _
      (physicalRieszOnFourGraph period hPeriod configuration data analysis chart
        sameAction bound))
    (mul_le_mul_of_nonneg_left hR (by norm_num))

end Physical

end
end P0EFTJanusProgramPT12FourSectorOffDiagonalOperatorNorm4D
end JanusFormal
