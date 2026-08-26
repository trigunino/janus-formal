import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCL2CorePairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D

/-!
# L2 pairing on the full shared-metric gauge-fixed core

The bulk pairing already contains the common metric and all gauge-fixed BRST,
LL and finite SpinC coordinates.  It is therefore supplemented only by the
separate D10 inner product and the L2 inner product of the normal displacement.
The duplicated boundary presentation of the metric is not counted twice.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCL2CorePairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Positive common-core pairing.  The three displayed summands occupy the
bulk, D10 and boundary-normal coordinates, respectively. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) : Real :=
  globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
      analysis first.1.1.1 second.1.1.1 +
    inner Real first.1.1.2 second.1.1.2 +
    inner Real
      (candidateANormalBoundaryNormalL2LinearMap
        period hPeriod first.1.2.2)
      (candidateANormalBoundaryNormalL2LinearMap
        period hPeriod second.1.2.2)

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_symm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis first second =
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis second first := by
  unfold
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
  rw [globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_symm]
  simp only [real_inner_comm]

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_add_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second third :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis (first + second) third =
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis first third +
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis second third := by
  unfold
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
  change
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis (first.1.1.1 + second.1.1.1) third.1.1.1 +
        inner Real (first.1.1.2 + second.1.1.2) third.1.1.2 +
      inner Real
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod
          (first.1.2.2 + second.1.2.2))
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod
          third.1.2.2) =
      (globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
            analysis first.1.1.1 third.1.1.1 +
          inner Real first.1.1.2 third.1.1.2 +
        inner Real
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod
            first.1.2.2)
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod
            third.1.2.2)) +
      (globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
            analysis second.1.1.1 third.1.1.1 +
          inner Real second.1.1.2 third.1.1.2 +
        inner Real
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod
            second.1.2.2)
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod
            third.1.2.2))
  rw [globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_add_left]
  simp only [map_add, inner_add_left]
  ring

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_smul_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (scalar : Real)
    (first second :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis (scalar • first) second =
      scalar *
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis first second := by
  unfold
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
  change
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis (scalar • first.1.1.1) second.1.1.1 +
        inner Real (scalar • first.1.1.2) second.1.1.2 +
      inner Real
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod
          (scalar • first.1.2.2))
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod
          second.1.2.2) =
      scalar *
        (globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
            analysis first.1.1.1 second.1.1.1 +
          inner Real first.1.1.2 second.1.1.2 +
          inner Real
            (candidateANormalBoundaryNormalL2LinearMap period hPeriod
              first.1.2.2)
            (candidateANormalBoundaryNormalL2LinearMap period hPeriod
              second.1.2.2))
  rw [globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_smul_left]
  simp only [map_smul, real_inner_smul_left]
  ring

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_nonneg
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    0 ≤
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis core core := by
  unfold
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
  exact add_nonneg
    (add_nonneg
      (globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_nonneg
        period hPeriod data analysis core.1.1.1)
      real_inner_self_nonneg)
    real_inner_self_nonneg

/-- Nondegeneracy of the full pairing.  Vanishing of the bulk block kills the
common metric; the pullback equation then kills its duplicate boundary
presentation. -/
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_eq_zero_iff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis core core = 0 ↔
      core = 0 := by
  constructor
  · intro hZero
    have hBulkNonneg :
        0 ≤ globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod
          data analysis core.1.1.1 core.1.1.1 :=
      globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_nonneg
        period hPeriod data analysis core.1.1.1
    have hD10Nonneg : 0 ≤ inner Real core.1.1.2 core.1.1.2 :=
      real_inner_self_nonneg
    have hNormalNonneg :
        0 ≤ inner Real
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2)
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2) :=
      real_inner_self_nonneg
    have hBulkZero :
        globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis core.1.1.1 core.1.1.1 = 0 := by
      unfold
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        at hZero
      nlinarith
    have hD10Zero : inner Real core.1.1.2 core.1.1.2 = 0 := by
      unfold
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        at hZero
      nlinarith
    have hNormalZero :
        inner Real
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2)
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2) = 0 := by
      unfold
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        at hZero
      nlinarith
    have hBulk : core.1.1.1 = 0 :=
      (globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_eq_zero_iff
        period hPeriod data analysis core.1.1.1).mp hBulkZero
    have hD10 : core.1.1.2 = 0 := inner_self_eq_zero.mp hD10Zero
    have hNormalImage :
        candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2 = 0 :=
      inner_self_eq_zero.mp hNormalZero
    have hNormal : core.1.2.2 = 0 := by
      apply candidateANormalBoundaryNormalL2LinearMap_injective
        period hPeriod
      simpa using hNormalImage
    have hAgreement :=
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_agreement
        period hPeriod analysis core
    have hMetric : core.1.2.1 = 0 := by
      have hSector := congrFun hAgreement Sector.plus
      rw [hBulk] at hSector
      change
        (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) =
          core.1.2.1 at hSector
      exact hSector.symm
    apply Subtype.ext
    exact Prod.ext (Prod.ext hBulk hD10) (Prod.ext hMetric hNormal)
  · rintro rfl
    change
      globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
            analysis
            (0 : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
              analysis) 0 +
          inner Real
            (0 : ProgramPD10ModeHilbert4D
              (d10SpectralData period hPeriod
                configuration.physical.d10Completion)) 0 +
        inner Real
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod 0)
          (candidateANormalBoundaryNormalL2LinearMap period hPeriod 0) = 0
    rw [(globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_eq_zero_iff
      period hPeriod data analysis 0).2 rfl]
    simp

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D
end JanusFormal
