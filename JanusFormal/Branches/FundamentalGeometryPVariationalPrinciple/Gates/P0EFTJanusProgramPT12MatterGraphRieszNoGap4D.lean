import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRieszEigen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SelfAdjointModalGapBound4D

/-! The isolated signed SpinC graph Riesz operator has no kernel-complement norm gap. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphRieszNoGap4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal lp LinearPMap

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPT12MatterGraphRieszEigen4D
open P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D
open P0EFTJanusProgramPT12SelfAdjointModalGapBound4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

local instance matterRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

local instance matterL2GraphInnerProductSpace :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  Submodule.innerProductSpace
    (programPPrimitiveSpinCMatterL2GraphSubmodule period hPeriod massSquared)

local instance matterL2GraphCompleteSpace :
    CompleteSpace
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  l2MatterGraphCompleteSpace period hPeriod massSquared

theorem matterL2GraphRiesz_isSelfAdjoint :
    @IsSelfAdjoint
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared →L[Real]
        ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
      (@ContinuousLinearMap.instStarId Real
        (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
        inferInstance inferInstance
        (matterL2GraphInnerProductSpace period hPeriod massSquared)
        (matterL2GraphCompleteSpace period hPeriod massSquared))
      (matterL2GraphRiesz period hPeriod massSquared) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric Real
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
    inferInstance inferInstance
    (matterL2GraphInnerProductSpace period hPeriod massSquared)
    (matterL2GraphCompleteSpace period hPeriod massSquared)
    (matterL2GraphRiesz period hPeriod massSquared)).2
  intro first second
  change inner Real (matterL2GraphRiesz period hPeriod massSquared first) second =
    inner Real first (matterL2GraphRiesz period hPeriod massSquared second)
  calc
    _ = matterL2GraphForm period hPeriod massSquared first second :=
      matterL2GraphRiesz_pairing period hPeriod massSquared first second
    _ = matterL2GraphForm period hPeriod massSquared second first := by
      exact programPPrimitiveSpinCMatterGraphForm_comm period hPeriod massSquared
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared first)
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared second)
    _ = inner Real (matterL2GraphRiesz period hPeriod massSquared second) first :=
      (matterL2GraphRiesz_pairing period hPeriod massSquared second first).symm
    _ = _ := real_inner_comm _ _

theorem matterGraphSingle_one_ne_zero
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    programPPrimitiveSpinCMatterGraphSingle
      period hPeriod massSquared sector mode 1 ≠ 0 := by
  intro h
  have hValue := congrArg
    (fun x : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared =>
      x.1.1 (sector, mode)) h
  simp [programPPrimitiveSpinCMatterGraphSingle, lp.single_apply] at hValue

theorem matterL2GraphSingle_one_ne_zero
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm
      (programPPrimitiveSpinCMatterGraphSingle
        period hPeriod massSquared sector mode 1) ≠ 0 := by
  intro h
  have hGraph := congrArg
    (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared) h
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero] at hGraph
  exact matterGraphSingle_one_ne_zero period hPeriod massSquared sector mode hGraph

/-- The proper SpinC tower supplies arbitrarily small *nonzero* Riesz
eigenvalues; a zero-weight mode alone would not refute a kernel gap. -/
theorem exists_nonzero_matter_ratio_below
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ mode : PrimitiveSpinCGeometricSignedMode,
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared ≠ 0 ∧
      |(primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) /
        (1 + (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) ^ 2)| < epsilon := by
  obtain ⟨mode, hLarge⟩ := exists_matter_weight_above
    period hPeriod massSquared (1 / epsilon)
  let w := primitiveSpinCGeometricSignedKineticHessianWeight
    period hPeriod mode + massSquared
  have hAbs : 0 < |w| := lt_of_le_of_lt (by positivity) hLarge
  have hDen : 0 < 1 + w ^ 2 := by positivity
  have hRatio : |w / (1 + w ^ 2)| ≤ 1 / |w| := by
    rw [abs_div, abs_of_pos hDen]
    apply (div_le_div_iff₀ hDen hAbs).2
    nlinarith [sq_abs w]
  have hInv : 1 / |w| < epsilon := by
    apply (div_lt_iff₀ hAbs).2
    have h := (div_lt_iff₀ hEpsilon).1 hLarge
    nlinarith
  exact ⟨mode, abs_pos.mp hAbs, lt_of_le_of_lt hRatio hInv⟩

/-- The isolated graph Riesz map fails H12's norm-gap contract even after
removing its actual kernel. This does not concern the coupled full Hessian. -/
theorem no_matterL2GraphRiesz_kernelComplementGap :
    SelfAdjointKernelComplementGapData
      (matterL2GraphRiesz period hPeriod massSquared)
      (matterL2GraphRiesz_isSelfAdjoint period hPeriod massSquared) → False := by
  intro data
  obtain ⟨mode, hWeight, hSmall⟩ := exists_nonzero_matter_ratio_below
    period hPeriod massSquared data.gap data.gap_pos
  let eigenvalue :=
    (primitiveSpinCGeometricSignedKineticHessianWeight
      period hPeriod mode + massSquared) /
      (1 + (primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared) ^ 2)
  have hDen : 1 + (primitiveSpinCGeometricSignedKineticHessianWeight
    period hPeriod mode + massSquared) ^ 2 ≠ 0 := by positivity
  have hEigenvalue : eigenvalue ≠ 0 := div_ne_zero hWeight hDen
  have hEigen := matterL2GraphRiesz_single_eigen
    period hPeriod massSquared (.plus : Sector) mode
  have hVector := matterL2GraphSingle_one_ne_zero
    period hPeriod massSquared (.plus : Sector) mode
  have hFloor := gap_le_abs_nonzero_eigenvalue
    (matterL2GraphRiesz period hPeriod massSquared)
    (matterL2GraphRiesz_isSelfAdjoint period hPeriod massSquared)
    data hEigenvalue hVector hEigen
  exact (not_lt_of_ge hFloor) hSmall

end
end P0EFTJanusProgramPT12MatterGraphRieszNoGap4D
end JanusFormal
