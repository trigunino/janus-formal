import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D

/-!
# T12 shifted LL Friedrichs reciprocal-square summability

The positive Friedrichs spectrum stays Schatten-two after every nonnegative
scalar shift.  This discharges the LL shifted coefficient estimate directly
from the existing unshifted inverse-square datum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal LinearPMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

namespace CanonicalLLFriedrichsInverseSquareData

/-- Every eigenvalue in the existing LL Friedrichs inverse-square datum is
strictly positive. -/
theorem eigenvalue_pos
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode)
    (mode : Mode) :
    0 < spectral.eigenvalue mode := by
  let eigenvector := spectral.basis mode
  let domainVector :
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
    ⟨eigenvector, spectral.basis_mem_domain mode⟩
  have hInverse :
      canonicalLLWeakL2Inverse period hPeriod analysis
          (spectral.eigenvalue mode • eigenvector) =
        eigenvector := by
    calc
      canonicalLLWeakL2Inverse period hPeriod analysis
          (spectral.eigenvalue mode • eigenvector) =
          canonicalLLWeakL2Inverse period hPeriod analysis
            (canonicalLLFriedrichsJacobi period hPeriod analysis domainVector) := by
              rw [spectral.operator_on_basis]
      _ = eigenvector :=
        canonicalLLWeakL2Inverse_friedrichsJacobi
          period hPeriod analysis domainVector
  have hPairing := canonicalLLWeakL2Inverse_pairing
    period hPeriod analysis (spectral.eigenvalue mode • eigenvector)
  have hNorm : ‖eigenvector‖ = 1 :=
    (HilbertBasis.orthonormal spectral.basis).1 mode
  rw [hInverse, real_inner_smul_left, real_inner_self_eq_norm_sq, hNorm] at hPairing
  norm_num at hPairing
  have hNonnegative : 0 ≤ spectral.eigenvalue mode := by
    rw [hPairing]
    positivity
  exact lt_of_le_of_ne hNonnegative
    (Ne.symm (spectral.eigenvalue_ne_zero mode))

/-- A nonnegative scalar shift preserves reciprocal-square summability of the
LL Friedrichs eigenvalues. -/
theorem shiftedInverseSquareSummable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode)
    (shift : Real) (hShift : 0 ≤ shift) :
    Summable (fun mode =>
      ((spectral.eigenvalue mode + shift) ^ 2)⁻¹) := by
  apply spectral.inverseSquareSummable.of_nonneg_of_le
  · intro mode
    exact inv_nonneg.mpr (sq_nonneg _)
  · intro mode
    have hEigenvalue := eigenvalue_pos period hPeriod spectral mode
    have hSquare :
        spectral.eigenvalue mode ^ 2 ≤
          (spectral.eigenvalue mode + shift) ^ 2 :=
      (sq_le_sq₀ hEigenvalue.le
        (add_nonneg hEigenvalue.le hShift)).2
          (le_add_of_nonneg_right hShift)
    exact inv_anti₀ (sq_pos_of_pos hEigenvalue) hSquare

/-- The shifted Friedrichs resolvent is diagonal in the supplied LL basis. -/
theorem shiftedResolvent_on_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode)
    (shift : Real) (hShift : 0 ≤ shift)
    (mode : Mode) :
    canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift hShift
        (spectral.basis mode) =
      (spectral.eigenvalue mode + shift)⁻¹ • spectral.basis mode := by
  let field : (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
    ⟨spectral.basis mode, spectral.basis_mem_domain mode⟩
  have hInverse := canonicalLLFriedrichsShiftedResolvent_left_inverse
    period hPeriod analysis shift hShift field
  have hOperator :
      canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift field =
        (spectral.eigenvalue mode + shift) • spectral.basis mode := by
    rw [canonicalLLFriedrichsShiftedJacobi_apply,
      spectral.operator_on_basis, add_smul]
  rw [hOperator, map_smul] at hInverse
  have hCoefficient : spectral.eigenvalue mode + shift ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg
      (eigenvalue_pos period hPeriod spectral mode) hShift)
  calc
    canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift hShift
        (spectral.basis mode) =
        (1 : Real) • canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift
          hShift (spectral.basis mode) := by simp
    _ = ((spectral.eigenvalue mode + shift)⁻¹ *
          (spectral.eigenvalue mode + shift)) •
        canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift
          hShift (spectral.basis mode) := by
      rw [inv_mul_cancel₀ hCoefficient]
    _ = (spectral.eigenvalue mode + shift)⁻¹ •
        ((spectral.eigenvalue mode + shift) •
          canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift
            hShift (spectral.basis mode)) := by rw [mul_smul]
    _ = (spectral.eigenvalue mode + shift)⁻¹ • spectral.basis mode := by
      rw [hInverse]

end CanonicalLLFriedrichsInverseSquareData

end
end P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D
end JanusFormal
