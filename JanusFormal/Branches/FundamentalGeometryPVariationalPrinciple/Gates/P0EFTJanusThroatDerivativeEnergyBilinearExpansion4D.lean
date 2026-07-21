import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-! Exact two-direction polarization of the throat derivative energy. -/

namespace JanusFormal
namespace P0EFTJanusThroatDerivativeEnergyBilinearExpansion4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- Exact pointwise expansion for two independent affine field directions. -/
theorem throatDerivativeEnergy_twoDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field first second : SmoothThroatField period hPeriod LLFieldFiber)
    (s t : Real) (point : EffectiveThroat period hPeriod) :
    throatDerivativeEnergy period hPeriod frame
        (field + s • first + t • second) point =
      throatDerivativeEnergy period hPeriod frame field point +
        2 * s * throatDerivativePairing period hPeriod frame field first point +
        2 * t * throatDerivativePairing period hPeriod frame field second point +
        s ^ 2 * throatDerivativeEnergy period hPeriod frame first point +
        t ^ 2 * throatDerivativeEnergy period hPeriod frame second point +
        2 * s * t * throatDerivativePairing period hPeriod frame first second point := by
  unfold throatDerivativeEnergy throatDerivativePairing
  simp_rw [throatFrameDerivative_add, throatFrameDerivative_smul]
  simp only [Pi.add_apply, Pi.smul_apply, inner_add_left, norm_add_sq_real,
    real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The cross coefficient is symmetric in the two directions. -/
theorem throatDerivativePairing_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame first second point =
      throatDerivativePairing period hPeriod frame second first point := by
  unfold throatDerivativePairing
  apply Finset.sum_congr rfl
  intro index _
  exact real_inner_comm _ _

end
end P0EFTJanusThroatDerivativeEnergyBilinearExpansion4D
end JanusFormal
