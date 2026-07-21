import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActualHelmholtz4D

/-!
# Inactive-sector kernel of the actual matter + Robin + LL Hessian

Only the kernel contributed by metric, gauge, ghost, and auxiliary directions
is asserted.  This is the Hessian of the existing matter + Robin + LL action,
not a Hessian of the complete Candidate-A action.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLInactiveSectorKernel4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLActualHelmholtz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The direction has no component in any sector on which this exact action
depends. Metric, gauge, ghost, and auxiliary components remain unrestricted. -/
def MatterRobinLLInactive
    (direction : MatterRobinLLEnrichedDirections period hPeriod) : Prop :=
  direction.common.matter = 0 ∧ direction.robin = 0 ∧ direction.common.ll = 0

/-- Such a direction lies in the left kernel of the actual assembled Hessian. -/
theorem commonMatterRobinLLHessian_left_kernel
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (inactive test : MatterRobinLLEnrichedDirections period hPeriod)
    (hInactive : MatterRobinLLInactive period hPeriod inactive) :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields inactive test = 0 := by
  rcases hInactive with ⟨hMatter, hRobin, hLL⟩
  have hQuotientZeroMatter : ∀ point,
      (0 : SmoothQuotientField period hPeriod MatterFiber) point = 0 :=
    fun _ => rfl
  have hQuotientZeroReal : ∀ point,
      (0 : SmoothQuotientField period hPeriod Real) point = 0 :=
    fun _ => rfl
  have hMatterZero :
      matterVariationComponentFamily period hPeriod
          (0 : SmoothQuotientField period hPeriod MatterFiber ×
            SmoothQuotientField period hPeriod MatterFiber) = 0 := by
    funext component
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    simp [matterVariationComponentFamily, hQuotientZeroMatter,
      hQuotientZeroReal]
  have hThroatZeroReal : ∀ point : EffectiveThroat period hPeriod,
      (0 : SmoothThroatField period hPeriod Real) point = 0 := fun _ => rfl
  have hThroatZeroLL : ∀ point : EffectiveThroat period hPeriod,
      (0 : SmoothThroatField period hPeriod LLFieldFiber) point = 0 := fun _ => rfl
  have hPTZero :
      differentialLLFluxDirectionPT period hPeriod
          (0 : SmoothThroatField period hPeriod LLFieldFiber) = 0 := by
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro point
    rfl
  have hDerivativeZero
      (other : SmoothThroatField period hPeriod LLFieldFiber)
      (point : EffectiveThroat period hPeriod) :
      throatDerivativePairing period hPeriod frame 0 other point = 0 := by
    have hAffine := throatDerivativePairing_fluxCurve_affine period hPeriod
      frame 0 0 other 1 point
    simp only [one_smul, zero_add, one_mul] at hAffine
    linarith
  unfold commonMatterRobinLLHessian matterRobinLLHessian
  rw [hMatter, hRobin, hLL]
  rw [hMatterZero]
  simp [matterVariationComponentFamily, globalMatterMultipletHessian,
    robinHessian, robinHessianDensity,
    globalPTSymmetricDifferentialLLFluxHessian,
    globalDifferentialLLFluxHessian, hThroatZeroReal, hThroatZeroLL,
    differentialLLFluxHessianDensity, hPTZero, hDerivativeZero]

/-- The same inactive direction lies in the right kernel, by the proved
Helmholtz symmetry of this exact Hessian. -/
theorem commonMatterRobinLLHessian_right_kernel
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (test inactive : MatterRobinLLEnrichedDirections period hPeriod)
    (hInactive : MatterRobinLLInactive period hPeriod inactive) :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields test inactive = 0 := by
  rw [commonMatterRobinLLHessian_symmetric period hPeriod matterData kPlus
    kMinus robinMeasure frame llMeasure fields test inactive]
  exact commonMatterRobinLLHessian_left_kernel period hPeriod matterData kPlus
    kMinus robinMeasure frame llMeasure fields inactive test hInactive

end

end P0EFTJanusCommonMatterRobinLLInactiveSectorKernel4D
end JanusFormal
