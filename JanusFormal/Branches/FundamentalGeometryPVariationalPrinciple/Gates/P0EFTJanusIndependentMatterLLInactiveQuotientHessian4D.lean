import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentMatterLLHessianBilinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

/-!
# Sectorial quotient descent of the common matter--LL Hessian

The actual matter plus differential-LL action is blind to the other slots of
the common independent tangent.  We identify that precise linear submodule and
descend its genuine Hessian algebraically.  This is not called a gauge quotient:
Maxwell and Einstein--Hilbert terms are absent, so entire gauge and metric slots
are inactive rather than merely gauge-equivalent.
-/

namespace JanusFormal
namespace P0EFTJanusIndependentMatterLLInactiveQuotientHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusIndependentMatterLLHessianBilinear4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact inactive submodule of the present matter--LL functional: both its
matter component family and its LL direction vanish. -/
def matterLLInvisibleSubmodule :
    Submodule Real (IndependentFieldVariation period hPeriod) :=
  LinearMap.ker (independentMatterComponentLinearMap period hPeriod) ⊓
    LinearMap.ker (independentLLFieldVariationLinearMap period hPeriod)

theorem mem_matterLLInvisibleSubmodule_iff
    (variation : IndependentFieldVariation period hPeriod) :
    variation ∈ matterLLInvisibleSubmodule period hPeriod ↔
      independentMatterComponentLinearMap period hPeriod variation = 0 ∧
      independentLLFieldVariationLinearMap period hPeriod variation = 0 := by
  simp only [matterLLInvisibleSubmodule, Submodule.mem_inf, LinearMap.mem_ker]

/-- The real matter--LL Hessian annihilates the inactive submodule on the left. -/
theorem matterLLHessian_zero_left
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (inactive direction : IndependentFieldVariation period hPeriod)
    (hInactive : inactive ∈ matterLLInvisibleSubmodule period hPeriod) :
    independentMatterLLHessianBilinear period hPeriod data frame fields mu
        inactive direction = 0 := by
  obtain ⟨hMatter, hLL⟩ :=
    (mem_matterLLInvisibleSubmodule_iff period hPeriod inactive).mp hInactive
  simp [independentMatterLLHessianBilinear,
    independentMatterHessianBilinear, independentLLHessianBilinear,
    pullbackBilinear, hMatter, hLL]

/-- The same Hessian annihilates the inactive submodule on the right. -/
theorem matterLLHessian_zero_right
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (inactive direction : IndependentFieldVariation period hPeriod)
    (hInactive : inactive ∈ matterLLInvisibleSubmodule period hPeriod) :
    independentMatterLLHessianBilinear period hPeriod data frame fields mu
        direction inactive = 0 := by
  obtain ⟨hMatter, hLL⟩ :=
    (mem_matterLLInvisibleSubmodule_iff period hPeriod inactive).mp hInactive
  simp [independentMatterLLHessianBilinear,
    independentMatterHessianBilinear, independentLLHessianBilinear,
    pullbackBilinear, hMatter, hLL]
  change weakLLJacobiOperator period hPeriod frame fields mu
      (independentLLFieldVariationLinearMap period hPeriod direction) 0 = 0
  exact map_zero _

/-- Algebraic descent to the quotient by exactly the slots invisible to the
present sectorial action. -/
def independentMatterLLInactiveQuotientHessian
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (IndependentFieldVariation period hPeriod ⧸
        matterLLInvisibleSubmodule period hPeriod) →ₗ[Real]
      (IndependentFieldVariation period hPeriod ⧸
        matterLLInvisibleSubmodule period hPeriod) →ₗ[Real] Real :=
  (independentMatterLLHessianBilinear period hPeriod data frame fields mu).liftQ₂
    (matterLLInvisibleSubmodule period hPeriod)
    (matterLLInvisibleSubmodule period hPeriod)
    (by
      intro inactive hInactive
      ext direction
      exact matterLLHessian_zero_left period hPeriod data frame fields mu
        inactive direction hInactive)
    (by
      intro inactive hInactive
      ext direction
      exact matterLLHessian_zero_right period hPeriod data frame fields mu
        inactive direction hInactive)

@[simp] theorem independentMatterLLInactiveQuotientHessian_mkQ
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod) :
    independentMatterLLInactiveQuotientHessian period hPeriod data frame fields mu
        ((matterLLInvisibleSubmodule period hPeriod).mkQ first)
        ((matterLLInvisibleSubmodule period hPeriod).mkQ second) =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu :=
  rfl

theorem independentMatterLLInactiveQuotientHessian_symmetric
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod ⧸
      matterLLInvisibleSubmodule period hPeriod) :
    independentMatterLLInactiveQuotientHessian period hPeriod data frame fields mu
        first second =
      independentMatterLLInactiveQuotientHessian period hPeriod data frame fields mu
        second first := by
  obtain ⟨first, rfl⟩ :=
    (matterLLInvisibleSubmodule period hPeriod).mkQ_surjective first
  obtain ⟨second, rfl⟩ :=
    (matterLLInvisibleSubmodule period hPeriod).mkQ_surjective second
  exact independentMatterLLHessianBilinear_symmetric period hPeriod data frame
    fields mu first second

/-- Every full gauge-slot direction lies in this inactive submodule.  This
records the absence of Maxwell dynamics; it is not gauge degeneracy of a
Maxwell Hessian. -/
theorem gaugeOnly_mem_matterLLInvisibleSubmodule
    (direction : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    gaugeOnlyIndependentVariation period hPeriod direction ∈
      matterLLInvisibleSubmodule period hPeriod := by
  rw [mem_matterLLInvisibleSubmodule_iff]
  constructor
  · funext component
    ext point
    simp [independentMatterComponentLinearMap, matterVariationComponentFamily,
      gaugeOnlyIndependentVariation]
    rfl
  · rfl

end
end P0EFTJanusIndependentMatterLLInactiveQuotientHessian4D
end JanusFormal
