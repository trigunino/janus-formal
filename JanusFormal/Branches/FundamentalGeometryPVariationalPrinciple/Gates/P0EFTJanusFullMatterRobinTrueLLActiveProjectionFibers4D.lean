import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitPolarization4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveProjectionFibers4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The four inactive differences carried by `x - y`. -/
def inactiveDifferenceData
    (x y : FullMatterRobinLLDirections period hPeriod) :
    ActiveProjectionKernelData period hPeriod :=
  fullToKernelData period hPeriod (subDirection period hPeriod x y)

theorem activeProjection_eq_iff_subDirection_inactive
    (x y : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod x = activeProjection period hPeriod y ↔
      activeProjection period hPeriod (subDirection period hPeriod x y) =
        zeroActiveDirection period hPeriod := by
  rcases x with ⟨⟨xm, xMatter, xGauge, xGhost, xAuxiliary, xLL⟩,
    xRobin, xLLAux, xLLMeasure⟩
  rcases y with ⟨⟨ym, yMatter, yGauge, yGhost, yAuxiliary, yLL⟩,
    yRobin, yLLAux, yLLMeasure⟩
  simp [subDirection, addDirection, negDirection, activeProjection, zeroActiveDirection,
    add_neg_eq_zero]

theorem subDirection_inactive_iff_four_differences
    (x y : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod (subDirection period hPeriod x y) =
        zeroActiveDirection period hPeriod ↔
      subDirection period hPeriod x y =
        kernelDataToFull period hPeriod (inactiveDifferenceData period hPeriod x y) := by
  exact activeProjection_zero_iff_free_components period hPeriod
    (subDirection period hPeriod x y)

/-- Exact fibre characterization: equality of active readings means that the
difference is completely and uniquely specified by its metric, gauge, ghost,
and auxiliary differences. No gauge-group interpretation is asserted. -/
theorem activeProjection_fiber_iff_four_differences
    (x y : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod x = activeProjection period hPeriod y ↔
      subDirection period hPeriod x y =
        kernelDataToFull period hPeriod (inactiveDifferenceData period hPeriod x y) := by
  rw [activeProjection_eq_iff_subDirection_inactive,
    subDirection_inactive_iff_four_differences]

theorem activeProjection_eq_iff_activeQuotientClass_eq
    (x y : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod x = activeProjection period hPeriod y ↔
      (⟦x⟧ : ActiveQuotient period hPeriod) = ⟦y⟧ := by
  constructor
  · intro h
    apply (activeQuotientEquiv period hPeriod).injective
    simpa using h
  · intro h
    have := congrArg (activeQuotientEquiv period hPeriod) h
    simpa using this

theorem activeQuotientClass_eq_iff_subDirection_four_differences
    (x y : FullMatterRobinLLDirections period hPeriod) :
    (⟦x⟧ : ActiveQuotient period hPeriod) = ⟦y⟧ ↔
      subDirection period hPeriod x y =
        kernelDataToFull period hPeriod (inactiveDifferenceData period hPeriod x y) := by
  rw [← activeProjection_eq_iff_activeQuotientClass_eq,
    activeProjection_fiber_iff_four_differences]

end
end P0EFTJanusFullMatterRobinTrueLLActiveProjectionFibers4D
end JanusFormal
