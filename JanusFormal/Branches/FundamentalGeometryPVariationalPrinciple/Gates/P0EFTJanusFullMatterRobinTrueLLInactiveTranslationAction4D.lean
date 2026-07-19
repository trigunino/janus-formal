import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveProjectionFibers4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D
open P0EFTJanusFullMatterRobinTrueLLActiveProjectionFibers4D
open P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D

variable (period : Real) (hPeriod : period ≠ 0)

def zeroKernelData : ActiveProjectionKernelData period hPeriod where
  metric := { plusLogDirection := 0, minusLogDirection := 0 }
  gauge := 0
  ghost := 0
  auxiliary := 0

def addKernelData (first second : ActiveProjectionKernelData period hPeriod) :
    ActiveProjectionKernelData period hPeriod where
  metric :=
    { plusLogDirection := first.metric.plusLogDirection + second.metric.plusLogDirection
      minusLogDirection := first.metric.minusLogDirection + second.metric.minusLogDirection }
  gauge := first.gauge + second.gauge
  ghost := first.ghost + second.ghost
  auxiliary := first.auxiliary + second.auxiliary

/-- Additive action of the four inactive translations on full directions.
This is not named or interpreted as a gauge-group action. -/
def inactiveTranslate (data : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod direction (kernelDataToFull period hPeriod data)

theorem inactiveTranslate_zero (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslate period hPeriod (zeroKernelData period hPeriod) direction = direction := by
  rcases direction with ⟨⟨metric, matter, gauge, ghost, auxiliary, ll⟩,
    robin, llAuxMetric, llMeasure⟩
  rcases metric with ⟨plus, minus⟩
  simp [inactiveTranslate, zeroKernelData, kernelDataToFull, fourInactiveDirection, addDirection]

theorem inactiveTranslate_add (first second : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslate period hPeriod (addKernelData period hPeriod first second) direction =
      inactiveTranslate period hPeriod second
        (inactiveTranslate period hPeriod first direction) := by
  rcases direction with ⟨⟨metric, matter, gauge, ghost, auxiliary, ll⟩,
    robin, llAuxMetric, llMeasure⟩
  rcases metric with ⟨plus, minus⟩
  rcases first with ⟨⟨firstPlus, firstMinus⟩, firstGauge, firstGhost, firstAuxiliary⟩
  rcases second with ⟨⟨secondPlus, secondMinus⟩, secondGauge, secondGhost, secondAuxiliary⟩
  simp [inactiveTranslate, addKernelData, kernelDataToFull, fourInactiveDirection, addDirection,
    add_assoc]

theorem inactiveTranslate_activeProjection
    (data : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod (inactiveTranslate period hPeriod data direction) =
      activeProjection period hPeriod direction := by
  rcases data with ⟨metric, gauge, ghost, auxiliary⟩
  exact addFourInactive_activeProjection period hPeriod direction metric gauge ghost auxiliary

def SameInactiveTranslationOrbit
    (first second : FullMatterRobinLLDirections period hPeriod) : Prop :=
  ∃ data : ActiveProjectionKernelData period hPeriod,
    inactiveTranslate period hPeriod data first = second

private theorem add_subDirection_cancel_right
    (first second : FullMatterRobinLLDirections period hPeriod) :
    addDirection period hPeriod second (subDirection period hPeriod first second) = first := by
  rcases first with ⟨⟨fm, fMatter, fGauge, fGhost, fAuxiliary, fLL⟩,
    fRobin, fLLAux, fLLMeasure⟩
  rcases second with ⟨⟨sm, sMatter, sGauge, sGhost, sAuxiliary, sLL⟩,
    sRobin, sLLAux, sLLMeasure⟩
  rcases fm with ⟨fp, fn⟩
  rcases sm with ⟨sp, sn⟩
  simp [subDirection, addDirection, negDirection]

/-- Orbits of inactive translations are exactly fibres of `activeProjection`. -/
theorem sameInactiveTranslationOrbit_iff_activeProjection_eq
    (first second : FullMatterRobinLLDirections period hPeriod) :
    SameInactiveTranslationOrbit period hPeriod first second ↔
      activeProjection period hPeriod first = activeProjection period hPeriod second := by
  constructor
  · rintro ⟨data, rfl⟩
    exact (inactiveTranslate_activeProjection period hPeriod data first).symm
  · intro hActive
    let data := inactiveDifferenceData period hPeriod second first
    refine ⟨data, ?_⟩
    have hDifference := (activeProjection_fiber_iff_four_differences period hPeriod
      second first).mp hActive.symm
    change addDirection period hPeriod first (kernelDataToFull period hPeriod data) = second
    rw [← hDifference]
    exact add_subDirection_cancel_right period hPeriod second first

/-- Equivalently, inactive-translation orbits are precisely equal classes in
the active quotient. This remains a translation quotient, not a gauge group. -/
theorem sameInactiveTranslationOrbit_iff_activeQuotientClass_eq
    (first second : FullMatterRobinLLDirections period hPeriod) :
    SameInactiveTranslationOrbit period hPeriod first second ↔
      (⟦first⟧ : ActiveQuotient period hPeriod) = ⟦second⟧ := by
  rw [sameInactiveTranslationOrbit_iff_activeProjection_eq,
    activeProjection_eq_iff_activeQuotientClass_eq]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D
end JanusFormal
