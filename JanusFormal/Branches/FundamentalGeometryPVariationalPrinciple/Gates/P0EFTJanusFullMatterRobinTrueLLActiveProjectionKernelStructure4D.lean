import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The four components ignored by `activeProjection`. This is merely the
set-theoretic kernel data, not a global gauge group. -/
structure ActiveProjectionKernelData where
  metric : SmoothDiagonalMetricVariation period hPeriod
  gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber
  ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber

def kernelDataToFull (data : ActiveProjectionKernelData period hPeriod) :
    FullMatterRobinLLDirections period hPeriod :=
  fourInactiveDirection period hPeriod data.metric data.gauge data.ghost data.auxiliary

theorem kernelDataToFull_activeProjection_zero
    (data : ActiveProjectionKernelData period hPeriod) :
    activeProjection period hPeriod (kernelDataToFull period hPeriod data) =
      zeroActiveDirection period hPeriod := by
  rfl

def fullToKernelData (direction : FullMatterRobinLLDirections period hPeriod) :
    ActiveProjectionKernelData period hPeriod where
  metric := direction.common.metric
  gauge := direction.common.gauge
  ghost := direction.common.ghost
  auxiliary := direction.common.auxiliary

theorem inactive_full_eq_kernelDataToFull
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    direction = kernelDataToFull period hPeriod (fullToKernelData period hPeriod direction) := by
  have hMatter := congrArg ActiveDirection.matter hInactive
  have hRobin := congrArg ActiveDirection.robin hInactive
  have hLL := congrArg ActiveDirection.llField hInactive
  have hLLAux := congrArg ActiveDirection.llAuxMetric hInactive
  have hLLMeasure := congrArg ActiveDirection.llMeasure hInactive
  change direction.common.matter = 0 at hMatter
  change direction.robin = 0 at hRobin
  change direction.common.ll = 0 at hLL
  change direction.llAuxMetric = 0 at hLLAux
  change direction.llMeasure = 0 at hLLMeasure
  rcases direction with ⟨⟨metric, matter, gauge, ghost, auxiliary, ll⟩,
    robin, llAuxMetric, llMeasure⟩
  dsimp only at hMatter hRobin hLL hLLAux hLLMeasure
  subst matter
  subst robin
  subst ll
  subst llAuxMetric
  subst llMeasure
  rfl

theorem activeProjection_zero_iff_free_components
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod direction = zeroActiveDirection period hPeriod ↔
      direction = kernelDataToFull period hPeriod (fullToKernelData period hPeriod direction) := by
  constructor
  · exact inactive_full_eq_kernelDataToFull period hPeriod direction
  · intro h
    rw [h]
    exact kernelDataToFull_activeProjection_zero period hPeriod _

/-- Exact set equivalence between the kernel subtype and the product of the
four free common-sector components. No gauge interpretation is asserted. -/
def activeProjectionKernelEquiv :
    { direction : FullMatterRobinLLDirections period hPeriod //
      activeProjection period hPeriod direction = zeroActiveDirection period hPeriod } ≃
      ActiveProjectionKernelData period hPeriod where
  toFun direction := fullToKernelData period hPeriod direction.1
  invFun data := ⟨kernelDataToFull period hPeriod data,
    kernelDataToFull_activeProjection_zero period hPeriod data⟩
  left_inv direction := by
    apply Subtype.ext
    exact (inactive_full_eq_kernelDataToFull period hPeriod direction.1 direction.2).symm
  right_inv data := by
    cases data
    rfl

end
end P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D
end JanusFormal
