import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveCharacterization4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod

/-- The zero class here means exactly the class corresponding, under the
active quotient equivalence, to the zero active reading. -/
def zeroActiveQuotientClass : ActiveQuotient period hPeriod :=
  (activeQuotientEquiv period hPeriod).symm (zeroActiveDirection period hPeriod)

theorem activeProjection_zero_iff_class_zero
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod direction = zeroActiveDirection period hPeriod ↔
      (⟦direction⟧ : ActiveQuotient period hPeriod) = zeroActiveQuotientClass period hPeriod := by
  constructor
  · intro h
    apply (activeQuotientEquiv period hPeriod).injective
    simpa [zeroActiveQuotientClass] using h
  · intro h
    have := congrArg (activeQuotientEquiv period hPeriod) h
    simpa [zeroActiveQuotientClass] using this

theorem activeProjection_zero_iff_enrichedD9_reading_zero
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod direction = zeroActiveDirection period hPeriod ↔
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) =
          zeroActiveDirection period hPeriod := by
  simp only [toActiveDirection_projection]

/-- Exact three-way characterization of action-inactivity. It makes no claim
that the resulting class is a global gauge orbit. -/
theorem inactive_projection_class_enrichedD9_characterization
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (activeProjection period hPeriod direction = zeroActiveDirection period hPeriod ↔
      (⟦direction⟧ : ActiveQuotient period hPeriod) = zeroActiveQuotientClass period hPeriod) ∧
    ((⟦direction⟧ : ActiveQuotient period hPeriod) = zeroActiveQuotientClass period hPeriod ↔
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) =
          zeroActiveDirection period hPeriod) := by
  refine ⟨activeProjection_zero_iff_class_zero period hPeriod direction, ?_⟩
  rw [← activeProjection_zero_iff_class_zero period hPeriod direction]
  exact activeProjection_zero_iff_enrichedD9_reading_zero period hPeriod fields sector column
    point direction

end
end P0EFTJanusFullMatterRobinTrueLLInactiveCharacterization4D
end JanusFormal
