import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D

/-!
# Active projection and its exact inactive fibre

For the assembled matter + Robin + LL action, the active direction consists
exactly of the matter pair, Robin field and LL field.  This gate computes the
zero fibre and every general fibre of that projection.  Metric, gauge, ghost
and auxiliary directions remain arbitrary in those fibres; no statement about
a complete Candidate-A action is made.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActiveProjectionKernel4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)

/-- Matter, Robin and LL directions seen by the assembled action. -/
abbrev ActiveMatterRobinLLDirection :=
  (SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber) ×
  (SmoothThroatField period hPeriod Real ×
    SmoothThroatField period hPeriod LLFieldFiber)

/-- Forget precisely the sectors absent from the matter + Robin + LL action. -/
def activeMatterRobinLLProjection
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    ActiveMatterRobinLLDirection period hPeriod :=
  (direction.common.matter, direction.robin, direction.common.ll)

/-- The inactive directions are the genuine zero fibre of the active
projection. -/
def inactiveMatterRobinLLDirections :
    Set (MatterRobinLLEnrichedDirections period hPeriod) :=
  activeMatterRobinLLProjection period hPeriod ⁻¹' {0}

/-- Exact componentwise characterization of the inactive fibre. -/
theorem mem_inactiveMatterRobinLLDirections_iff
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    direction ∈ inactiveMatterRobinLLDirections period hPeriod ↔
      direction.common.matter = 0 ∧ direction.robin = 0 ∧
        direction.common.ll = 0 := by
  change (direction.common.matter, (direction.robin, direction.common.ll)) = 0 ↔ _
  constructor
  · intro hEqual
    have hMatter := congrArg Prod.fst hEqual
    have hPair := congrArg Prod.snd hEqual
    exact ⟨hMatter, congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · rintro ⟨hMatter, hRobin, hLL⟩
    rw [hMatter, hRobin, hLL]
    rfl

/-- Explicit constructor for every inactive direction; the four sectors not
used by this action remain arbitrary. -/
def inactiveMatterRobinLLDirection
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    MatterRobinLLEnrichedDirections period hPeriod :=
  { common :=
      { metric := metric
        matter := 0
        gauge := gauge
        ghost := ghost
        auxiliary := auxiliary
        ll := 0 }
    robin := 0 }

@[simp] theorem inactiveMatterRobinLLDirection_mem
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    inactiveMatterRobinLLDirection period hPeriod metric gauge ghost auxiliary ∈
      inactiveMatterRobinLLDirections period hPeriod := by
  simp [mem_inactiveMatterRobinLLDirections_iff,
    inactiveMatterRobinLLDirection]

/-- Every element of the zero fibre is uniquely represented by its four
inactive sector values through the explicit constructor. -/
theorem mem_inactive_iff_exists_inactive_sectors
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    direction ∈ inactiveMatterRobinLLDirections period hPeriod ↔
      ∃ metric gauge ghost auxiliary,
        direction = inactiveMatterRobinLLDirection period hPeriod
          metric gauge ghost auxiliary := by
  constructor
  · intro hInactive
    rw [mem_inactiveMatterRobinLLDirections_iff] at hInactive
    rcases hInactive with ⟨hMatter, hRobin, hLL⟩
    refine ⟨direction.common.metric, direction.common.gauge,
      direction.common.ghost, direction.common.auxiliary, ?_⟩
    cases direction with
    | mk common robin =>
        cases common with
        | mk metric matter gauge ghost auxiliary ll =>
            simp only at hMatter hRobin hLL
            subst matter
            subst robin
            subst ll
            rfl
  · rintro ⟨metric, gauge, ghost, auxiliary, rfl⟩
    exact inactiveMatterRobinLLDirection_mem period hPeriod
      metric gauge ghost auxiliary

/-- Two enriched directions have the same active projection exactly when all
three visible sector directions agree. -/
theorem activeMatterRobinLLProjection_eq_iff
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    activeMatterRobinLLProjection period hPeriod first =
        activeMatterRobinLLProjection period hPeriod second ↔
      first.common.matter = second.common.matter ∧
        first.robin = second.robin ∧ first.common.ll = second.common.ll := by
  change
    (first.common.matter, (first.robin, first.common.ll)) =
        (second.common.matter, (second.robin, second.common.ll)) ↔ _
  constructor
  · intro hEqual
    have hMatter := congrArg Prod.fst hEqual
    have hPair := congrArg Prod.snd hEqual
    exact ⟨hMatter, congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · rintro ⟨hMatter, hRobin, hLL⟩
    rw [hMatter, hRobin, hLL]

/-- Every fibre is explicitly the set of directions whose three active
components equal the target; all other common sectors are unrestricted. -/
theorem mem_activeMatterRobinLLProjection_fiber_iff
    (target : ActiveMatterRobinLLDirection period hPeriod)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    direction ∈ activeMatterRobinLLProjection period hPeriod ⁻¹' {target} ↔
      direction.common.matter = target.1 ∧
        direction.robin = target.2.1 ∧ direction.common.ll = target.2.2 := by
  change
    (direction.common.matter, (direction.robin, direction.common.ll)) = target ↔ _
  constructor
  · intro hEqual
    have hMatter := congrArg Prod.fst hEqual
    have hPair := congrArg Prod.snd hEqual
    exact ⟨hMatter, congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · rintro ⟨hMatter, hRobin, hLL⟩
    rw [hMatter, hRobin, hLL]

end

end P0EFTJanusCommonMatterRobinLLActiveProjectionKernel4D
end JanusFormal
