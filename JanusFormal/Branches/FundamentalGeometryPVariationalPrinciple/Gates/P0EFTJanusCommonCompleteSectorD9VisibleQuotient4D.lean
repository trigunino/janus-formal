import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D

/-!
# Quotient by the currently supplied D9 visible projection

This is only the set quotient of the six-sector common direction packet by
equality of the four D9 blocks at one fixed sector, column and throat point.
It is not a gauge quotient, a Sobolev quotient, or the global Program-P field
quotient.
-/

namespace JanusFormal
namespace P0EFTJanusCommonCompleteSectorD9VisibleQuotient4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Two common directions are related precisely when the currently supplied
four-block D9 observation cannot distinguish them. -/
def combinedVisibleD9Setoid
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    Setoid (CommonSectorDirections period hPeriod) where
  r first second :=
    combinedVisibleD9Projection period hPeriod fields first sector column point =
      combinedVisibleD9Projection period hPeriod fields second sector column point
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Set quotient by equality of the fixed current D9 observation. -/
abbrev CombinedVisibleD9Quotient
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :=
  Quotient (combinedVisibleD9Setoid period hPeriod fields sector column point)

/-- The visible projection descends to the observational quotient. -/
def descendedCombinedVisibleD9Projection
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    CombinedVisibleD9Quotient period hPeriod fields sector column point →
      VisibleD9Projection :=
  Quotient.lift
    (combinedVisibleD9Projection period hPeriod fields · sector column point)
    (fun _ _ hEqual => hEqual)

@[simp]
theorem descendedCombinedVisibleD9Projection_mk
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    descendedCombinedVisibleD9Projection period hPeriod fields sector column point
        (Quotient.mk _ direction) =
      combinedVisibleD9Projection period hPeriod fields direction
        sector column point :=
  rfl

/-- No further information is lost after quotienting: the descended current
D9 projection is injective. -/
theorem descendedCombinedVisibleD9Projection_injective
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    Function.Injective
      (descendedCombinedVisibleD9Projection period hPeriod fields
        sector column point) := by
  intro first second hEqual
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply Quotient.sound
      exact hEqual

/-- At fixed visible data, every choice of auxiliary and LL direction gives
the same class in the current D9 observational quotient. -/
theorem auxiliary_ll_modifications_same_quotient_class
    (fields : IndependentFields period hPeriod)
    (visible : CommonSectorDirections period hPeriod)
    (firstAux secondAux :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber)
    (firstLL secondLL : SmoothThroatField period hPeriod LLFieldFiber)
    (sector : Sector) (column : Fin 2)
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    (Quotient.mk _ { visible with auxiliary := firstAux, ll := firstLL } :
        CombinedVisibleD9Quotient period hPeriod fields sector column point) =
      Quotient.mk _ { visible with auxiliary := secondAux, ll := secondLL } := by
  apply Quotient.sound
  exact combinedVisibleD9Projection_auxiliary_ll_kernel period hPeriod fields
    visible firstAux secondAux firstLL secondLL sector column point

end

end P0EFTJanusCommonCompleteSectorD9VisibleQuotient4D
end JanusFormal
