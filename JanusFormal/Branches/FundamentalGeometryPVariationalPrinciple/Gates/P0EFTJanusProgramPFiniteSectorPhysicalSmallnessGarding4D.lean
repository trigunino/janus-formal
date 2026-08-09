import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

/-!
# Full Gårding after a small physical quadratic perturbation

Once the principal finite-sector form has an explicit positive margin, the
retained physical Hessian is treated as one bounded quadratic perturbation.  A
strictly smaller physical constant gives coercivity of the total Hessian with
margin

`principal.margin - physicalConstant`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Principal finite-sector Gårding plus one bounded physical perturbation. -/
structure FiniteSectorPhysicalSmallnessGardingData where
  principal : FiniteSectorQuadraticGardingData
    (Sector := Sector) (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalEnergy vector + physicalEnergy vector

namespace FiniteSectorPhysicalSmallnessGardingData

/-- Explicit coercive margin of the total Hessian. -/
def margin
    (data : FiniteSectorPhysicalSmallnessGardingData
      (Sector := Sector) (E := E)) : Real :=
  data.principal.margin - data.physicalConstant

/-- Positivity of the total margin. -/
theorem margin_pos
    (data : FiniteSectorPhysicalSmallnessGardingData
      (Sector := Sector) (E := E)) :
    0 < data.margin :=
  sub_pos.mpr data.physical_small

/-- The physical perturbation cannot close the principal sector gap. -/
theorem margin_norm_sq_le_totalEnergy
    (data : FiniteSectorPhysicalSmallnessGardingData
      (Sector := Sector) (E := E))
    (vector : E) :
    data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  have hPrincipal :=
    data.principal.margin_norm_sq_le_principalEnergy vector
  have hPhysical :
      -(data.physicalConstant * ‖vector‖ ^ 2) ≤
        data.physicalEnergy vector :=
    (abs_le.mp (data.physical_bound vector)).1
  rw [data.total_eq vector]
  unfold margin
  nlinarith

/-- Public full-Hessian Gårding checkpoint. -/
theorem finite_sector_physical_smallness_garding_gate
    (data : FiniteSectorPhysicalSmallnessGardingData
      (Sector := Sector) (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector :=
  ⟨data.margin_pos, data.margin_norm_sq_le_totalEnergy⟩

end FiniteSectorPhysicalSmallnessGardingData

end
end P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
end JanusFormal
