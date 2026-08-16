import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteProjectionNormResolution4D

/-!
# Positive norm resolution from symmetric idempotent projections

A bounded projection is positive in the required sense once its bilinear
pairing is symmetric and it is idempotent.  For every sector,

`⟪P x, x⟫ = ⟪P x, P x⟫ = ‖P x‖²`.

Consequently a finite symmetric idempotent resolution of the identity supplies
the norm-square decomposition used by the projected-principal Gårding route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteProjectionNormResolution4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- A finite resolution of the identity by symmetric idempotent bounded maps. -/
structure FiniteSelfAdjointProjectionResolutionData where
  projection : Sector → E →L[Real] E
  sum_projection : ∀ vector,
    (∑ sector : Sector, projection sector vector) = vector
  projection_idempotent : ∀ sector vector,
    projection sector (projection sector vector) = projection sector vector
  projection_symmetric : ∀ sector first second,
    inner Real (projection sector first) second =
      inner Real first (projection sector second)

namespace FiniteSelfAdjointProjectionResolutionData

/-- Positivity identity of one symmetric idempotent projection. -/
theorem projection_inner_eq_norm_sq
    (data : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E))
    (sector : Sector) (vector : E) :
    inner Real (data.projection sector vector) vector =
      ‖data.projection sector vector‖ ^ 2 := by
  calc
    inner Real (data.projection sector vector) vector =
        inner Real vector (data.projection sector vector) :=
      data.projection_symmetric sector vector vector
    _ = inner Real (data.projection sector vector)
        (data.projection sector vector) := by
      have hSym := data.projection_symmetric sector vector
        (data.projection sector vector)
      rw [data.projection_idempotent sector vector] at hSym
      exact hSym.symm
    _ = ‖data.projection sector vector‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Forget symmetry/idempotence and retain the generated positive norm
resolution. -/
def toNormResolution
    (data : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) :
    FiniteProjectionNormResolutionData (Sector := Sector) (E := E) where
  projection := data.projection
  sum_projection := data.sum_projection
  projection_inner_eq_norm_sq := data.projection_inner_eq_norm_sq

/-- Pythagorean norm decomposition. -/
theorem norm_sq_decomposition
    (data : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E))
    (vector : E) :
    ‖vector‖ ^ 2 =
      ∑ sector : Sector, ‖data.projection sector vector‖ ^ 2 :=
  data.toNormResolution.norm_sq_decomposition vector

/-- Public self-adjoint projection-resolution checkpoint. -/
theorem finite_selfAdjoint_projection_resolution_gate
    (data : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) :
    ∀ vector : E,
      ‖vector‖ ^ 2 =
        ∑ sector : Sector, ‖data.projection sector vector‖ ^ 2 :=
  data.norm_sq_decomposition

end FiniteSelfAdjointProjectionResolutionData

end
end P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
end JanusFormal
