import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace JanusFormal.P0EFTJanusProgramPT12OrthogonalColumnPairing4D
set_option autoImplicit false
noncomputable section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [NormedAddCommGroup K] [InnerProductSpace Real K]

theorem orthogonalColumn_pairing (A : H →L[Real] H) (B : K →L[Real] K)
    (I : K →ₗᵢ[Real] H)
    (hSym : ∀ x y, inner Real (A x) y = inner Real x (A y))
    (hColumn : ∀ z, A (I z) = I (B z)) (u t : H) (v w : K)
    (hu : ∀ z, inner Real (I z) u = 0) (ht : ∀ z, inner Real (I z) t = 0) :
    inner Real (A (u + I v)) (t + I w) = inner Real (A u) t + inner Real (B v) w := by
  have hCross : inner Real (A u) (I w) = 0 := by
    rw [hSym, hColumn, ← real_inner_comm u, hu]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    hColumn, ht, I.inner_map_map, hCross]
  simp

end
end JanusFormal.P0EFTJanusProgramPT12OrthogonalColumnPairing4D
