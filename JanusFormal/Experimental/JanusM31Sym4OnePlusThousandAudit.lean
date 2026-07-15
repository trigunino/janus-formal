import Mathlib

namespace JanusFormal
namespace JanusM31Sym4OnePlusThousandAudit

set_option autoImplicit false

/-- Euclidean quadratic form on a concrete eleven-dimensional space. -/
def normSq11 (x : Fin 11 → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The radial quartic singled out by an invariant quadratic form. -/
def radialQuartic11 (x : Fin 11 → ℝ) : ℝ := normSq11 x ^ 2

/-- Any action preserving the quadratic form also preserves its radial quartic. -/
theorem radialQuartic11_invariant
    (g : (Fin 11 → ℝ) → (Fin 11 → ℝ))
    (hOrthogonal : ∀ x, normSq11 (g x) = normSq11 x)
    (x : Fin 11 → ℝ) :
    radialQuartic11 (g x) = radialQuartic11 x := by
  simp [radialQuartic11, hOrthogonal]

/-- Number of degree-four symmetric monomials in eleven variables. -/
theorem sym4_dimension_11 : Nat.choose 14 4 = 1001 := by native_decide

/-- Number removed by one trace from degree four. -/
theorem sym2_dimension_11 : Nat.choose 12 2 = 66 := by native_decide

/-- Orthogonal harmonic decomposition dimensions:
`Sym⁴ = H⁴ ⊕ q H² ⊕ ⟨q²⟩`, hence `935 + 65 + 1 = 1001`. -/
theorem orthogonal_one_plus_thousand_dimension_audit :
    (1001 - 66) + (66 - 1) + 1 = 1001 := by norm_num

/-- Minimal model of the translation term in the M31 coadjoint action. -/
def coadjointShear (d : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1 + d * state.2, state.2)

def naiveNormSq (state : ℝ × ℝ) : ℝ := state.1 ^ 2 + state.2 ^ 2

/-- A translation shear does not preserve the naive Euclidean quadratic form. -/
theorem coadjoint_translation_breaks_naive_orthogonality :
    naiveNormSq (coadjointShear 1 (0, 1)) ≠ naiveNormSq (0, 1) := by
  norm_num [naiveNormSq, coadjointShear]

end JanusM31Sym4OnePlusThousandAudit
end JanusFormal
