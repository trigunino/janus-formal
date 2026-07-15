import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteJetCompatibilityNaturality

/-!
# Principal symbol of the finite Gram compatibility linearization

For a covector `ξ` and ambient vector `V`, the rank-one one-jet
`H = ξ ⊗ V` is inserted into the actual Gram linearization `J_F`.  The
resulting pointwise symbol is

`σ_J(F, ξ)(V)(x,y) = ξ(x) ⟪V,Fy⟫ + ξ(y) ⟪Fx,V⟫`.

For nonzero `ξ`, its kernel consists exactly of ambient vectors orthogonal to
the range of `F`; in particular it is injective when `F` is surjective.  This
is a finite Euclidean first-symbol theorem.  It does not construct a global
PDE complex, a Lorentzian symbol, or symbol exactness for the Janus fields.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteJetCompatibilityPrincipalSymbol

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusFiniteGramInducedMetricFrechetBridge
open P0EFTJanusFiniteJetCompatibilityNaturality

universe u v

variable {Tangent : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- Rank-one one-jet `x ↦ ξ(x) • V`. -/
def rankOneJet
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) :=
  covector.smulRight variation

@[simp]
theorem rankOneJet_apply
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient) (x : Tangent) :
    rankOneJet covector variation x = covector x • variation := by
  rfl

/-- Principal-symbol map obtained by restricting `J_F` to rank-one jets. -/
def finiteJetCompatibilityPrincipalSymbol
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (covector : Tangent →L[ℝ] ℝ) :
    Ambient →L[ℝ] GramMetricTensor (Tangent := Tangent) :=
  (finiteJetCompatibilityLinearization F).comp
    ((ContinuousLinearMap.smulRightL ℝ Tangent Ambient) covector)

@[simp]
theorem finiteJetCompatibilityPrincipalSymbol_apply
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient) (x y : Tangent) :
    finiteJetCompatibilityPrincipalSymbol F covector variation x y =
      covector x * ⟪variation, F y⟫_ℝ +
        covector y * ⟪F x, variation⟫_ℝ := by
  simp [finiteJetCompatibilityPrincipalSymbol,
    finiteJetCompatibilityLinearization_apply,
    real_inner_smul_left, real_inner_smul_right]

/-- A nonzero continuous covector is nonzero on some vector. -/
theorem exists_apply_ne_zero_of_ne_zero
    (covector : Tangent →L[ℝ] ℝ) (hCovector : covector ≠ 0) :
    ∃ x : Tangent, covector x ≠ 0 := by
  by_contra h
  push Not at h
  apply hCovector
  ext x
  simpa using h x

/-- For nonzero frequency, the symbol kernel is exactly the orthogonal
complement of the range of the immersion one-jet. -/
theorem principalSymbol_eq_zero_iff_range_orthogonal
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient)
    (hCovector : covector ≠ 0) :
    finiteJetCompatibilityPrincipalSymbol F covector variation = 0 ↔
      ∀ y : Tangent, ⟪variation, F y⟫_ℝ = 0 := by
  constructor
  · intro hSymbol
    obtain ⟨x, hx⟩ := exists_apply_ne_zero_of_ne_zero covector hCovector
    have hDiagonal := congrArg (fun tensor => tensor x x) hSymbol
    simp only [finiteJetCompatibilityPrincipalSymbol_apply, zero_apply] at hDiagonal
    rw [real_inner_comm variation (F x)] at hDiagonal
    have hTwice : covector x * (2 * ⟪variation, F x⟫_ℝ) = 0 := by
      calc
        covector x * (2 * ⟪variation, F x⟫_ℝ) =
            covector x * ⟪variation, F x⟫_ℝ +
              covector x * ⟪variation, F x⟫_ℝ := by ring
        _ = 0 := hDiagonal
    have hInnerX : ⟪variation, F x⟫_ℝ = 0 := by
      have hTwoInner : 2 * ⟪variation, F x⟫_ℝ = 0 :=
        (mul_eq_zero.mp hTwice).resolve_left hx
      linarith
    intro y
    have hMixed := congrArg (fun tensor => tensor x y) hSymbol
    simp only [finiteJetCompatibilityPrincipalSymbol_apply, zero_apply] at hMixed
    rw [real_inner_comm variation (F x), hInnerX, mul_zero, add_zero] at hMixed
    exact (mul_eq_zero.mp hMixed).resolve_left hx
  · intro hOrthogonal
    ext x y
    simp only [finiteJetCompatibilityPrincipalSymbol_apply, zero_apply]
    rw [hOrthogonal y, real_inner_comm variation (F x), hOrthogonal x]
    ring

/-- If the one-jet is onto the ambient model, the nonzero-frequency symbol is
injective. -/
theorem principalSymbol_injective_of_surjective
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (hSurjective : Function.Surjective F)
    (covector : Tangent →L[ℝ] ℝ) (hCovector : covector ≠ 0) :
    Function.Injective (finiteJetCompatibilityPrincipalSymbol F covector) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  have hKernel :
      finiteJetCompatibilityPrincipalSymbol F covector (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hOrthogonal :=
    (principalSymbol_eq_zero_iff_range_orthogonal F covector
      (first - second) hCovector).mp hKernel
  obtain ⟨preimage, hPreimage⟩ := hSurjective (first - second)
  have hSelf := hOrthogonal preimage
  rw [hPreimage] at hSelf
  exact inner_self_eq_zero.mp hSelf

end

end P0EFTJanusFiniteJetCompatibilityPrincipalSymbol
end JanusFormal
