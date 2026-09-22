import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact signed Gram representatives of the two off-shell BRST forms.
These are bounded graph-space operators, not spectral or Fredholm claims. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12SignedBRSTGram4D

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

variable {H V : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]

def gram (P : H →L[Real] V) : H →L[Real] H := P.adjoint.comp P

theorem gram_pairing (P : H →L[Real] V) (x y : H) :
    inner Real (gram P x) y = inner Real (P x) (P y) := by
  exact P.adjoint_inner_left y (P x)

/-- The mixed symmetric block is a difference of two positive Gram blocks. -/
def signedCross (P Q : H →L[Real] V) : H →L[Real] H :=
  (1 / 2 : Real) • (gram (P + Q) - gram (P - Q))

theorem signedCross_pairing (P Q : H →L[Real] V) (x y : H) :
    inner Real (signedCross P Q x) y =
      inner Real (P x) (Q y) + inner Real (Q x) (P y) := by
  simp only [signedCross, smul_apply,
    sub_apply, real_inner_smul_left, inner_sub_left,
    gram_pairing, add_apply, inner_add_left,
    inner_add_right, inner_sub_right]
  ring

/-- Abelian coordinates are `L`, `B-L`, `cbar+FP c`, `cbar-FP c`.
The negative auxiliary square and the ghost minus square are retained. -/
def abelianSignedGram (L B C F : H →L[Real] V) : H →L[Real] H :=
  gram L - gram (B - L) + signedCross C F

theorem abelianSignedGram_pairing (L B C F : H →L[Real] V) (x y : H) :
    inner Real (abelianSignedGram L B C F x) y =
      inner Real (B x) (L y) + inner Real (L x) (B y) -
        inner Real (B x) (B y) +
        inner Real (C x) (F y) + inner Real (F x) (C y) := by
  simp only [abelianSignedGram, add_apply,
    sub_apply, inner_add_left, inner_sub_left,
    gram_pairing, signedCross_pairing, inner_sub_right]
  ring

/-- For diffeomorphisms the Lorentz-flat B coordinate is kept explicitly.
The ghost sign is the one in the actual covariant action. -/
def diffeomorphismSignedGram (D B Bflat F C : H →L[Real] V) : H →L[Real] H :=
  signedCross (D - (1 / 2 : Real) • Bflat) B - signedCross F C

theorem diffeomorphismSignedGram_pairing
    (D B Bflat F C : H →L[Real] V) (x y : H) :
    inner Real (diffeomorphismSignedGram D B Bflat F C x) y =
      inner Real (D x) (B y) + inner Real (B x) (D y) -
        (1 / 2 : Real) * inner Real (Bflat x) (B y) -
        (1 / 2 : Real) * inner Real (B x) (Bflat y) -
        inner Real (F x) (C y) - inner Real (C x) (F y) := by
  simp only [diffeomorphismSignedGram, sub_apply,
    inner_sub_left, signedCross_pairing, smul_apply,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- An actual realization can be pulled back along a bounded sector map. -/
def pullback {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace Real K] [CompleteSpace K]
    (P : H →L[Real] K) (A : K →L[Real] K) : H →L[Real] H :=
  P.adjoint.comp (A.comp P)

theorem pullback_pairing {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace Real K] [CompleteSpace K]
    (P : H →L[Real] K) (A : K →L[Real] K) (x y : H) :
    inner Real (pullback P A x) y = inner Real (A (P x)) (P y) := by
  exact P.adjoint_inner_left y (A (P x))

end
end P0EFTJanusProgramPT12SignedBRSTGram4D
end JanusFormal
