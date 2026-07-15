import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH01BalanceLaws

namespace JanusFormal
namespace P0EFTJanusTH02PTOnsagerCasimir

set_option autoImplicit false

/-- Two-channel Onsager-Casimir condition with PT parities `eps=±1`. -/
def onsagerCasimirCondition
    (epsilonFirst epsilonSecond l12 l21 : ℝ) : Prop :=
  l12 = epsilonFirst * epsilonSecond * l21

theorem equal_parity_gives_reciprocal_cross_coefficient
    (l12 l21 : ℝ)
    (h : onsagerCasimirCondition 1 1 l12 l21) :
    l12 = l21 := by
  simpa [onsagerCasimirCondition] using h

theorem opposite_parity_gives_antisymmetric_cross_coefficient
    (l12 l21 : ℝ)
    (h : onsagerCasimirCondition 1 (-1) l12 l21) :
    l12 = -l21 := by
  simpa [onsagerCasimirCondition] using h

/-- Antisymmetric transport does not contribute to quadratic entropy
production. -/
theorem antisymmetric_cross_terms_cancel
    (a x y : ℝ) :
    x * (a * y) + y * (-a * x) = 0 := by
  ring

structure TH02Inputs where
  forceParitiesDerived : Prop
  fluxParitiesDerived : Prop
  microscopicPTInvarianceDerived : Prop
  equilibriumStateSpecified : Prop

def physicalOnsagerCasimirReady (s : TH02Inputs) : Prop :=
  s.forceParitiesDerived ∧
  s.fluxParitiesDerived ∧
  s.microscopicPTInvarianceDerived ∧
  s.equilibriumStateSpecified

end P0EFTJanusTH02PTOnsagerCasimir
end JanusFormal
