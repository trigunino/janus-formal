import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH02PTOnsagerCasimir

namespace JanusFormal
namespace P0EFTJanusTH03EntropyPositivity

set_option autoImplicit false

/-- Entropy production from the symmetric part of a two-channel transport
matrix. -/
def quadraticEntropyProduction
    (l11 symmetricCross l22 x y : ℝ) : ℝ :=
  l11 * x ^ 2 + 2 * symmetricCross * x * y + l22 * y ^ 2

theorem positive_semidefinite_transport_gives_nonnegative_entropy
    (l11 symmetricCross l22 x y : ℝ)
    (h11 : 0 < l11)
    (hDet : symmetricCross ^ 2 ≤ l11 * l22) :
    0 ≤ quadraticEntropyProduction l11 symmetricCross l22 x y := by
  have hSquare : 0 ≤ (l11 * x + symmetricCross * y) ^ 2 := sq_nonneg _
  have hY : 0 ≤ (l11 * l22 - symmetricCross ^ 2) * y ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hDet) (sq_nonneg y)
  have hScaled :
      0 ≤ l11 * quadraticEntropyProduction l11 symmetricCross l22 x y := by
    unfold quadraticEntropyProduction
    nlinarith
  apply nonneg_of_mul_nonneg_left _ h11
  simpa [mul_comm] using hScaled

theorem negative_diagonal_transport_violates_second_law
    (l11 : ℝ) (hNegative : l11 < 0) :
    quadraticEntropyProduction l11 0 0 1 0 < 0 := by
  simpa [quadraticEntropyProduction] using hNegative

structure TH03Status where
  symmetricTransportPartDerived : Prop
  positiveSemidefiniteConeChecked : Prop
  antisymmetricPartEntropyNeutral : Prop
  transportCoefficientsDerivedFromP : Prop
  sigmaStateLawDerivedFromP : Prop

def conditionalTH03Closed (s : TH03Status) : Prop :=
  s.symmetricTransportPartDerived ∧
  s.positiveSemidefiniteConeChecked ∧
  s.antisymmetricPartEntropyNeutral

def physicalTH03Closed (s : TH03Status) : Prop :=
  conditionalTH03Closed s ∧
  s.transportCoefficientsDerivedFromP ∧
  s.sigmaStateLawDerivedFromP

end P0EFTJanusTH03EntropyPositivity
end JanusFormal
