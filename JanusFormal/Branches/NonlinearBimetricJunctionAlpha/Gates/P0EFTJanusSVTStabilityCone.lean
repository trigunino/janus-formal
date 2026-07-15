import Mathlib

namespace JanusFormal
namespace P0EFTJanusSVTStabilityCone

set_option autoImplicit false

def vectorAlpha (v planckSquared aetherScale : ℝ) : ℝ :=
  v * (planckSquared - aetherScale)

def vectorBeta (v planckSquared : ℝ) : ℝ :=
  v * planckSquared

def scalarAlpha
    (v planckSquared aetherScale lambdaPhi : ℝ) : ℝ :=
  v * (planckSquared - aetherScale + 2 * lambdaPhi * v)

def scalarBeta
    (v planckSquared membraneTension hrMassSquared : ℝ) : ℝ :=
  v * (planckSquared + membraneTension +
    hrMassSquared * planckSquared * (3 * v ^ 2 + 3 * v + 1))

def scalarMassSquared (v lambdaPhi hrMassSquared : ℝ) : ℝ :=
  2 * lambdaPhi * v ^ 2 + hrMassSquared

/-- A simple sufficient cone for the vector no-ghost/no-gradient conditions. -/
theorem vector_stability_cone
    (v planckSquared aetherScale hrMassSquared : ℝ)
    (hV : 0 < v)
    (hPlanck : 0 < planckSquared)
    (hAether : aetherScale < planckSquared)
    (hMass : 0 ≤ hrMassSquared) :
    0 < vectorAlpha v planckSquared aetherScale ∧
      0 < vectorBeta v planckSquared ∧
      0 ≤ hrMassSquared := by
  constructor
  · exact mul_pos hV (sub_pos.mpr hAether)
  constructor
  · exact mul_pos hV hPlanck
  · exact hMass

/-- The scalar coefficient polynomial is positive for positive background ratio. -/
theorem scalar_hr_shape_positive (v : ℝ) (hV : 0 < v) :
    0 < 3 * v ^ 2 + 3 * v + 1 := by
  nlinarith [sq_nonneg v]

/-- Sufficient cone for scalar no-ghost, no-gradient and no-tachyon signs. -/
theorem scalar_stability_cone
    (v planckSquared aetherScale lambdaPhi membraneTension hrMassSquared : ℝ)
    (hV : 0 < v)
    (hPlanck : 0 < planckSquared)
    (hAether : aetherScale < planckSquared)
    (hLambda : 0 ≤ lambdaPhi)
    (hTension : 0 ≤ membraneTension)
    (hMass : 0 ≤ hrMassSquared) :
    0 < scalarAlpha v planckSquared aetherScale lambdaPhi ∧
      0 < scalarBeta v planckSquared membraneTension hrMassSquared ∧
      0 ≤ scalarMassSquared v lambdaPhi hrMassSquared := by
  have hCore : 0 < planckSquared - aetherScale := sub_pos.mpr hAether
  have hLambdaTerm : 0 ≤ 2 * lambdaPhi * v := by positivity
  have hShape := scalar_hr_shape_positive v hV
  have hHR :
      0 ≤ hrMassSquared * planckSquared * (3 * v ^ 2 + 3 * v + 1) := by
    positivity
  constructor
  · unfold scalarAlpha
    exact mul_pos hV (add_pos_of_pos_of_nonneg hCore hLambdaTerm)
  constructor
  · unfold scalarBeta
    apply mul_pos hV
    positivity
  · unfold scalarMassSquared
    positivity

end P0EFTJanusSVTStabilityCone
end JanusFormal
