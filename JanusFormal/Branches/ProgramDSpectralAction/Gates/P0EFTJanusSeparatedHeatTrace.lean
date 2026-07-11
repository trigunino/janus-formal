import Mathlib

namespace JanusFormal
namespace P0EFTJanusSeparatedHeatTrace

set_option autoImplicit false

variable {SphereIndex CircleIndex : Type*}
variable [Fintype SphereIndex] [Fintype CircleIndex]

/-- One finite sphere heat-trace term. -/
noncomputable def sphereHeatTerm
    (multiplicity eigenvalue : SphereIndex → ℝ)
    (time : ℝ)
    (index : SphereIndex) : ℝ :=
  multiplicity index * Real.exp (-time * eigenvalue index)

/-- One finite circle heat-trace term. -/
noncomputable def circleHeatTerm
    (multiplicity eigenvalue : CircleIndex → ℝ)
    (time : ℝ)
    (index : CircleIndex) : ℝ :=
  multiplicity index * Real.exp (-time * eigenvalue index)

/-- Finite sphere heat trace. -/
noncomputable def finiteSphereHeatTrace
    (multiplicity eigenvalue : SphereIndex → ℝ)
    (time : ℝ) : ℝ :=
  ∑ index, sphereHeatTerm multiplicity eigenvalue time index

/-- Finite circle heat trace. -/
noncomputable def finiteCircleHeatTrace
    (multiplicity eigenvalue : CircleIndex → ℝ)
    (time : ℝ) : ℝ :=
  ∑ index, circleHeatTerm multiplicity eigenvalue time index

/-- Finite separated product heat trace. -/
noncomputable def finiteProductHeatTrace
    (sphereMultiplicity sphereEigenvalue : SphereIndex → ℝ)
    (circleMultiplicity circleEigenvalue : CircleIndex → ℝ)
    (time : ℝ) : ℝ :=
  ∑ sphereIndex, ∑ circleIndex,
    sphereHeatTerm sphereMultiplicity sphereEigenvalue time sphereIndex *
      circleHeatTerm circleMultiplicity circleEigenvalue time circleIndex

/-- A separated product eigenvalue gives the product of the two heat factors. -/
theorem separated_exponential_factorization
    (time sphereEigenvalue circleEigenvalue : ℝ) :
    Real.exp (-time * (sphereEigenvalue + circleEigenvalue)) =
      Real.exp (-time * sphereEigenvalue) *
        Real.exp (-time * circleEigenvalue) := by
  rw [show -time * (sphereEigenvalue + circleEigenvalue) =
      -time * sphereEigenvalue + -time * circleEigenvalue by ring]
  exact Real.exp_add _ _

/-- Exact factorization of every finite separated heat trace. -/
theorem finite_product_heat_trace_factorizes
    (sphereMultiplicity sphereEigenvalue : SphereIndex → ℝ)
    (circleMultiplicity circleEigenvalue : CircleIndex → ℝ)
    (time : ℝ) :
    finiteProductHeatTrace sphereMultiplicity sphereEigenvalue
        circleMultiplicity circleEigenvalue time =
      finiteSphereHeatTrace sphereMultiplicity sphereEigenvalue time *
        finiteCircleHeatTrace circleMultiplicity circleEigenvalue time := by
  unfold finiteProductHeatTrace finiteSphereHeatTrace finiteCircleHeatTrace
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro sphereIndex _
  rw [Finset.mul_sum]

/-- Every heat term is nonnegative for nonnegative multiplicity. -/
theorem sphere_heat_term_nonnegative
    (multiplicity eigenvalue : SphereIndex → ℝ)
    (time : ℝ)
    (index : SphereIndex)
    (hMultiplicity : 0 ≤ multiplicity index) :
    0 ≤ sphereHeatTerm multiplicity eigenvalue time index := by
  unfold sphereHeatTerm
  exact mul_nonneg hMultiplicity (le_of_lt (Real.exp_pos _))

/-- The finite sphere heat trace is nonnegative for nonnegative multiplicities. -/
theorem finite_sphere_heat_trace_nonnegative
    (multiplicity eigenvalue : SphereIndex → ℝ)
    (time : ℝ)
    (hMultiplicity : ∀ index, 0 ≤ multiplicity index) :
    0 ≤ finiteSphereHeatTrace multiplicity eigenvalue time := by
  unfold finiteSphereHeatTrace
  exact Finset.sum_nonneg fun index _ =>
    sphere_heat_term_nonnegative multiplicity eigenvalue time index
      (hMultiplicity index)

/-- Eigenvalue scaling by `scale^-2` is equivalent to heat-time scaling. -/
theorem heat_time_homothety
    (time eigenvalue scale : ℝ)
    (hScale : scale ≠ 0) :
    Real.exp (-time * (eigenvalue / scale ^ 2)) =
      Real.exp (-(time / scale ^ 2) * eigenvalue) := by
  congr 1
  field_simp [hScale]
  ring

/--
This module closes the universal finite-sum algebra. Passing to the actual
infinite spectrum requires summability, trace-class heat operators and a proof
that the product Dirac/Laplace operator has the separated spectrum used here.
-/
structure InfiniteHeatTraceClosureStatus where
  selfAdjointOperatorConstructed : Prop
  discreteSpectrumProved : Prop
  finiteMultiplicityProved : Prop
  heatOperatorTraceClass : Prop
  separatedSpectrumComplete : Prop
  infiniteTraceFactorizationProved : Prop


def infiniteHeatTraceClosure
    (s : InfiniteHeatTraceClosureStatus) : Prop :=
  s.selfAdjointOperatorConstructed /\
  s.discreteSpectrumProved /\
  s.finiteMultiplicityProved /\
  s.heatOperatorTraceClass /\
  s.separatedSpectrumComplete /\
  s.infiniteTraceFactorizationProved

end P0EFTJanusSeparatedHeatTrace
end JanusFormal
