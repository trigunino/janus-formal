import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteProductHeatTrace

set_option autoImplicit false

/-- Heat weight of one nonnegative eigenvalue. -/
noncomputable def heatWeight (heatTime eigenvalue : ℝ) : ℝ :=
  Real.exp (-heatTime * eigenvalue)

/-- Finite heat trace used as an algebraic approximation to a discrete spectrum. -/
noncomputable def finiteHeatTrace
    (spectrum : List ℝ) (heatTime : ℝ) : ℝ :=
  (spectrum.map (heatWeight heatTime)).sum

/-- Finite product spectrum: eigenvalues add on a product geometry. -/
def finiteProductSpectrum
    (first second : List ℝ) : List ℝ :=
  first.flatMap (fun firstEigenvalue =>
    second.map (fun secondEigenvalue =>
      firstEigenvalue + secondEigenvalue))

/-- Heat weights multiply when eigenvalues add. -/
theorem heat_weight_add
    (heatTime firstEigenvalue secondEigenvalue : ℝ) :
    heatWeight heatTime (firstEigenvalue + secondEigenvalue) =
      heatWeight heatTime firstEigenvalue *
        heatWeight heatTime secondEigenvalue := by
  unfold heatWeight
  rw [show
      -heatTime * (firstEigenvalue + secondEigenvalue) =
        -heatTime * firstEigenvalue +
          -heatTime * secondEigenvalue by ring,
    Real.exp_add]

/-- Shifting every eigenvalue multiplies the finite heat trace by one heat weight. -/
theorem finite_heat_trace_shift
    (base heatTime : ℝ)
    (spectrum : List ℝ) :
    finiteHeatTrace
        (spectrum.map (fun eigenvalue => base + eigenvalue)) heatTime =
      heatWeight heatTime base * finiteHeatTrace spectrum heatTime := by
  induction spectrum with
  | nil => simp [finiteHeatTrace]
  | cons eigenvalue rest ih =>
      simp [finiteHeatTrace, heat_weight_add, ih, mul_add]

/-- Finite product heat traces factorize exactly. -/
theorem finite_product_heat_trace_factorizes
    (first second : List ℝ)
    (heatTime : ℝ) :
    finiteHeatTrace (finiteProductSpectrum first second) heatTime =
      finiteHeatTrace first heatTime *
        finiteHeatTrace second heatTime := by
  induction first with
  | nil => simp [finiteProductSpectrum, finiteHeatTrace]
  | cons firstEigenvalue rest ih =>
      simp [finiteProductSpectrum, finiteHeatTrace,
        finite_heat_trace_shift, ih, add_mul]

/-- PT reflection of a finite real spectrum preserves the heat trace of its square. -/
def squareSpectrum (spectrum : List ℝ) : List ℝ :=
  spectrum.map (fun eigenvalue => eigenvalue ^ 2)

/-- Negating all eigenvalues leaves the squared spectrum unchanged. -/
theorem square_spectrum_negation
    (spectrum : List ℝ) :
    squareSpectrum
        (spectrum.map (fun eigenvalue => -eigenvalue)) =
      squareSpectrum spectrum := by
  induction spectrum with
  | nil => rfl
  | cons eigenvalue rest ih =>
      simp [squareSpectrum, ih]
      ring

/-- Hence the parity-even finite heat trace is PT invariant. -/
theorem pt_negation_preserves_squared_heat_trace
    (spectrum : List ℝ)
    (heatTime : ℝ) :
    finiteHeatTrace
        (squareSpectrum
          (spectrum.map (fun eigenvalue => -eigenvalue))) heatTime =
      finiteHeatTrace (squareSpectrum spectrum) heatTime := by
  rw [square_spectrum_negation]

/--
The finite theorem isolates the analytic tasks for the real operator: prove
spectral discreteness and completeness, justify the infinite product trace and
control convergence uniformly enough for Poisson/Mellin continuation.
-/
structure ProductHeatTraceAnalyticStatus where
  firstFactorOperatorConstructed : Prop
  secondFactorOperatorConstructed : Prop
  productOperatorConstructed : Prop
  separatedSpectrumProved : Prop
  multiplicitiesControlled : Prop
  infiniteHeatTracesConvergent : Prop
  productTraceFactorizationProved : Prop
  smallTimeExpansionDerived : Prop


def productHeatTraceAnalyticClosed
    (s : ProductHeatTraceAnalyticStatus) : Prop :=
  s.firstFactorOperatorConstructed /\
  s.secondFactorOperatorConstructed /\
  s.productOperatorConstructed /\
  s.separatedSpectrumProved /\
  s.multiplicitiesControlled /\
  s.infiniteHeatTracesConvergent /\
  s.productTraceFactorizationProved /\
  s.smallTimeExpansionDerived

end P0EFTJanusFiniteProductHeatTrace
end JanusFormal
