import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteProductHeatTrace

set_option autoImplicit false

/-- Finite spectral mode with real multiplicity/weight. -/
structure WeightedSpectralMode where
  eigenvalue : ℝ
  weight : ℝ

/-- Heat weight of one mode. -/
noncomputable def modeHeatWeight
    (heatTime : ℝ) (mode : WeightedSpectralMode) : ℝ :=
  mode.weight * Real.exp (-heatTime * mode.eigenvalue)

/-- Finite weighted heat trace. -/
noncomputable def finiteWeightedHeatTrace
    (heatTime : ℝ) (modes : List WeightedSpectralMode) : ℝ :=
  (modes.map (modeHeatWeight heatTime)).sum

/-- Product mode for a sum operator `P1 tensor 1 + 1 tensor P2`. -/
def productMode
    (first second : WeightedSpectralMode) : WeightedSpectralMode :=
  { eigenvalue := first.eigenvalue + second.eigenvalue
    weight := first.weight * second.weight }

/-- Finite Cartesian product of two spectral lists. -/
def productSpectrum
    (first second : List WeightedSpectralMode) :
    List WeightedSpectralMode :=
  first.flatMap (fun firstMode => second.map (productMode firstMode))

/-- Heat weight of a product mode factorizes. -/
theorem product_mode_heat_weight_factorizes
    (heatTime : ℝ)
    (first second : WeightedSpectralMode) :
    modeHeatWeight heatTime (productMode first second) =
      modeHeatWeight heatTime first *
        modeHeatWeight heatTime second := by
  unfold modeHeatWeight productMode
  rw [show
    -heatTime * (first.eigenvalue + second.eigenvalue) =
      -heatTime * first.eigenvalue +
        -heatTime * second.eigenvalue by ring]
  rw [Real.exp_add]
  ring

/-- Heat trace of all products with one fixed first-factor mode. -/
theorem fixed_mode_product_heat_trace
    (heatTime : ℝ)
    (firstMode : WeightedSpectralMode)
    (secondModes : List WeightedSpectralMode) :
    finiteWeightedHeatTrace heatTime
        (secondModes.map (productMode firstMode)) =
      modeHeatWeight heatTime firstMode *
        finiteWeightedHeatTrace heatTime secondModes := by
  induction secondModes with
  | nil =>
      simp [finiteWeightedHeatTrace]
  | cons secondMode rest ih =>
      simp [finiteWeightedHeatTrace,
        product_mode_heat_weight_factorizes, ih]
      ring

/-- Exact finite product heat-trace factorization. -/
theorem finite_product_heat_trace_factorizes
    (heatTime : ℝ)
    (firstModes secondModes : List WeightedSpectralMode) :
    finiteWeightedHeatTrace heatTime
        (productSpectrum firstModes secondModes) =
      finiteWeightedHeatTrace heatTime firstModes *
        finiteWeightedHeatTrace heatTime secondModes := by
  induction firstModes with
  | nil =>
      simp [productSpectrum, finiteWeightedHeatTrace]
  | cons firstMode rest ih =>
      rw [productSpectrum]
      simp only [List.flatMap_cons]
      rw [finiteWeightedHeatTrace]
      simp only [List.map_append, List.sum_append]
      rw [show
        (List.map (modeHeatWeight heatTime)
          (List.map (productMode firstMode) secondModes)).sum =
          finiteWeightedHeatTrace heatTime
            (secondModes.map (productMode firstMode)) by
        rfl]
      rw [fixed_mode_product_heat_trace]
      rw [show
        (List.map (modeHeatWeight heatTime)
          (productSpectrum rest secondModes)).sum =
          finiteWeightedHeatTrace heatTime
            (productSpectrum rest secondModes) by
        rfl]
      rw [ih]
      unfold finiteWeightedHeatTrace
      simp
      ring

/-- Opposite PT eta data may have the same squared spectral modes. -/
structure PTSquaredSpectrumPair where
  positiveFoldModes : List WeightedSpectralMode
  negativeFoldModes : List WeightedSpectralMode
  squaredSpectrumEquality : negativeFoldModes = positiveFoldModes

/-- Equal squared spectra give equal parity-even finite heat traces. -/
theorem pt_pair_has_equal_even_heat_trace
    (pair : PTSquaredSpectrumPair)
    (heatTime : ℝ) :
    finiteWeightedHeatTrace heatTime pair.negativeFoldModes =
      finiteWeightedHeatTrace heatTime pair.positiveFoldModes := by
  rw [pair.squaredSpectrumEquality]

/-- Their paired parity-even heat trace is doubled. -/
theorem pt_pair_doubles_even_heat_trace
    (pair : PTSquaredSpectrumPair)
    (heatTime : ℝ) :
    finiteWeightedHeatTrace heatTime pair.positiveFoldModes +
        finiteWeightedHeatTrace heatTime pair.negativeFoldModes =
      2 * finiteWeightedHeatTrace heatTime pair.positiveFoldModes := by
  rw [pt_pair_has_equal_even_heat_trace pair heatTime]
  ring

/--
The finite theorem is exact. The analytic completion must prove summability,
spectral completeness and passage to the infinite product trace for the actual
monopole-twisted Dirac square.
-/
structure ProductHeatTraceAnalyticStatus where
  sphereSpectrumComplete : Prop
  circleSpectrumComplete : Prop
  productOperatorConstructed : Prop
  productSpectrumComplete : Prop
  positiveHeatTimeTraceClassProved : Prop
  infiniteTraceFactorizationProved : Prop
  poissonResummationProved : Prop
  zetaMellinTransformDerived : Prop


def productHeatTraceAnalyticClosure
    (s : ProductHeatTraceAnalyticStatus) : Prop :=
  s.sphereSpectrumComplete /\
  s.circleSpectrumComplete /\
  s.productOperatorConstructed /\
  s.productSpectrumComplete /\
  s.positiveHeatTimeTraceClassProved /\
  s.infiniteTraceFactorizationProved /\
  s.poissonResummationProved /\
  s.zetaMellinTransformDerived

end P0EFTJanusFiniteProductHeatTrace
end JanusFormal
