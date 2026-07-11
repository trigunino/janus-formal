import Mathlib

namespace JanusFormal
namespace P0EFTJanusMonopoleDiracSpectrum

set_option autoImplicit false

/--
Algebraic spectrum of the round two-sphere Dirac operator twisted by a monopole
of absolute Chern number `m`.  The radial label is `k = 0,1,...` and the cleared
spectral law is

`lambda_k^2 * L^2 = k * (k + m)`.
-/
def clearedEigenvalueSquared
    (monopoleMagnitude radialLevel : ℕ) : ℕ :=
  radialLevel * (radialLevel + monopoleMagnitude)

/-- Degeneracy of the level labelled by `k`. -/
def levelDegeneracy
    (monopoleMagnitude radialLevel : ℕ) : ℕ :=
  monopoleMagnitude + 2 * radialLevel

@[simp] theorem zero_level_has_zero_eigenvalue
    (monopoleMagnitude : ℕ) :
    clearedEigenvalueSquared monopoleMagnitude 0 = 0 := by
  simp [clearedEigenvalueSquared]

@[simp] theorem zero_level_degeneracy_is_monopole_magnitude
    (monopoleMagnitude : ℕ) :
    levelDegeneracy monopoleMagnitude 0 = monopoleMagnitude := by
  simp [levelDegeneracy]

@[simp] theorem first_positive_level_gap
    (monopoleMagnitude : ℕ) :
    clearedEigenvalueSquared monopoleMagnitude 1 =
      monopoleMagnitude + 1 := by
  simp [clearedEigenvalueSquared]

@[simp] theorem first_positive_level_degeneracy
    (monopoleMagnitude : ℕ) :
    levelDegeneracy monopoleMagnitude 1 =
      monopoleMagnitude + 2 := by
  simp [levelDegeneracy]

/-- Primitive monopole sector. -/
def PrimitiveMonopole (monopoleMagnitude : ℕ) : Prop :=
  monopoleMagnitude = 1

/-- A primitive monopole has one chiral zero mode. -/
theorem primitive_monopole_has_one_zero_mode
    (monopoleMagnitude : ℕ)
    (hPrimitive : PrimitiveMonopole monopoleMagnitude) :
    levelDegeneracy monopoleMagnitude 0 = 1 := by
  simp [PrimitiveMonopole] at hPrimitive
  simpa [hPrimitive] using
    zero_level_degeneracy_is_monopole_magnitude monopoleMagnitude

/-- Its first nonzero squared gap is `2/L^2`. -/
theorem primitive_first_gap_is_two
    (monopoleMagnitude : ℕ)
    (hPrimitive : PrimitiveMonopole monopoleMagnitude) :
    clearedEigenvalueSquared monopoleMagnitude 1 = 2 := by
  simp [PrimitiveMonopole] at hPrimitive
  simp [hPrimitive]

/-- Signed index data: the index equals the monopole Chern number. -/
structure MonopoleIndexPackage where
  chernNumber : ℤ
  diracIndex : ℤ
  zeroModeMultiplicity : ℕ
  indexLaw : diracIndex = chernNumber
  multiplicityLaw : zeroModeMultiplicity = chernNumber.natAbs

/-- Primitive Chern number gives exactly one zero mode. -/
theorem primitive_index_has_one_zero_mode
    (s : MonopoleIndexPackage)
    (hPrimitive : s.chernNumber.natAbs = 1) :
    s.zeroModeMultiplicity = 1 := by
  rw [s.multiplicityLaw, hPrimitive]

/--
The explicit spectrum and the index theorem are primary mathematical inputs to
the spectral program.  A complete geometric formalization must construct the
SpinC bundle, connection and self-adjoint Dirac operator rather than only carry
these formulas.
-/
structure GeometricDiracRealizationStatus where
  roundSphereMetricConstructed : Prop
  monopoleLineBundleConstructed : Prop
  unitaryConnectionConstructed : Prop
  spinCBundleConstructed : Prop
  twistedDiracOperatorConstructed : Prop
  selfAdjointnessProved : Prop
  compactResolventProved : Prop
  indexLawProved : Prop
  explicitSpectrumProved : Prop


def geometricDiracRealizationClosed
    (s : GeometricDiracRealizationStatus) : Prop :=
  s.roundSphereMetricConstructed /\
  s.monopoleLineBundleConstructed /\
  s.unitaryConnectionConstructed /\
  s.spinCBundleConstructed /\
  s.twistedDiracOperatorConstructed /\
  s.selfAdjointnessProved /\
  s.compactResolventProved /\
  s.indexLawProved /\
  s.explicitSpectrumProved

end P0EFTJanusMonopoleDiracSpectrum
end JanusFormal
