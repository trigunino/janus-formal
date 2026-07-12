import Mathlib

namespace JanusFormal
namespace P0EFTJanusDiracScaleOrbitNoGo

set_option autoImplicit false

/-- Rescale a length by a nonzero factor. -/
def rescaleLength (scale length : ℝ) : ℝ :=
  scale * length

/-- Rescale an inverse-area quantity. -/
noncomputable def rescaleInverseArea (scale value : ℝ) : ℝ :=
  value / scale ^ 2

/-- Cleared Dirac gap laws are invariant under a common length rescaling. -/
theorem dirac_gap_law_scale_invariant
    (scale gapSquared radius constant : ℝ)
    (hScale : scale ≠ 0)
    (hGap : gapSquared * radius ^ 2 = constant) :
    rescaleInverseArea scale gapSquared *
        rescaleLength scale radius ^ 2 = constant := by
  unfold rescaleInverseArea rescaleLength
  field_simp [pow_ne_zero 2 hScale]
  nlinarith [hGap]

/-- The primitive LL flux law is invariant under `A -> s A`, `q -> q/s^2`. -/
theorem primitive_ll_flux_scale_invariant
    (scale chargeUnit alphaSquaredLength : ℝ)
    (hScale : scale ≠ 0)
    (hFlux : 16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1) :
    16 * (rescaleInverseArea scale chargeUnit) ^ 2 *
        (rescaleLength scale alphaSquaredLength) ^ 4 = 1 := by
  unfold rescaleInverseArea rescaleLength
  field_simp [pow_ne_zero 2 hScale]
  nlinarith [hFlux]

/-- Dimensionless modulus and holonomy do not change under global metric scaling. -/
def rescaleDimensionless (value : ℝ) : ℝ := value

@[simp] theorem dimensionless_data_are_scale_fixed
    (value : ℝ) :
    rescaleDimensionless value = value :=
  rfl

/--
A spectral solution with a nontrivial positive rescaling generates a distinct
solution unless a dimensionful law fixes the orbit.
-/
structure SpectralScaleOrbit where
  scaleFactor : ℝ
  originalLength : ℝ
  scaleFactorPositive : 0 < scaleFactor
  scaleFactorNontrivial : scaleFactor ≠ 1
  originalLengthPositive : 0 < originalLength

/-- A nontrivial positive scale changes the length. -/
theorem nontrivial_scale_changes_length
    (s : SpectralScaleOrbit) :
    rescaleLength s.scaleFactor s.originalLength ≠ s.originalLength := by
  unfold rescaleLength
  intro hEqual
  have hFactor :
      (s.scaleFactor - 1) * s.originalLength = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hFactor with hScale | hLength
  · apply s.scaleFactorNontrivial
    linarith
  · exact (ne_of_gt s.originalLengthPositive) hLength

/--
Dirac spectrum, eta, primitive flux and holonomy can fix ratios and discrete
sectors, but their homogeneous equations do not fix the common absolute length.
A renormalization scale, boundary charge, gravitational coupling relation or
other dimensionful input must break this orbit.
-/
structure AbsoluteScaleBreakingStatus where
  diracRatiosDerived : Prop
  etaAndHolonomyDerived : Prop
  primitiveFluxDerived : Prop
  commonScaleOrbitIdentified : Prop
  quantumTransmutationScaleDerived : Prop
  bimetricHamiltonianScaleDerived : Prop
  bulkBoundaryChargeUnitDerived : Prop
  commonScaleOrbitBroken : Prop
  absoluteAlphaDerived : Prop


def absoluteScaleBreakingClosed
    (s : AbsoluteScaleBreakingStatus) : Prop :=
  s.diracRatiosDerived /\
  s.etaAndHolonomyDerived /\
  s.primitiveFluxDerived /\
  s.commonScaleOrbitIdentified /\
  (s.quantumTransmutationScaleDerived \/
    s.bimetricHamiltonianScaleDerived \/
    s.bulkBoundaryChargeUnitDerived) /\
  s.commonScaleOrbitBroken /\
  s.absoluteAlphaDerived

end P0EFTJanusDiracScaleOrbitNoGo
end JanusFormal
