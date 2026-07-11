import Mathlib

namespace JanusFormal
namespace P0EFTJanusProductThroatLocalInvariants

set_option autoImplicit false

/-- Product throat with round `S2` radius `L` and circle circumference `C`. -/
structure ProductThroatGeometry where
  sphereRadius : ℝ
  circleLength : ℝ
  sphereRadiusPositive : 0 < sphereRadius
  circleLengthPositive : 0 < circleLength

/-- Three-dimensional volume `4*pi*L^2*C`. -/
noncomputable def throatVolume (g : ProductThroatGeometry) : ℝ :=
  4 * Real.pi * g.sphereRadius ^ 2 * g.circleLength

/-- Scalar curvature of `S2_L x S1_C`. -/
noncomputable def scalarCurvature (g : ProductThroatGeometry) : ℝ :=
  2 / g.sphereRadius ^ 2

/-- Squared Ricci norm. -/
noncomputable def ricciSquare (g : ProductThroatGeometry) : ℝ :=
  2 / g.sphereRadius ^ 4

/-- Squared Riemann norm. -/
noncomputable def riemannSquare (g : ProductThroatGeometry) : ℝ :=
  4 / g.sphereRadius ^ 4

/-- Pointwise squared field strength of a charge-`n` Dirac monopole. -/
noncomputable def monopoleFieldSquare
    (g : ProductThroatGeometry) (chernNumber : ℤ) : ℝ :=
  (chernNumber : ℝ) ^ 2 / (2 * g.sphereRadius ^ 4)

/-- The throat volume is positive. -/
theorem throat_volume_positive (g : ProductThroatGeometry) :
    0 < throatVolume g := by
  unfold throatVolume
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) Real.pi_pos)
      (pow_pos g.sphereRadiusPositive 2))
    g.circleLengthPositive

/-- Integrated scalar curvature. -/
theorem integrated_scalar_curvature
    (g : ProductThroatGeometry) :
    scalarCurvature g * throatVolume g =
      8 * Real.pi * g.circleLength := by
  unfold scalarCurvature throatVolume
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hRadius]
  ring

/-- Cleared integrated Ricci-square identity. -/
theorem integrated_ricci_square_cleared
    (g : ProductThroatGeometry) :
    ricciSquare g * throatVolume g * g.sphereRadius ^ 2 =
      8 * Real.pi * g.circleLength := by
  unfold ricciSquare throatVolume
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hRadius]
  ring

/-- Cleared integrated Riemann-square identity. -/
theorem integrated_riemann_square_cleared
    (g : ProductThroatGeometry) :
    riemannSquare g * throatVolume g * g.sphereRadius ^ 2 =
      16 * Real.pi * g.circleLength := by
  unfold riemannSquare throatVolume
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hRadius]
  ring

/-- Cleared integrated monopole-field identity. -/
theorem integrated_monopole_field_square_cleared
    (g : ProductThroatGeometry)
    (chernNumber : ℤ) :
    monopoleFieldSquare g chernNumber * throatVolume g *
        g.sphereRadius ^ 2 =
      2 * Real.pi * (chernNumber : ℝ) ^ 2 * g.circleLength := by
  unfold monopoleFieldSquare throatVolume
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hRadius]
  ring

/-- Positive common homothety of the throat. -/
def rescale
    (g : ProductThroatGeometry)
    (scale : ℝ)
    (hScale : 0 < scale) : ProductThroatGeometry :=
  { sphereRadius := scale * g.sphereRadius
    circleLength := scale * g.circleLength
    sphereRadiusPositive := mul_pos hScale g.sphereRadiusPositive
    circleLengthPositive := mul_pos hScale g.circleLengthPositive }

/-- Volume scales cubically. -/
theorem throat_volume_rescale
    (g : ProductThroatGeometry)
    (scale : ℝ)
    (hScale : 0 < scale) :
    throatVolume (rescale g scale hScale) =
      scale ^ 3 * throatVolume g := by
  unfold throatVolume rescale
  ring

/-- Scalar curvature scales as inverse length squared. -/
theorem scalar_curvature_rescale_cleared
    (g : ProductThroatGeometry)
    (scale : ℝ)
    (hScale : 0 < scale) :
    scalarCurvature (rescale g scale hScale) * scale ^ 2 =
      scalarCurvature g := by
  unfold scalarCurvature rescale
  have hScaleNonzero : scale ≠ 0 := ne_of_gt hScale
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hScaleNonzero, hRadius]
  ring

/-- The integrated Einstein term scales linearly. -/
theorem integrated_scalar_rescale
    (g : ProductThroatGeometry)
    (scale : ℝ)
    (hScale : 0 < scale) :
    scalarCurvature (rescale g scale hScale) *
        throatVolume (rescale g scale hScale) =
      scale * (scalarCurvature g * throatVolume g) := by
  rw [integrated_scalar_curvature, integrated_scalar_curvature]
  unfold rescale
  ring

/-- The integrated curvature-square term scales inversely. -/
theorem integrated_ricci_square_rescale_cleared
    (g : ProductThroatGeometry)
    (scale : ℝ)
    (hScale : 0 < scale) :
    scale * ricciSquare (rescale g scale hScale) *
        throatVolume (rescale g scale hScale) =
      ricciSquare g * throatVolume g := by
  unfold ricciSquare throatVolume rescale
  have hScaleNonzero : scale ≠ 0 := ne_of_gt hScale
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hScaleNonzero, hRadius]
  ring

/--
The local invariant basis therefore carries the homothety powers `L^3`, `L`
and `L^-1`.  Their coefficients are renormalized couplings; geometry fixes the
basis but does not by itself fix those coefficients.
-/
structure LocalInvariantDerivationStatus where
  productMetricConstructed : Prop
  LeviCivitaCurvatureComputed : Prop
  monopoleConnectionConstructed : Prop
  bundleCurvatureNormComputed : Prop
  heatCoefficientConventionFixed : Prop
  renormalizedLocalCouplingsDerived : Prop


def localInvariantDerivationClosed
    (s : LocalInvariantDerivationStatus) : Prop :=
  s.productMetricConstructed /\
  s.LeviCivitaCurvatureComputed /\
  s.monopoleConnectionConstructed /\
  s.bundleCurvatureNormComputed /\
  s.heatCoefficientConventionFixed /\
  s.renormalizedLocalCouplingsDerived

end P0EFTJanusProductThroatLocalInvariants
end JanusFormal
