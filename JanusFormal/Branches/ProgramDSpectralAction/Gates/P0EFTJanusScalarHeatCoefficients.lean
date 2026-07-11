import Mathlib
import JanusFormal.Branches.ProgramDSpectralAction.Gates.P0EFTJanusProductThroatLocalInvariants

namespace JanusFormal
namespace P0EFTJanusScalarHeatCoefficients

set_option autoImplicit false

open P0EFTJanusProductThroatLocalInvariants

/-- Integrated `a0` coefficient before the universal `(4*pi*t)^(-3/2)` factor. -/
noncomputable def scalarA0 (g : ProductThroatGeometry) : ℝ :=
  throatVolume g

/-- Integrated `a2` coefficient for the minimal scalar Laplacian. -/
noncomputable def scalarA2 (g : ProductThroatGeometry) : ℝ :=
  scalarCurvature g * throatVolume g / 6

/-- Integrated `a4` coefficient for the minimal scalar Laplacian on a closed manifold. -/
noncomputable def scalarA4 (g : ProductThroatGeometry) : ℝ :=
  (5 * scalarCurvature g ^ 2 -
      2 * ricciSquare g +
      2 * riemannSquare g) * throatVolume g / 360

/-- Closed form of `a0`. -/
theorem scalar_a0_closed_form (g : ProductThroatGeometry) :
    scalarA0 g =
      4 * Real.pi * g.sphereRadius ^ 2 * g.circleLength := by
  rfl

/-- Closed form of `a2`. -/
theorem scalar_a2_closed_form (g : ProductThroatGeometry) :
    scalarA2 g = 4 * Real.pi * g.circleLength / 3 := by
  unfold scalarA2
  rw [integrated_scalar_curvature]
  ring

/-- Closed form of `a4`. -/
theorem scalar_a4_closed_form (g : ProductThroatGeometry) :
    scalarA4 g =
      4 * Real.pi * g.circleLength /
        (15 * g.sphereRadius ^ 2) := by
  unfold scalarA4 scalarCurvature ricciSquare riemannSquare throatVolume
  have hRadius : g.sphereRadius ≠ 0 :=
    ne_of_gt g.sphereRadiusPositive
  field_simp [hRadius]
  ring

/-- Product throat parametrized by radius `L` and dimensionless circumference modulus `T`. -/
def normalizedThroat
    (radius modulus : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus) : ProductThroatGeometry :=
  { sphereRadius := radius
    circleLength := radius * modulus
    sphereRadiusPositive := hRadius
    circleLengthPositive := mul_pos hRadius hModulus }

/-- The normalized `a0` coefficient scales as `L^3`. -/
theorem normalized_scalar_a0
    (radius modulus : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus) :
    scalarA0 (normalizedThroat radius modulus hRadius hModulus) =
      4 * Real.pi * modulus * radius ^ 3 := by
  rw [scalar_a0_closed_form]
  unfold normalizedThroat
  ring

/-- The normalized `a2` coefficient scales as `L`. -/
theorem normalized_scalar_a2
    (radius modulus : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus) :
    scalarA2 (normalizedThroat radius modulus hRadius hModulus) =
      4 * Real.pi * modulus * radius / 3 := by
  rw [scalar_a2_closed_form]
  unfold normalizedThroat
  ring

/-- The normalized `a4` coefficient scales as `L^-1`. -/
theorem normalized_scalar_a4
    (radius modulus : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus) :
    scalarA4 (normalizedThroat radius modulus hRadius hModulus) =
      4 * Real.pi * modulus / (15 * radius) := by
  rw [scalar_a4_closed_form]
  unfold normalizedThroat
  have hRadiusNonzero : radius ≠ 0 := ne_of_gt hRadius
  field_simp [hRadiusNonzero]
  ring

/-- `a0` obeys cubic homothety scaling at fixed modulus. -/
theorem scalar_a0_homothety
    (radius modulus scale : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus)
    (hScale : 0 < scale) :
    scalarA0
        (normalizedThroat (scale * radius) modulus
          (mul_pos hScale hRadius) hModulus) =
      scale ^ 3 *
        scalarA0 (normalizedThroat radius modulus hRadius hModulus) := by
  rw [normalized_scalar_a0, normalized_scalar_a0]
  ring

/-- `a2` obeys linear homothety scaling at fixed modulus. -/
theorem scalar_a2_homothety
    (radius modulus scale : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus)
    (hScale : 0 < scale) :
    scalarA2
        (normalizedThroat (scale * radius) modulus
          (mul_pos hScale hRadius) hModulus) =
      scale *
        scalarA2 (normalizedThroat radius modulus hRadius hModulus) := by
  rw [normalized_scalar_a2, normalized_scalar_a2]
  ring

/-- `a4` obeys inverse homothety scaling at fixed modulus. -/
theorem scalar_a4_homothety_cleared
    (radius modulus scale : ℝ)
    (hRadius : 0 < radius)
    (hModulus : 0 < modulus)
    (hScale : 0 < scale) :
    scale *
        scalarA4
          (normalizedThroat (scale * radius) modulus
            (mul_pos hScale hRadius) hModulus) =
      scalarA4 (normalizedThroat radius modulus hRadius hModulus) := by
  rw [normalized_scalar_a4, normalized_scalar_a4]
  have hScaleNonzero : scale ≠ 0 := ne_of_gt hScale
  have hRadiusNonzero : radius ≠ 0 := ne_of_gt hRadius
  field_simp [hScaleNonzero, hRadiusNonzero]
  ring

/--
These are reference coefficients for a minimal scalar Laplacian. The actual
monopole-twisted Dirac operator has different endomorphism and bundle-curvature
terms; their convention-dependent coefficients must be derived separately.
-/
structure DiracHeatCoefficientStatus where
  lichnerowiczFormulaFixed : Prop
  laplaceTypeSignConventionFixed : Prop
  spinorTraceComputed : Prop
  monopoleCurvatureContributionComputed : Prop
  etaOddPartSeparated : Prop
  integratedDiracCoefficientsDerived : Prop


def diracHeatCoefficientClosure
    (s : DiracHeatCoefficientStatus) : Prop :=
  s.lichnerowiczFormulaFixed /\
  s.laplaceTypeSignConventionFixed /\
  s.spinorTraceComputed /\
  s.monopoleCurvatureContributionComputed /\
  s.etaOddPartSeparated /\
  s.integratedDiracCoefficientsDerived

end P0EFTJanusScalarHeatCoefficients
end JanusFormal
