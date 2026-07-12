import Mathlib

namespace JanusFormal
namespace P0EFTJanusProductThroatLocalInvariants

set_option autoImplicit false

/-- Algebraic invariant data for `S2_L x S1_(L*T)`. -/
structure ProductThroatInvariantData where
  geometricLength : ℝ
  circleModulus : ℝ
  piConstant : ℝ
  monopoleNumber : ℤ
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus
  piConstantPositive : 0 < piConstant

/-- Product volume `4*pi*L^3*T`. -/
def throatVolume (s : ProductThroatInvariantData) : ℝ :=
  4 * s.piConstant * s.geometricLength ^ 3 * s.circleModulus

/-- Scalar curvature of the round sphere factor. -/
noncomputable def scalarCurvature (s : ProductThroatInvariantData) : ℝ :=
  2 / s.geometricLength ^ 2

/-- Ricci-tensor norm squared on `S2 x S1`. -/
noncomputable def ricciSquaredDensity
    (s : ProductThroatInvariantData) : ℝ :=
  2 / s.geometricLength ^ 4

/-- Riemann-tensor norm squared on `S2 x S1`. -/
noncomputable def riemannSquaredDensity
    (s : ProductThroatInvariantData) : ℝ :=
  4 / s.geometricLength ^ 4

/-- Convention `F_{mu nu}F^{mu nu}=n^2/(2*L^4)` for the Dirac monopole. -/
noncomputable def monopoleFieldSquaredDensity
    (s : ProductThroatInvariantData) : ℝ :=
  (s.monopoleNumber : ℝ) ^ 2 /
    (2 * s.geometricLength ^ 4)

/-- Integrated scalar curvature. -/
noncomputable def integratedScalarCurvature
    (s : ProductThroatInvariantData) : ℝ :=
  scalarCurvature s * throatVolume s

/-- Integrated scalar-curvature square. -/
noncomputable def integratedScalarCurvatureSquared
    (s : ProductThroatInvariantData) : ℝ :=
  scalarCurvature s ^ 2 * throatVolume s

/-- Integrated Ricci norm squared. -/
noncomputable def integratedRicciSquared
    (s : ProductThroatInvariantData) : ℝ :=
  ricciSquaredDensity s * throatVolume s

/-- Integrated Riemann norm squared. -/
noncomputable def integratedRiemannSquared
    (s : ProductThroatInvariantData) : ℝ :=
  riemannSquaredDensity s * throatVolume s

/-- Integrated monopole field-strength square. -/
noncomputable def integratedMonopoleFieldSquared
    (s : ProductThroatInvariantData) : ℝ :=
  monopoleFieldSquaredDensity s * throatVolume s

/-- Exact product volume. -/
theorem throat_volume_formula
    (s : ProductThroatInvariantData) :
    throatVolume s =
      4 * s.piConstant * s.geometricLength ^ 3 * s.circleModulus := by
  rfl

/-- `integral R = 8*pi*L*T`. -/
theorem integrated_scalar_curvature_formula
    (s : ProductThroatInvariantData) :
    integratedScalarCurvature s =
      8 * s.piConstant * s.geometricLength * s.circleModulus := by
  have hLength : s.geometricLength ≠ 0 :=
    ne_of_gt s.geometricLengthPositive
  unfold integratedScalarCurvature scalarCurvature throatVolume
  field_simp [hLength]
  ring

/-- `integral R^2 = 16*pi*T/L`. -/
theorem integrated_scalar_curvature_squared_formula
    (s : ProductThroatInvariantData) :
    integratedScalarCurvatureSquared s =
      16 * s.piConstant * s.circleModulus / s.geometricLength := by
  have hLength : s.geometricLength ≠ 0 :=
    ne_of_gt s.geometricLengthPositive
  unfold integratedScalarCurvatureSquared scalarCurvature throatVolume
  field_simp [hLength]
  ring

/-- `integral |Ric|^2 = 8*pi*T/L`. -/
theorem integrated_ricci_squared_formula
    (s : ProductThroatInvariantData) :
    integratedRicciSquared s =
      8 * s.piConstant * s.circleModulus / s.geometricLength := by
  have hLength : s.geometricLength ≠ 0 :=
    ne_of_gt s.geometricLengthPositive
  unfold integratedRicciSquared ricciSquaredDensity throatVolume
  field_simp [hLength]
  ring

/-- `integral |Riem|^2 = 16*pi*T/L`. -/
theorem integrated_riemann_squared_formula
    (s : ProductThroatInvariantData) :
    integratedRiemannSquared s =
      16 * s.piConstant * s.circleModulus / s.geometricLength := by
  have hLength : s.geometricLength ≠ 0 :=
    ne_of_gt s.geometricLengthPositive
  unfold integratedRiemannSquared riemannSquaredDensity throatVolume
  field_simp [hLength]
  ring

/-- `integral F_{mu nu}F^{mu nu} = 2*pi*n^2*T/L` in the declared convention. -/
theorem integrated_monopole_field_squared_formula
    (s : ProductThroatInvariantData) :
    integratedMonopoleFieldSquared s =
      2 * s.piConstant * (s.monopoleNumber : ℝ) ^ 2 *
        s.circleModulus / s.geometricLength := by
  have hLength : s.geometricLength ≠ 0 :=
    ne_of_gt s.geometricLengthPositive
  unfold integratedMonopoleFieldSquared
    monopoleFieldSquaredDensity throatVolume
  field_simp [hLength]
  ring

/-- Pure geometric combination appearing in the universal closed-manifold `a4` coefficient. -/
noncomputable def integratedUniversalA4Geometry
    (s : ProductThroatInvariantData) : ℝ :=
  5 * integratedScalarCurvatureSquared s -
    2 * integratedRicciSquared s +
    2 * integratedRiemannSquared s

/-- The universal geometric `a4` combination is `96*pi*T/L`. -/
theorem integrated_universal_a4_geometry_formula
    (s : ProductThroatInvariantData) :
    integratedUniversalA4Geometry s =
      96 * s.piConstant * s.circleModulus / s.geometricLength := by
  rw [integratedUniversalA4Geometry,
    integrated_scalar_curvature_squared_formula,
    integrated_ricci_squared_formula,
    integrated_riemann_squared_formula]
  ring

/-- Every displayed integrated local invariant is linear in the circle modulus. -/
theorem displayed_local_invariants_linear_in_circle
    (s : ProductThroatInvariantData) :
    integratedScalarCurvature s =
        s.circleModulus * (8 * s.piConstant * s.geometricLength) /\
    integratedScalarCurvatureSquared s =
        s.circleModulus * (16 * s.piConstant / s.geometricLength) /\
    integratedMonopoleFieldSquared s =
        s.circleModulus *
          (2 * s.piConstant * (s.monopoleNumber : ℝ) ^ 2 /
            s.geometricLength) := by
  constructor
  · rw [integrated_scalar_curvature_formula]
    ring
  · constructor
    · rw [integrated_scalar_curvature_squared_formula]
      ring
    · rw [integrated_monopole_field_squared_formula]
      ring

/--
These formulas supply the local invariant basis needed for the `a0`, `a2` and
`a4` coefficients. Operator-dependent endomorphism and bundle-curvature traces
must still be computed for the actual monopole-twisted Dirac operator.
-/
structure ProductThroatSeeleyDeWittStatus where
  productMetricConstructed : Prop
  curvatureTensorsComputed : Prop
  monopoleCurvatureGlobalized : Prop
  diracLichnerowiczEndomorphismComputed : Prop
  bundleCurvatureTraceComputed : Prop
  a0Computed : Prop
  a2Computed : Prop
  a4Computed : Prop
  finiteCountertermsMatched : Prop


def productThroatSeeleyDeWittClosed
    (s : ProductThroatSeeleyDeWittStatus) : Prop :=
  s.productMetricConstructed /\
  s.curvatureTensorsComputed /\
  s.monopoleCurvatureGlobalized /\
  s.diracLichnerowiczEndomorphismComputed /\
  s.bundleCurvatureTraceComputed /\
  s.a0Computed /\
  s.a2Computed /\
  s.a4Computed /\
  s.finiteCountertermsMatched

end P0EFTJanusProductThroatLocalInvariants
end JanusFormal
