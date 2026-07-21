import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicDiagonalLorentzFrame4D

/-!
# Determinant-volume bridge for the holonomic diagonal model metric

The Gram matrix of the exact holonomic diagonal pairing is the existing
diagonal Lorentz matrix.  Its absolute determinant density is therefore
exactly the volume factor used by the global scalar action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHolonomicDiagonalVolumeBridge4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusHolonomicDiagonalSharp4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Gram matrix of the exact diagonal pairing in the fixed time-first
holonomic model basis. -/
def holonomicDiagonalGramMatrix
    (magnitude : HolonomicCoefficients) : Matrix (Fin 4) (Fin 4) Real :=
  fun i j => holonomicDiagonalPair magnitude
    (tangentCoordinate i) (tangentCoordinate j)

theorem holonomicDiagonalGramMatrix_eq_lorentzMetric
    (magnitude : HolonomicCoefficients) :
    holonomicDiagonalGramMatrix magnitude = lorentzMetric magnitude := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [holonomicDiagonalGramMatrix, holonomicDiagonalPair,
      holonomicVectorCoefficient_tangentCoordinate, lorentzMetric]
  · simp [holonomicDiagonalGramMatrix, holonomicDiagonalPair,
      holonomicVectorCoefficient_tangentCoordinate, lorentzMetric, hij]

/-- Absolute determinant density of the diagonal model Gram matrix. -/
def holonomicDiagonalGramVolumeDensity
    (magnitude : HolonomicCoefficients) : Real :=
  Real.sqrt |(holonomicDiagonalGramMatrix magnitude).det|

theorem holonomicDiagonalGramVolumeDensity_eq_sqrt_prod
    (magnitude : HolonomicCoefficients)
    (hPositive : ∀ index, 0 < magnitude index) :
    holonomicDiagonalGramVolumeDensity magnitude =
      Real.sqrt (∏ index : Fin 4, magnitude index) := by
  rw [holonomicDiagonalGramVolumeDensity,
    holonomicDiagonalGramMatrix_eq_lorentzMetric, lorentzMetric,
    Matrix.det_diagonal]
  have hProductPositive : 0 < ∏ index : Fin 4, magnitude index :=
    Finset.prod_pos fun index _ => hPositive index
  have hSignedProduct :
      (∏ index : Fin 4, signature index * magnitude index) =
        -(∏ index : Fin 4, magnitude index) := by
    simp [Fin.prod_univ_succ, signature]
  rw [hSignedProduct, abs_neg, abs_of_pos hProductPositive]

/-- Exact volume bridge for the same smooth positive magnitude field used by
the global scalar action. -/
theorem diagonalMetricVolumeDensity_eq_holonomicDiagonalGramVolumeDensity
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    diagonalMetricVolumeDensity period hPeriod magnitude point =
      holonomicDiagonalGramVolumeDensity (magnitude point) := by
  rw [holonomicDiagonalGramVolumeDensity_eq_sqrt_prod
    (magnitude point) (hPositive point)]
  rfl

end

end P0EFTJanusMappingTorusHolonomicDiagonalVolumeBridge4D
end JanusFormal
