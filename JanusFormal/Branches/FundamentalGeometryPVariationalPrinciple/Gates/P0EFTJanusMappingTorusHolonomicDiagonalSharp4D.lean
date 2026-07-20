import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

/-!
# Exact diagonal sharp in holonomic model coordinates

This gate constructs the inverse diagonal Lorentz contraction in the exact
time-first coordinates used by the global scalar action.  The construction
is model-space algebra and does not assert a forbidden global smooth frame.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHolonomicDiagonalSharp4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Covariant diagonal Lorentz pairing in the exact holonomic model basis. -/
def holonomicDiagonalPair
    (magnitude : HolonomicCoefficients)
    (first second : CoverCoordinates) : Real :=
  ∑ index : Fin 4,
    signature index * magnitude index *
      holonomicVectorCoefficient first index *
      holonomicVectorCoefficient second index

/-- Explicit inverse diagonal metric applied to a model covector. -/
def holonomicDiagonalSharp
    (magnitude : HolonomicCoefficients)
    (covector : CoverCoordinates → Real) : CoverCoordinates :=
  ∑ index : Fin 4,
    (signature index / magnitude index * covector (tangentCoordinate index)) •
      tangentCoordinate index

private theorem signature_sq (index : Fin 4) :
    signature index * signature index = 1 := by
  fin_cases index <;> norm_num [signature]

@[simp]
theorem holonomicVectorCoefficient_holonomicDiagonalSharp
    (magnitude : HolonomicCoefficients)
    (covector : CoverCoordinates → Real)
    (coefficientIndex : Fin 4) :
    holonomicVectorCoefficient
        (holonomicDiagonalSharp magnitude covector) coefficientIndex =
      signature coefficientIndex / magnitude coefficientIndex *
        covector (tangentCoordinate coefficientIndex) := by
  change holonomicCoefficientLinearMap
      (holonomicDiagonalSharp magnitude covector) coefficientIndex = _
  rw [holonomicDiagonalSharp, map_sum]
  simp [holonomicVectorCoefficient_tangentCoordinate]

/-- The explicit sharp is a right inverse of the diagonal flat pairing. -/
theorem holonomicDiagonalPair_sharp
    (magnitude : HolonomicCoefficients)
    (hMagnitude : ∀ index, magnitude index ≠ 0)
    (covector : CoverCoordinates →L[Real] Real)
    (vector : CoverCoordinates) :
    holonomicDiagonalPair magnitude
        (holonomicDiagonalSharp magnitude covector) vector =
      covector vector := by
  unfold holonomicDiagonalPair
  simp_rw [holonomicVectorCoefficient_holonomicDiagonalSharp]
  calc
    ∑ index : Fin 4,
        signature index * magnitude index *
            (signature index / magnitude index *
              covector (tangentCoordinate index)) *
          holonomicVectorCoefficient vector index =
        ∑ index : Fin 4,
          holonomicVectorCoefficient vector index *
            covector (tangentCoordinate index) := by
      apply Finset.sum_congr rfl
      intro index _
      have hSignature : signature index ^ 2 = 1 := by
        simpa [pow_two] using signature_sq index
      field_simp [hMagnitude index]
      simp [hSignature]
    _ = covector
        (∑ index : Fin 4,
          holonomicVectorCoefficient vector index • tangentCoordinate index) := by
      simp
    _ = covector vector := by
      rw [holonomic_vector_decomposition]

/-- Covector contraction with the sharp is exactly the inverse diagonal
quadratic form. -/
theorem covector_holonomicDiagonalSharp
    (magnitude : HolonomicCoefficients)
    (covector : CoverCoordinates →L[Real] Real) :
    covector (holonomicDiagonalSharp magnitude (fun vector => covector vector)) =
      ∑ index : Fin 4,
        signature index / magnitude index *
          covector (tangentCoordinate index) ^ 2 := by
  rw [holonomicDiagonalSharp, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp [pow_two]
  ring

/-- The kinetic density in the global action is precisely one half of the
model-covector contraction with the explicit diagonal sharp whenever the
model covector has the genuine holonomic differential components. -/
theorem diagonalHolonomicKineticDensity_eq_model_sharp_contraction
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (modelCovector : CoverCoordinates →L[Real] Real)
    (hComponents : ∀ index,
      modelCovector (tangentCoordinate index) =
        holonomicCovectorComponent period hPeriod field point index) :
    diagonalHolonomicKineticDensity period hPeriod magnitude field point =
      (1 / 2 : Real) *
        modelCovector (holonomicDiagonalSharp (magnitude point)
          (fun vector => modelCovector vector)) := by
  rw [covector_holonomicDiagonalSharp]
  simp_rw [hComponents]
  rfl

end

end P0EFTJanusMappingTorusHolonomicDiagonalSharp4D
end JanusFormal
