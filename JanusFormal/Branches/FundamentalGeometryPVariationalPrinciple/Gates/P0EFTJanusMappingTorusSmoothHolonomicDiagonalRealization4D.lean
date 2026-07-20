import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPointwiseHolonomicDiagonalLorentzMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Smooth realization interface for the holonomic diagonal metric

Once the canonical pointwise tensor family is realized by a genuine smooth
symmetric tensor section, all remaining algebraic fields of
`SmoothGeneralLorentzMetric` are discharged automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusPointwiseHolonomicDiagonalLorentzMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Genuine smooth tensor data realizing the already constructed canonical
pointwise diagonal tensor family. -/
structure SmoothHolonomicDiagonalRealization
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index) where
  tensor : SmoothSymmetricCovariantTwoTensor period hPeriod
  realizes : ∀ point,
    tensor.tensor point =
      pointwiseHolonomicDiagonalTensor period hPeriod magnitude hPositive point

/-- A smooth realization canonically supplies the full general-Lorentz metric
record, using the same pointwise musical as the realized tensor. -/
def SmoothHolonomicDiagonalRealization.toSmoothGeneralLorentzMetric
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (realization :
      SmoothHolonomicDiagonalRealization period hPeriod magnitude hPositive) :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor := realization.tensor
  musical := pointwiseHolonomicDiagonalMusical period hPeriod magnitude hPositive
  musical_eq_tensor := by
    intro point
    rw [realization.realizes point]
    rfl
  lorentzian := by
    intro point
    unfold IsLorentzianAt
    rw [realization.realizes point]
    exact pointwiseHolonomicDiagonalTensor_lorentzian period hPeriod
      magnitude hPositive point

@[simp]
theorem SmoothHolonomicDiagonalRealization.toSmoothGeneralLorentzMetric_tensor
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (realization :
      SmoothHolonomicDiagonalRealization period hPeriod magnitude hPositive) :
    (realization.toSmoothGeneralLorentzMetric period hPeriod magnitude
      hPositive).tensor = realization.tensor :=
  rfl

@[simp]
theorem SmoothHolonomicDiagonalRealization.toSmoothGeneralLorentzMetric_musical
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (realization :
      SmoothHolonomicDiagonalRealization period hPeriod magnitude hPositive)
    (point : EffectiveQuotient period hPeriod) :
    (realization.toSmoothGeneralLorentzMetric period hPeriod magnitude
      hPositive).musical point =
        pointwiseHolonomicDiagonalMusical period hPeriod magnitude hPositive
          point :=
  rfl

end

end P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D
end JanusFormal
