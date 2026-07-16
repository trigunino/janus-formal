import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

/-!
# Scalar diffeomorphism generator and Noether operator on D8

This gate bundles the intrinsic scalar Lie derivative on the actual smooth D8
quotient as a linear gauge generator.  Composing a supplied scalar Euler
covector with this concrete generator gives its exact Noether operator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem scalarLieDerivative_smulGhost
    (scalarCoefficient : Real)
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (background : SmoothQuotientField period hPeriod Real) :
    scalarLieDerivative period hPeriod (scalarCoefficient • ghost) background =
      scalarCoefficient •
        scalarLieDerivative period hPeriod ghost background := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change mvfderiv coverModelWithCorners background.toFun point
      (scalarCoefficient • ghost point) =
    scalarCoefficient •
      mvfderiv coverModelWithCorners background.toFun point (ghost point)
  exact map_smul _ _ _

/-- The concrete scalar diffeomorphism generator
`R_background(c) = L_c background` on the actual quotient. -/
def scalarDiffeomorphismGaugeGenerator
    (background : SmoothQuotientField period hPeriod Real) :
    SmoothDiffeomorphismGhost period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun ghost := scalarLieDerivative period hPeriod ghost background
  map_add' first second :=
    scalarLieDerivative_addGhost period hPeriod first second background
  map_smul' scalarCoefficient ghost :=
    scalarLieDerivative_smulGhost period hPeriod scalarCoefficient ghost background

@[simp]
theorem scalarDiffeomorphismGaugeGenerator_apply
    (background : SmoothQuotientField period hPeriod Real)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    scalarDiffeomorphismGaugeGenerator period hPeriod background ghost =
      scalarLieDerivative period hPeriod ghost background :=
  rfl

/-- The generator on a selected scalar component of either independent matter
sector. -/
def independentMatterDiffeomorphismGaugeGenerator
    (fields : IndependentFields period hPeriod)
    (sector : Fin 2) (component : Fin 4) :
    SmoothDiffeomorphismGhost period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real :=
  scalarDiffeomorphismGaugeGenerator period hPeriod
    (independentMatterScalar period hPeriod fields sector component)

/-- The exact scalar Noether operator `B(E) = R_backgroundᵀ E`, expressed
algebraically as composition with the concrete diffeomorphism generator. -/
def scalarDiffeomorphismNoetherOperator
    (background : SmoothQuotientField period hPeriod Real)
    (euler : SmoothQuotientField period hPeriod Real →ₗ[Real] Real) :
    SmoothDiffeomorphismGhost period hPeriod →ₗ[Real] Real :=
  euler.comp (scalarDiffeomorphismGaugeGenerator period hPeriod background)

@[simp]
theorem scalarDiffeomorphismNoetherOperator_apply
    (background : SmoothQuotientField period hPeriod Real)
    (euler : SmoothQuotientField period hPeriod Real →ₗ[Real] Real)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    scalarDiffeomorphismNoetherOperator period hPeriod background euler ghost =
      euler (scalarLieDerivative period hPeriod ghost background) :=
  rfl

end

end P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
end JanusFormal
