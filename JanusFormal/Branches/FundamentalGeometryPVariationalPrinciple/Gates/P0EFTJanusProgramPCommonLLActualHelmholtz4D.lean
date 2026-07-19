import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusProgramPCommonLLActualHelmholtz4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusProgramPCommonLLActionVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The nonlinear Helmholtz condition for the actual LL Euler functional:
at every background, its derivative along the common Program-P variation
space is symmetric in the two LL directions. -/
def LLActualHelmholtzCondition : Prop :=
  ∀ (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu],
    deriv (fun parameter : Real =>
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (llFluxIndependentVariation period hPeriod first) parameter)
        second mu) 0 =
    deriv (fun parameter : Real =>
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (llFluxIndependentVariation period hPeriod second) parameter)
        first mu) 0

/-- The LL block satisfies Helmholtz because both derivatives are genuine
mixed second variations of the same unchanged PT-averaged action. -/
theorem ll_actual_helmholtz_condition :
    LLActualHelmholtzCondition period hPeriod := by
  intro frame fields first second mu _
  rw [(globalPTSymmetricDifferentialLLFirstVariation_independentFieldCurve_hasDerivAt
      period hPeriod frame fields first second mu).deriv,
    (globalPTSymmetricDifferentialLLFirstVariation_independentFieldCurve_hasDerivAt
      period hPeriod frame fields second first mu).deriv]
  exact globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod frame
    fields first second mu

end

end P0EFTJanusProgramPCommonLLActualHelmholtz4D
end JanusFormal
