import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

/-! PT average of the exact simultaneous LL field/auxiliary kinetic polynomial. -/

namespace JanusFormal
namespace P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def ptSymmetricDifferentialLLKineticDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (differentialLLKineticDensity period hPeriod frame aux field point +
      differentialLLKineticDensity period hPeriod frame
        (throatPTPullback period hPeriod LLMetricFiber aux)
        (throatPTPullback period hPeriod LLFieldFiber field) point)

def ptSymmetricDifferentialLLKineticFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (differentialLLKineticFirstVariation period hPeriod frame aux field
        dAux dField point +
      differentialLLKineticFirstVariation period hPeriod frame
        (throatPTPullback period hPeriod LLMetricFiber aux)
        (throatPTPullback period hPeriod LLFieldFiber field)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (differentialLLFluxDirectionPT period hPeriod dField) point)

/-- Exact PT polynomial: the average of the two genuine orbit polynomials. -/
theorem ptSymmetricDifferentialLLKineticDensity_simultaneous_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (t : Real) (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticDensity period hPeriod frame
        (aux + t • dAux) (field + t • dField) point =
      (1 / 2 : Real) *
        ((1 / 2 : Real) *
          ((1 + ‖aux point‖ ^ 2) + t * (2 * inner Real (aux point) (dAux point)) +
              t ^ 2 * ‖dAux point‖ ^ 2) *
            (throatDerivativeEnergy period hPeriod frame field point +
              t * (2 * throatDerivativePairing period hPeriod frame field dField point) +
              t ^ 2 * throatDerivativeEnergy period hPeriod frame dField point) +
          (1 / 2 : Real) *
          ((1 + ‖throatPTPullback period hPeriod LLMetricFiber aux point‖ ^ 2) +
              t * (2 * inner Real
                (throatPTPullback period hPeriod LLMetricFiber aux point)
                (differentialLLAuxMetricDirectionPT period hPeriod dAux point)) +
              t ^ 2 * ‖differentialLLAuxMetricDirectionPT period hPeriod dAux point‖ ^ 2) *
            (throatDerivativeEnergy period hPeriod frame
                (throatPTPullback period hPeriod LLFieldFiber field) point +
              t * (2 * throatDerivativePairing period hPeriod frame
                (throatPTPullback period hPeriod LLFieldFiber field)
                (differentialLLFluxDirectionPT period hPeriod dField) point) +
              t ^ 2 * throatDerivativeEnergy period hPeriod frame
                (differentialLLFluxDirectionPT period hPeriod dField) point)) := by
  unfold ptSymmetricDifferentialLLKineticDensity
  rw [show throatPTPullback period hPeriod LLMetricFiber (aux + t • dAux) =
      throatPTPullback period hPeriod LLMetricFiber aux +
        t • differentialLLAuxMetricDirectionPT period hPeriod dAux by
      apply SmoothThroatField.ext period hPeriod LLMetricFiber; intro p; rfl]
  rw [show throatPTPullback period hPeriod LLFieldFiber (field + t • dField) =
      throatPTPullback period hPeriod LLFieldFiber field +
        t • differentialLLFluxDirectionPT period hPeriod dField by
      apply SmoothThroatField.ext period hPeriod LLFieldFiber; intro p; rfl]
  rw [differentialLLKineticDensity_simultaneous_polynomial,
    differentialLLKineticDensity_simultaneous_polynomial]

theorem ptSymmetricKineticFirstVariation_eq_linearCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame aux field
        dAux dField point =
      (1 / 2 : Real) *
        ((1 / 2 : Real) * ((1 + ‖aux point‖ ^ 2) *
          (2 * throatDerivativePairing period hPeriod frame field dField point) +
          (2 * inner Real (aux point) (dAux point)) *
            throatDerivativeEnergy period hPeriod frame field point) +
        (1 / 2 : Real) *
          ((1 + ‖throatPTPullback period hPeriod LLMetricFiber aux point‖ ^ 2) *
            (2 * throatDerivativePairing period hPeriod frame
              (throatPTPullback period hPeriod LLFieldFiber field)
              (differentialLLFluxDirectionPT period hPeriod dField) point) +
          (2 * inner Real (throatPTPullback period hPeriod LLMetricFiber aux point)
            (differentialLLAuxMetricDirectionPT period hPeriod dAux point)) *
            throatDerivativeEnergy period hPeriod frame
              (throatPTPullback period hPeriod LLFieldFiber field) point)) := by
  unfold ptSymmetricDifferentialLLKineticFirstVariation
  rw [differentialLLKineticFirstVariation_eq_linearCoefficient,
    differentialLLKineticFirstVariation_eq_linearCoefficient]

theorem ptSymmetricDifferentialLLKineticFirstVariation_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
      frame aux field dAux dField) := by
  have hRaw (a : SmoothThroatField period hPeriod LLMetricFiber)
      (f : SmoothThroatField period hPeriod LLFieldFiber)
      (da : SmoothThroatField period hPeriod LLMetricFiber)
      (df : SmoothThroatField period hPeriod LLFieldFiber) :
      Continuous (differentialLLKineticFirstVariation period hPeriod frame
        a f da df) := by
    unfold differentialLLKineticFirstVariation
    exact
      ((continuous_const.add (a.contMDiff_toFun.continuous.norm.pow 2)).mul
        (throatDerivativePairing_continuous period hPeriod frame f df)).add
      ((a.contMDiff_toFun.continuous.inner da.contMDiff_toFun.continuous).mul
        (throatDerivativeEnergy_continuous period hPeriod frame f))
  exact continuous_const.mul
    ((hRaw aux field dAux dField).add
      (hRaw (throatPTPullback period hPeriod LLMetricFiber aux)
        (throatPTPullback period hPeriod LLFieldFiber field)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (differentialLLFluxDirectionPT period hPeriod dField)))

theorem ptSymmetricDifferentialLLKineticFirstVariation_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
      frame aux field dAux dField) mu :=
  (ptSymmetricDifferentialLLKineticFirstVariation_continuous period hPeriod
    frame aux field dAux dField).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end
end P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
end JanusFormal
