import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

/-! Exact action decomposition along the simultaneous three-slot LL curve. -/

namespace JanusFormal
namespace P0EFTJanusDifferentialLLFullCurveActionDecomposition4D

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
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
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

local instance effectiveThroatCompactSpace : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The genuine affine curve in all three LL slots of `IndependentFields`. -/
def differentialLLFullCurve
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (t : Real) : IndependentFields period hPeriod :=
  { fields with
    llAuxMetric := fields.llAuxMetric + t • dAux
    llMeasure := fields.llMeasure + t • dMeasure
    llField := fields.llField + t • dField }

/-- PT-averaged integral of precisely the kinetic summand. -/
def globalPTSymmetricDifferentialLLKineticAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    ((∫ point, differentialLLKineticDensity period hPeriod frame
        fields.llAuxMetric fields.llField point ∂mu) +
      ∫ point, differentialLLKineticDensity period hPeriod frame
        (llPTPullback period hPeriod fields).llAuxMetric
        (llPTPullback period hPeriod fields).llField point ∂mu)

/-- PT-averaged integral of the actual measure-times-flux worldvolume term. -/
def globalPTSymmetricLLWorldvolumeAction
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    ((∫ point, llWorldvolumeDensity period hPeriod fields point ∂mu) +
      ∫ point, llWorldvolumeDensity period hPeriod
        (llPTPullback period hPeriod fields) point ∂mu)

private theorem differentialLLKineticDensity_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (differentialLLKineticDensity period hPeriod frame
      fields.llAuxMetric fields.llField) mu := by
  have h := (differentialLLDensity_integrable period hPeriod frame fields mu).sub
      (llWorldvolumeDensity_integrable period hPeriod fields mu)
  apply h.congr
  filter_upwards [] with point
  unfold differentialLLDensity differentialLLKineticDensity
    llAuxiliaryKineticWeight
  simp only [Pi.sub_apply]
  ring

/-- Along the simultaneous field/auxiliary-metric/measure curve, the true
PT-symmetric action is exactly its integrated kinetic part plus its actual
worldvolume/measure part. -/
theorem globalPTSymmetricDifferentialLLAction_fullCurve_decomposition
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields dAux dMeasure dField t) mu =
      globalPTSymmetricDifferentialLLKineticAction period hPeriod frame
          (differentialLLFullCurve period hPeriod fields dAux dMeasure dField t) mu +
        globalPTSymmetricLLWorldvolumeAction period hPeriod
          (differentialLLFullCurve period hPeriod fields dAux dMeasure dField t) mu := by
  let curve := differentialLLFullCurve period hPeriod fields dAux dMeasure dField t
  have hRaw : globalDifferentialLLAction period hPeriod frame curve mu =
      (∫ point, differentialLLKineticDensity period hPeriod frame
        curve.llAuxMetric curve.llField point ∂mu) +
      ∫ point, llWorldvolumeDensity period hPeriod curve point ∂mu := by
    unfold globalDifferentialLLAction
    rw [← integral_add
      (differentialLLKineticDensity_integrable period hPeriod frame curve mu)
      (llWorldvolumeDensity_integrable period hPeriod curve mu)]
    congr 1
  have hPTRaw : globalDifferentialLLAction period hPeriod frame
      (llPTPullback period hPeriod curve) mu =
      (∫ point, differentialLLKineticDensity period hPeriod frame
        (llPTPullback period hPeriod curve).llAuxMetric
        (llPTPullback period hPeriod curve).llField point ∂mu) +
      ∫ point, llWorldvolumeDensity period hPeriod
        (llPTPullback period hPeriod curve) point ∂mu := by
    unfold globalDifferentialLLAction
    rw [← integral_add
      (differentialLLKineticDensity_integrable period hPeriod frame
        (llPTPullback period hPeriod curve) mu)
      (llWorldvolumeDensity_integrable period hPeriod
        (llPTPullback period hPeriod curve) mu)]
    congr 1
  unfold globalPTSymmetricDifferentialLLAction
    globalPTSymmetricDifferentialLLKineticAction
    globalPTSymmetricLLWorldvolumeAction
  rw [hRaw, hPTRaw]
  ring

end

end P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
end JanusFormal
