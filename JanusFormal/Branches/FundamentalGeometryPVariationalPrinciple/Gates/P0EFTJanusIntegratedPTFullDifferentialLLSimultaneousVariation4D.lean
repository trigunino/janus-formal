import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLMeasureFieldTwoParameterRawAction4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D

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
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def llVariationPT (variation : LLVariation period hPeriod) : LLVariation period hPeriod where
  measureDirection := throatPTPullback period hPeriod Real variation.measureDirection
  fieldDirection := differentialLLFluxDirectionPT period hPeriod variation.fieldDirection

def globalPTLLWorldvolumeAction (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) * (globalLLAction period hPeriod fields mu +
    globalLLAction period hPeriod (llPTPullback period hPeriod fields) mu)

def globalPTFullDifferentialLLAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTDifferentialLLKineticAction period hPeriod frame fields.llAuxMetric
      fields.llField mu + globalPTLLWorldvolumeAction period hPeriod fields mu

def fullLLCurve (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (t : Real) :
    IndependentFields period hPeriod :=
  { fields with
    llMeasure := fields.llMeasure + t • variation.measureDirection
    llField := fields.llField + t • variation.fieldDirection
    llAuxMetric := fields.llAuxMetric + t • dAux }

private theorem llPTPullback_fullLLCurve (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (t : Real) :
    llPTPullback period hPeriod (fullLLCurve period hPeriod fields variation dAux t) =
      fullLLCurve period hPeriod (llPTPullback period hPeriod fields)
        (llVariationPT period hPeriod variation)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux) t := by
  cases fields
  apply IndependentFields.ext <;> rfl

theorem globalPTFullDifferentialLLAction_simultaneous_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTFullDifferentialLLAction period hPeriod frame
      (fullLLCurve period hPeriod fields variation dAux t) mu)
      ((∫ p, P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
        period hPeriod frame fields.llAuxMetric fields.llField dAux
          variation.fieldDirection p ∂mu) +
       (1 / 2 : Real) * (globalLLFirstVariation period hPeriod fields variation mu +
         globalLLFirstVariation period hPeriod (llPTPullback period hPeriod fields)
           (llVariationPT period hPeriod variation) mu)) 0 := by
  have hk := globalPTDifferentialLLKineticAction_simultaneous_hasDerivAt
    period hPeriod frame fields.llAuxMetric dAux fields.llField
      variation.fieldDirection mu
  have hw0 := globalLLAction_affine_hasDerivAt period hPeriod fields variation mu
  have hw1 := globalLLAction_affine_hasDerivAt period hPeriod
    (llPTPullback period hPeriod fields) (llVariationPT period hPeriod variation) mu
  have hw := (hw0.add hw1).const_mul (1 / 2 : Real)
  have hFunction :
      (fun t : Real => globalPTFullDifferentialLLAction period hPeriod frame
        (fullLLCurve period hPeriod fields variation dAux t) mu) =
      (fun t : Real =>
        globalPTDifferentialLLKineticAction period hPeriod frame
          (fields.llAuxMetric + t • dAux)
          (fields.llField + t • variation.fieldDirection) mu +
        (1 / 2 : Real) *
          (globalLLAction period hPeriod
              (llAffineCurve period hPeriod fields variation t) mu +
            globalLLAction period hPeriod
              (llAffineCurve period hPeriod (llPTPullback period hPeriod fields)
                (llVariationPT period hPeriod variation) t) mu)) := by
    funext t
    unfold globalPTFullDifferentialLLAction globalPTLLWorldvolumeAction
    rw [llPTPullback_fullLLCurve period hPeriod fields variation dAux t]
    rfl
  rw [hFunction]
  exact hk.add hw

end
end P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
end JanusFormal
