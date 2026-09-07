import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricAbelianBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAbelianBRSTMetricChangeDefect4D

/-! # Exact smooth agreement of the variable-metric paired Abelian BRST action

Both physical potentials and all nonminimal fields are retained. The metric
in the completed Lorenz and FP expressions is the same varied metric used by
the original action. The integration measure is the canonical Lorentz volume.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricAbelianBRSTSameAction4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusVariableMetricC2FPSmoothAgreement4D
open P0EFTJanusVariableMetricC2LorenzFPL2Features4D
open P0EFTJanusVariableMetricAbelianBRSTAction4D
open P0EFTJanusAbelianBRSTMetricChangeDefect4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Smooth physical and nonminimal fields in the independent completed slots. -/
def smoothVariableMetricAbelianBRSTCore
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (nonminimal : GlobalAbelianNonminimalFields period hPeriod) :
    VariableMetricAbelianBRSTCore period hPeriod reference :=
  (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor,
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod reference potential),
      (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.nakanishiLautrup.field,
        (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.antighost.field,
          smoothAbelianGhostC2Core period hPeriod nonminimal.ghost.field))))

theorem smoothVariableMetricAbelianBRSTCore_mem_domain
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (nonminimal : GlobalAbelianNonminimalFields period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference) :
    smoothVariableMetricAbelianBRSTCore period hPeriod reference tensor potential nonminimal ∈
      variableMetricAbelianBRSTDomain period hPeriod reference :=
  ⟨hVariation, Set.mem_univ _⟩

theorem variableMetricAbelianBRSTAction_smooth_eq_coordinates
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (nonminimal : GlobalAbelianNonminimalFields period hPeriod) :
    variableMetricAbelianBRSTAction period hPeriod reference
        (smoothVariableMetricAbelianBRSTCore period hPeriod reference tensor potential nonminimal) =
      ∑ component : Fin 2,
        (inner Real
            (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.nakanishiLautrup.field component)
            (globalGaugeLieFieldL2Coordinates period hPeriod
              (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential) component) -
          (1 / 2 : Real) * inner Real
            (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.nakanishiLautrup.field component)
            (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.nakanishiLautrup.field component) +
          inner Real
            (globalGaugeLieFieldL2Coordinates period hPeriod nonminimal.antighost.field component)
            (globalGaugeLieFieldL2Coordinates period hPeriod
              (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric nonminimal.ghost.field)
              component)) := by
  simp only [variableMetricAbelianBRSTAction, variableMetricAbelianLorenzFeature,
    variableMetricAbelianFPFeature, smoothVariableMetricAbelianBRSTCore,
    variableMetricC2LorenzComponentL2_smooth period hPeriod reference tensor metric hMetric hVariation,
    regularFrameGaugePotentialFromCoefficients_frameCoefficients,
    variableMetricC2FPComponentL2_smooth period hPeriod reference tensor metric hMetric hVariation,
    globalGaugeLieFieldL2Coordinates, LinearMap.coe_mk, AddHom.coe_mk]

def smoothPairedVariableMetricAbelianBRSTCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    PairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase :=
  (smoothVariableMetricAbelianBRSTCore period hPeriod plusBase plusTensor
      (state.potential .plus) (state.nonminimal .plus),
    smoothVariableMetricAbelianBRSTCore period hPeriod minusBase minusTensor
      (state.potential .minus) (state.nonminimal .minus))

theorem smoothPairedVariableMetricAbelianBRSTCore_mem_domain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusBase)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusBase) :
    smoothPairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase
        plusTensor minusTensor state ∈
      pairedVariableMetricAbelianBRSTDomain period hPeriod plusBase minusBase :=
  ⟨smoothVariableMetricAbelianBRSTCore_mem_domain period hPeriod plusBase plusTensor
      _ _ hPlusVariation,
    smoothVariableMetricAbelianBRSTCore_mem_domain period hPeriod minusBase minusTensor
      _ _ hMinusVariation⟩

/-- SAME-ACTION for the entire paired Abelian sector with genuinely varied metrics. -/
theorem pairedVariableMetricAbelianBRSTAction_smooth_eq_BRST
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusBase.metric.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusBase.metric.tensor + minusTensor)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusBase)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusBase)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase
        (smoothPairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase
          plusTensor minusTensor state) =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  classical
  change variableMetricAbelianBRSTAction period hPeriod plusBase
      (smoothVariableMetricAbelianBRSTCore period hPeriod plusBase plusTensor
        (state.potential .plus) (state.nonminimal .plus)) +
    variableMetricAbelianBRSTAction period hPeriod minusBase
      (smoothVariableMetricAbelianBRSTCore period hPeriod minusBase minusTensor
        (state.potential .minus) (state.nonminimal .minus)) = _
  rw [variableMetricAbelianBRSTAction_smooth_eq_coordinates period hPeriod plusBase plusTensor
    (metric .plus) hPlusMetric hPlusVariation,
    variableMetricAbelianBRSTAction_smooth_eq_coordinates period hPeriod minusBase minusTensor
      (metric .minus) hMinusMetric hMinusVariation]
  have hAction := globalPairedAbelianGaugeFermionBRSTMixedAction_eq_offShell_inner
    period hPeriod metric state state
  change globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = _ at hAction
  rw [hAction]
  have hSectors : (Finset.univ : Finset Sector) = {.plus, .minus} := by decide
  simp only [PiLp.inner_apply, Fintype.sum_prod_type,
    globalPairedGaugeLieL2LinearMap, globalPairedAbelianLorenzL2LinearMap,
    globalPairedAbelianFPL2LinearMap, hSectors, Finset.sum_insert,
    Finset.sum_singleton, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The fixed-metric graph action requires the explicit metric-change correction. -/
theorem pairedVariableMetricAbelianBRSTAction_smooth_eq_graph_add_metricChange
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusBase.metric.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusBase.metric.tensor + minusTensor)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusBase)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusBase)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase
        (smoothPairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase
          plusTensor minusTensor state) =
      globalPairedAbelianOffShellGraphAction period hPeriod
          (fun | .plus => plusBase.metric | .minus => minusBase.metric)
          (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
            (fun | .plus => plusBase.metric | .minus => minusBase.metric) state) +
        globalPairedAbelianBRSTMetricChangeAction period hPeriod metric
          (fun | .plus => plusBase.metric | .minus => minusBase.metric) state := by
  rw [pairedVariableMetricAbelianBRSTAction_smooth_eq_BRST period hPeriod
    plusBase minusBase plusTensor minusTensor metric hPlusMetric hMinusMetric
      hPlusVariation hMinusVariation state,
    globalPairedAbelianOffShellGraphAction_smooth_eq_BRST,
    ← globalPairedAbelianGaugeFermionBRSTAction_sub_eq_metricChange]
  ring

end
end P0EFTJanusVariableMetricAbelianBRSTSameAction4D
end JanusFormal
