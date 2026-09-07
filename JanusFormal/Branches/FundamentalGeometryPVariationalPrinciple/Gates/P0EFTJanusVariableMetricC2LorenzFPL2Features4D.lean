import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2FPSmoothAgreement4D

/-! # Variable-metric Lorenz and Faddeev--Popov features in physical L² -/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2LorenzFPL2Features4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D
open P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
open P0EFTJanusVariableMetricC2FPSmoothAgreement4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
private abbrev MetricC2Core (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod metric

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

def variableMetricC2LorenzComponentL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) (component : Fin 2) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  continuousToCanonicalPhysicalBulkL2 period hPeriod
    (variableMetricC2LorenzComponentExpression period hPeriod metric
      variation coefficients component)

theorem variableMetricC2LorenzComponentL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        variableMetricC2LorenzComponentL2 period hPeriod metric input.1 input.2 component)
      (variableMetricC2LorenzDomain period hPeriod metric) :=
  (continuousToCanonicalPhysicalBulkL2 period hPeriod).contDiff.comp_contDiffOn
    (variableMetricC2LorenzComponentExpression_contDiffOn period hPeriod metric component)

def variableMetricC2FPComponentL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (ghost : AbelianGhostC2Core period hPeriod) (component : Fin 2) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  continuousToCanonicalPhysicalBulkL2 period hPeriod
    (variableMetricC2FPComponentExpression period hPeriod metric variation ghost component)

theorem variableMetricC2FPComponentL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        variableMetricC2FPComponentL2 period hPeriod metric input.1 input.2 component)
      (variableMetricC2FPDomain period hPeriod metric) :=
  (continuousToCanonicalPhysicalBulkL2 period hPeriod).contDiff.comp_contDiffOn
    (variableMetricC2FPComponentExpression_contDiffOn period hPeriod metric component)

theorem variableMetricC2LorenzComponentL2_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) (component : Fin 2) :
    variableMetricC2LorenzComponentL2 period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) component =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
            (regularFrameGaugePotentialFromCoefficients period hPeriod reference coefficients))
          component) := by
  unfold variableMetricC2LorenzComponentL2
  rw [variableMetricC2LorenzComponentExpression_smooth period hPeriod reference tensor
    metric hMetric hVariation coefficients component,
    continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

theorem variableMetricC2FPComponentL2_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    variableMetricC2FPComponentL2 period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
        (smoothAbelianGhostC2Core period hPeriod ghost) component =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost) component) := by
  unfold variableMetricC2FPComponentL2
  rw [variableMetricC2FPComponentExpression_smooth period hPeriod reference tensor
    metric hMetric hVariation ghost component,
    continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

/-- Both components in the ordinary finite-product L² space. -/
def variableMetricC2LorenzL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    Fin 2 → CanonicalPhysicalBulkL2 period hPeriod :=
  variableMetricC2LorenzComponentL2 period hPeriod metric variation coefficients

def variableMetricC2FPL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod metric)
    (ghost : AbelianGhostC2Core period hPeriod) :
    Fin 2 → CanonicalPhysicalBulkL2 period hPeriod :=
  variableMetricC2FPComponentL2 period hPeriod metric variation ghost

theorem variableMetricC2LorenzL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        variableMetricC2LorenzL2 period hPeriod metric input.1 input.2)
      (variableMetricC2LorenzDomain period hPeriod metric) :=
  contDiffOn_pi.mpr (variableMetricC2LorenzComponentL2_contDiffOn period hPeriod metric)

theorem variableMetricC2FPL2_contDiffOn
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod metric × AbelianGhostC2Core period hPeriod =>
        variableMetricC2FPL2 period hPeriod metric input.1 input.2)
      (variableMetricC2FPDomain period hPeriod metric) :=
  contDiffOn_pi.mpr (variableMetricC2FPComponentL2_contDiffOn period hPeriod metric)

end
end P0EFTJanusVariableMetricC2LorenzFPL2Features4D
end JanusFormal
