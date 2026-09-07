import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2LorenzFPL2Features4D

/-! # The Abelian BRST action with a genuinely variable metric

Metric and potential coefficients, the auxiliary B field, the antighost,
and the ghost are independent coordinates.  The action retains both
metric-dependent Lorenz and Faddeev--Popov features and the negative
auxiliary square of the original BRST density.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricAbelianBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D
open P0EFTJanusVariableMetricC2LorenzFPL2Features4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev ScalarL2 := CanonicalPhysicalBulkL2 period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Coordinates are metric, potential, B, antighost, ghost, in that order. -/
abbrev VariableMetricAbelianBRSTCore
    (reference : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod reference ×
    (RegularGeneralMetricC2GaugeCoefficientCore period hPeriod ×
      ((Fin 2 → ScalarL2 period hPeriod) ×
        ((Fin 2 → ScalarL2 period hPeriod) × AbelianGhostC2Core period hPeriod)))

def variableMetricAbelianBRSTDomain
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    Set (VariableMetricAbelianBRSTCore period hPeriod reference) :=
  regularGeneralMetricC2Domain period hPeriod reference ×ˢ univ

theorem variableMetricAbelianBRSTDomain_isOpen
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (variableMetricAbelianBRSTDomain period hPeriod reference) :=
  (regularGeneralMetricC2Domain_isOpen period hPeriod reference).prod isOpen_univ

def variableMetricAbelianLorenzFeature
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) (input : VariableMetricAbelianBRSTCore period hPeriod reference) :
    ScalarL2 period hPeriod :=
  variableMetricC2LorenzComponentL2 period hPeriod reference input.1 input.2.1 component

def variableMetricAbelianFPFeature
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) (input : VariableMetricAbelianBRSTCore period hPeriod reference) :
    ScalarL2 period hPeriod :=
  variableMetricC2FPComponentL2 period hPeriod reference input.1 input.2.2.2.2 component

theorem variableMetricAbelianLorenzFeature_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞ (variableMetricAbelianLorenzFeature period hPeriod reference component)
      (variableMetricAbelianBRSTDomain period hPeriod reference) := by
  have hProjection : ContDiffOn Real ∞
      (fun input : VariableMetricAbelianBRSTCore period hPeriod reference =>
        (input.1, input.2.1))
      (variableMetricAbelianBRSTDomain period hPeriod reference) :=
    (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
  have hComposition :=
    (variableMetricC2LorenzComponentL2_contDiffOn period hPeriod reference component).comp
      hProjection (fun _ hInput => ⟨hInput.1, Set.mem_univ _⟩)
  exact hComposition

theorem variableMetricAbelianFPFeature_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    ContDiffOn Real ∞ (variableMetricAbelianFPFeature period hPeriod reference component)
      (variableMetricAbelianBRSTDomain period hPeriod reference) := by
  have hProjection : ContDiffOn Real ∞
      (fun input : VariableMetricAbelianBRSTCore period hPeriod reference =>
        (input.1, input.2.2.2.2))
      (variableMetricAbelianBRSTDomain period hPeriod reference) :=
    (contDiff_fst.prodMk contDiff_snd.snd.snd.snd).contDiffOn
  have hComposition :=
    (variableMetricC2FPComponentL2_contDiffOn period hPeriod reference component).comp
      hProjection (fun _ hInput => ⟨hInput.1, Set.mem_univ _⟩)
  exact hComposition

/-- The three genuine BRST terms, with every nonminimal slot independent. -/
def variableMetricAbelianBRSTAction
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricAbelianBRSTCore period hPeriod reference) : Real :=
  ∑ component : Fin 2,
    (inner Real (input.2.2.1 component)
        (variableMetricAbelianLorenzFeature period hPeriod reference component input) -
      (1 / 2 : Real) * inner Real (input.2.2.1 component) (input.2.2.1 component) +
      inner Real (input.2.2.2.1 component)
        (variableMetricAbelianFPFeature period hPeriod reference component input))

theorem variableMetricAbelianBRSTAction_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞ (variableMetricAbelianBRSTAction period hPeriod reference)
      (variableMetricAbelianBRSTDomain period hPeriod reference) := by
  have hB (component : Fin 2) : ContDiff Real ∞
      (fun input : VariableMetricAbelianBRSTCore period hPeriod reference =>
        input.2.2.1 component) :=
    (ContinuousLinearMap.proj component :
      (Fin 2 → ScalarL2 period hPeriod) →L[Real] ScalarL2 period hPeriod).contDiff.comp
      contDiff_snd.snd.fst
  have hAntighost (component : Fin 2) : ContDiff Real ∞
      (fun input : VariableMetricAbelianBRSTCore period hPeriod reference =>
        input.2.2.2.1 component) :=
    (ContinuousLinearMap.proj component :
      (Fin 2 → ScalarL2 period hPeriod) →L[Real] ScalarL2 period hPeriod).contDiff.comp
      contDiff_snd.snd.snd.fst
  unfold variableMetricAbelianBRSTAction
  apply ContDiffOn.sum
  intro component _
  exact (((hB component).contDiffOn.inner Real
      (variableMetricAbelianLorenzFeature_contDiffOn period hPeriod reference component)).sub
        (contDiffOn_const.mul
          ((hB component).contDiffOn.inner Real (hB component).contDiffOn))).add
    ((hAntighost component).contDiffOn.inner Real
      (variableMetricAbelianFPFeature_contDiffOn period hPeriod reference component))

theorem variableMetricAbelianBRSTAction_hasFDerivAt
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (input : VariableMetricAbelianBRSTCore period hPeriod reference)
    (hInput : input ∈ variableMetricAbelianBRSTDomain period hPeriod reference) :
    HasFDerivAt (variableMetricAbelianBRSTAction period hPeriod reference)
      (fderiv Real (variableMetricAbelianBRSTAction period hPeriod reference) input) input :=
  ((variableMetricAbelianBRSTAction_contDiffOn period hPeriod reference input hInput).contDiffAt
    ((variableMetricAbelianBRSTDomain_isOpen period hPeriod reference).mem_nhds hInput)
      ).differentiableAt (by simp) |>.hasFDerivAt

abbrev PairedVariableMetricAbelianBRSTCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  VariableMetricAbelianBRSTCore period hPeriod plusBase ×
    VariableMetricAbelianBRSTCore period hPeriod minusBase

def pairedVariableMetricAbelianBRSTDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (PairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase) :=
  variableMetricAbelianBRSTDomain period hPeriod plusBase ×ˢ
    variableMetricAbelianBRSTDomain period hPeriod minusBase

theorem pairedVariableMetricAbelianBRSTDomain_isOpen
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (pairedVariableMetricAbelianBRSTDomain period hPeriod plusBase minusBase) :=
  (variableMetricAbelianBRSTDomain_isOpen period hPeriod plusBase).prod
    (variableMetricAbelianBRSTDomain_isOpen period hPeriod minusBase)

def pairedVariableMetricAbelianBRSTAction
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (input : PairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase) : Real :=
  variableMetricAbelianBRSTAction period hPeriod plusBase input.1 +
    variableMetricAbelianBRSTAction period hPeriod minusBase input.2

theorem pairedVariableMetricAbelianBRSTAction_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞ (pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase)
      (pairedVariableMetricAbelianBRSTDomain period hPeriod plusBase minusBase) :=
  ((variableMetricAbelianBRSTAction_contDiffOn period hPeriod plusBase).comp
    contDiff_fst.contDiffOn (fun _ hInput => hInput.1)).add
      ((variableMetricAbelianBRSTAction_contDiffOn period hPeriod minusBase).comp
        contDiff_snd.contDiffOn (fun _ hInput => hInput.2))

end
end P0EFTJanusVariableMetricAbelianBRSTAction4D
end JanusFormal
