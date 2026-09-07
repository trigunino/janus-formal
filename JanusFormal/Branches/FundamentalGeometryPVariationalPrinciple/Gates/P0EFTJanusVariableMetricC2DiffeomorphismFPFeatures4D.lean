import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2CartanFirstJet4D

/-! # Diffeomorphism Faddeev--Popov on the mobile C² metric chart

De Donder acts on the first jet of the Cartan tensor. Only second spatial
jets of the metric and the vector ghost enter this completed expression.
Its intrinsic smooth agreement is supplied separately.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusVariableMetricDeDonderFirstJet4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev MetricC2Core (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod metric
private abbrev GhostC2 := DiffeomorphismGhostC2Coefficients period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  inferInstance

def variableMetricC2DiffeomorphismFPDomain
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    Set (MetricC2Core period hPeriod reference × GhostC2 period hPeriod) :=
  regularGeneralMetricC2Domain period hPeriod reference ×ˢ univ

theorem variableMetricC2DiffeomorphismFPDomain_isOpen
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (variableMetricC2DiffeomorphismFPDomain period hPeriod reference) :=
  (regularGeneralMetricC2Domain_isOpen period hPeriod reference).prod isOpen_univ

def variableMetricC2DiffeomorphismFPComponentExpression
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : GhostC2 period hPeriod) (component : Fin 4) :
    C(EffectiveQuotient period hPeriod, Real) :=
  variableMetricDeDonderFirstJetComponentExpression period hPeriod reference variation
    (variableMetricC2CartanFirstJet period hPeriod reference variation ghost) component

theorem variableMetricC2DiffeomorphismFPComponentExpression_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod reference × GhostC2 period hPeriod =>
        variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
          input.1 input.2 component)
      (variableMetricC2DiffeomorphismFPDomain period hPeriod reference) := by
  have hJet := contDiff_fst.prodMk
    (variableMetricC2CartanFirstJet_contDiff period hPeriod reference)
  have hProjection : ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod reference × GhostC2 period hPeriod =>
        (input.1, variableMetricC2CartanFirstJet period hPeriod reference input.1 input.2))
      (variableMetricC2DiffeomorphismFPDomain period hPeriod reference) := hJet.contDiffOn
  have h := (variableMetricDeDonderFirstJetComponentExpression_contDiffOn
    period hPeriod reference component).comp hProjection (fun _ h => ⟨h.1, mem_univ _⟩)
  simp only [Function.comp_def] at h
  dsimp only [variableMetricC2DiffeomorphismFPComponentExpression]
  exact h

def variableMetricC2DiffeomorphismFPComponentL2
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : GhostC2 period hPeriod) (component : Fin 4) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  continuousToCanonicalPhysicalBulkL2 period hPeriod
    (variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
      variation ghost component)

theorem variableMetricC2DiffeomorphismFPComponentL2_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) (component : Fin 4) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod reference × GhostC2 period hPeriod =>
        variableMetricC2DiffeomorphismFPComponentL2 period hPeriod reference
          input.1 input.2 component)
      (variableMetricC2DiffeomorphismFPDomain period hPeriod reference) := by
  have h := (continuousToCanonicalPhysicalBulkL2 period hPeriod).contDiff.comp_contDiffOn
    (variableMetricC2DiffeomorphismFPComponentExpression_contDiffOn
      period hPeriod reference component)
  exact h

def variableMetricC2DiffeomorphismFPL2
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricC2Core period hPeriod reference)
    (ghost : GhostC2 period hPeriod) : Fin 4 → CanonicalPhysicalBulkL2 period hPeriod :=
  variableMetricC2DiffeomorphismFPComponentL2 period hPeriod reference variation ghost

theorem variableMetricC2DiffeomorphismFPL2_contDiffOn
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (fun input : MetricC2Core period hPeriod reference × GhostC2 period hPeriod =>
        variableMetricC2DiffeomorphismFPL2 period hPeriod reference input.1 input.2)
      (variableMetricC2DiffeomorphismFPDomain period hPeriod reference) :=
  contDiffOn_pi.mpr
    (variableMetricC2DiffeomorphismFPComponentL2_contDiffOn period hPeriod reference)

end
end P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
end JanusFormal
