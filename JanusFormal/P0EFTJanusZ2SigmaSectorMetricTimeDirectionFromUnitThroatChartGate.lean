namespace JanusFormal
namespace P0EFTJanusZ2SigmaSectorMetricTimeDirectionFromUnitThroatChartGate

set_option autoImplicit false

structure SectorMetricTimeDirectionFromUnitThroatChartGate where
  unitIntrinsicMetricReady : Prop
  activeAGridReady : Prop
  unitThroatChartDeclared : Prop
  metricFormulaDeclared : Prop
  timeDirectionFormulaDeclared : Prop
  sectorMetricOnSigmaWritten : Prop
  sectorTimeDirectionOnSigmaWritten : Prop

def sectorMetricTimeDirectionReady
    (g : SectorMetricTimeDirectionFromUnitThroatChartGate) : Prop :=
  g.unitIntrinsicMetricReady /\
  g.activeAGridReady /\
  g.unitThroatChartDeclared /\
  g.metricFormulaDeclared /\
  g.timeDirectionFormulaDeclared /\
  g.sectorMetricOnSigmaWritten /\
  g.sectorTimeDirectionOnSigmaWritten

theorem metric_time_direction_requires_q_and_grid
    (g : SectorMetricTimeDirectionFromUnitThroatChartGate)
    (h : sectorMetricTimeDirectionReady g) :
    g.unitIntrinsicMetricReady /\ g.activeAGridReady := by
  exact And.intro h.1 h.2.1

end P0EFTJanusZ2SigmaSectorMetricTimeDirectionFromUnitThroatChartGate
end JanusFormal
