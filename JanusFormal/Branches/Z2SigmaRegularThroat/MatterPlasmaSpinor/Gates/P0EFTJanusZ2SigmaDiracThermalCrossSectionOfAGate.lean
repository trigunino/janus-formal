import JanusFormal.Basic
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaDiracHolstVertexOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate

set_option autoImplicit false

structure DiracThermalCrossSectionOfAGate where
  crossSectionBibliographyChecked : Prop
  thermalAverageSigmaVImported : Prop
  gondoloGelminiRelativisticAverageImported : Prop
  plusMatrixElementDeclared : Prop
  minusMatrixElementDeclared : Prop
  diracHolstVertexGateDeclared : Prop
  plusPhaseSpaceMeasureDeclared : Prop
  minusPhaseSpaceMeasureDeclared : Prop
  massTemperatureLawRequired : Prop
  z2SigmaProjectionRequired : Prop
  observationalFitForbidden : Prop
  plusMatrixElementReady : Prop
  minusMatrixElementReady : Prop
  plusPhaseSpaceMeasureReady : Prop
  minusPhaseSpaceMeasureReady : Prop
  plusThermalCrossSectionOfAReady : Prop
  minusThermalCrossSectionOfAReady : Prop
  projectedThermalCrossSectionOfAReady : Prop
  diracThermalCrossSectionOfAReady : Prop

def diracThermalCrossSectionLedgerDeclared
    (g : DiracThermalCrossSectionOfAGate) : Prop :=
  g.crossSectionBibliographyChecked /\
  g.thermalAverageSigmaVImported /\
  g.gondoloGelminiRelativisticAverageImported /\
  g.plusMatrixElementDeclared /\
  g.minusMatrixElementDeclared /\
  g.diracHolstVertexGateDeclared /\
  g.plusPhaseSpaceMeasureDeclared /\
  g.minusPhaseSpaceMeasureDeclared /\
  g.massTemperatureLawRequired /\
  g.z2SigmaProjectionRequired /\
  g.observationalFitForbidden

def diracThermalCrossSectionReady
    (g : DiracThermalCrossSectionOfAGate) : Prop :=
  diracThermalCrossSectionLedgerDeclared g /\
  g.plusMatrixElementReady /\
  g.minusMatrixElementReady /\
  g.plusPhaseSpaceMeasureReady /\
  g.minusPhaseSpaceMeasureReady /\
  g.plusThermalCrossSectionOfAReady /\
  g.minusThermalCrossSectionOfAReady /\
  g.projectedThermalCrossSectionOfAReady /\
  g.diracThermalCrossSectionOfAReady

theorem cross_section_requires_amplitudes_and_phase_space
    (g : DiracThermalCrossSectionOfAGate)
    (hReady : diracThermalCrossSectionReady g) :
    g.plusMatrixElementReady /\ g.minusMatrixElementReady /\
      g.plusPhaseSpaceMeasureReady /\ g.minusPhaseSpaceMeasureReady := by
  exact And.intro hReady.2.1
    (And.intro hReady.2.2.1
      (And.intro hReady.2.2.2.1 hReady.2.2.2.2.1))

end P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate
end JanusFormal
