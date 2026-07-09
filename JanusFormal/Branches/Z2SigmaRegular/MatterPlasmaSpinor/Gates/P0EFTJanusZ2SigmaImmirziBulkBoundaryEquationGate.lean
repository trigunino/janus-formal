import JanusFormal.Basic
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate

set_option autoImplicit false

structure ImmirziBulkBoundaryEquationGate where
  variationBibliographyChecked : Prop
  scalarImmirziHolstVariationImported : Prop
  niehYanVariationImported : Prop
  bulkEulerLagrangeSlotDeclared : Prop
  sigmaBoundaryTermDeclared : Prop
  torsionPullbackRequired : Prop
  torsionPullbackOnSigmaGateDeclared : Prop
  spinorSourceRequired : Prop
  observationalFitForbidden : Prop
  bulkImmirziEquationReduced : Prop
  sigmaBoundaryConditionReduced : Prop
  torsionPullbackReady : Prop
  spinorSourceReady : Prop
  immirziBulkBoundaryEquationReady : Prop

def immirziBulkBoundaryLedgerDeclared
    (g : ImmirziBulkBoundaryEquationGate) : Prop :=
  g.variationBibliographyChecked /\
  g.scalarImmirziHolstVariationImported /\
  g.niehYanVariationImported /\
  g.bulkEulerLagrangeSlotDeclared /\
  g.sigmaBoundaryTermDeclared /\
  g.torsionPullbackRequired /\
  g.torsionPullbackOnSigmaGateDeclared /\
  g.spinorSourceRequired /\
  g.observationalFitForbidden

def immirziBulkBoundaryEquationReady
    (g : ImmirziBulkBoundaryEquationGate) : Prop :=
  immirziBulkBoundaryLedgerDeclared g /\
  g.bulkImmirziEquationReduced /\
  g.sigmaBoundaryConditionReduced /\
  g.torsionPullbackReady /\
  g.spinorSourceReady /\
  g.immirziBulkBoundaryEquationReady

theorem immirzi_equation_requires_bulk_and_boundary_reduction
    (g : ImmirziBulkBoundaryEquationGate)
    (hReady : immirziBulkBoundaryEquationReady g) :
    g.bulkImmirziEquationReduced /\ g.sigmaBoundaryConditionReduced := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate
end JanusFormal
