namespace JanusFormal
namespace P0EFTJanusZ4LinearizedEquation

set_option autoImplicit false

structure UnifiedZ4LinearizedEquation where
  masterEquationEncoded : Prop
  projectionOperatorNormalized : Prop
  projectedSectorEquations : Prop
  noIndependentMetricForces : Prop
  bianchiProjectionClosed : Prop
  explicitTensorOperatorDerived : Prop

def z4ProjectionScaffoldReady (e : UnifiedZ4LinearizedEquation) : Prop :=
  e.masterEquationEncoded /\
  e.projectionOperatorNormalized /\
  e.projectedSectorEquations /\
  e.noIndependentMetricForces /\
  e.bianchiProjectionClosed

def fullTensorDerivationReady (e : UnifiedZ4LinearizedEquation) : Prop :=
  z4ProjectionScaffoldReady e /\
  e.explicitTensorOperatorDerived

theorem projected_sectors_descend_from_unified_z4
    (e : UnifiedZ4LinearizedEquation)
    (h : z4ProjectionScaffoldReady e) :
    e.masterEquationEncoded /\
    e.projectedSectorEquations /\
    e.noIndependentMetricForces := by
  exact ⟨h.left, h.right.right.left, h.right.right.right.left⟩

theorem scaffold_does_not_imply_full_tensor_derivation
    (e : UnifiedZ4LinearizedEquation)
    (_h : z4ProjectionScaffoldReady e)
    (hMissing : Not e.explicitTensorOperatorDerived) :
    Not (fullTensorDerivationReady e) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4LinearizedEquation
end JanusFormal
