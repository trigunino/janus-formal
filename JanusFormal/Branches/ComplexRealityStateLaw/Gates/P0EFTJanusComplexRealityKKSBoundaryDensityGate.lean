import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCoadjointStateSpaceGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityKKSBoundaryDensityGate

set_option autoImplicit false

structure KKSBoundaryDensityGate where
  coadjointStateSpaceReady : Prop
  finiteDimensionalKKSFormulaReady : Prop
  finiteDimensionalKKSNonzero : Prop
  sigmaBoundaryPhaseSpaceDeclared : Prop
  sigmaVariationsMappedToComplexLieAlgebra : Prop
  boundaryTwoCycleWithNonzeroPeriodDeclared : Prop
  densityOnSigmaNonzero : Prop
  alphaGenerated : Prop

def globalKKSOrbitNonzero (g : KKSBoundaryDensityGate) : Prop :=
  g.coadjointStateSpaceReady /\
  g.finiteDimensionalKKSFormulaReady /\
  g.finiteDimensionalKKSNonzero

def kksBoundaryDensityReady (g : KKSBoundaryDensityGate) : Prop :=
  globalKKSOrbitNonzero g /\
  g.sigmaBoundaryPhaseSpaceDeclared /\
  g.sigmaVariationsMappedToComplexLieAlgebra /\
  g.boundaryTwoCycleWithNonzeroPeriodDeclared /\
  g.densityOnSigmaNonzero

def alphaGeneratedByKKSBoundary (g : KKSBoundaryDensityGate) : Prop :=
  kksBoundaryDensityReady g /\ g.alphaGenerated

theorem finite_kks_nonzero_does_not_imply_sigma_density
    (g : KKSBoundaryDensityGate)
    (hMissing : Not g.boundaryTwoCycleWithNonzeroPeriodDeclared) :
    Not (kksBoundaryDensityReady g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusComplexRealityKKSBoundaryDensityGate
end JanusFormal
