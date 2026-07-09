import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaGrowthPerturbationEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaGrowthPredictionVectorGate

set_option autoImplicit false

structure Z2SigmaGrowthPredictionVectorGate where
  growthPerturbationEquationsDerived : Prop
  numericalHZ2SigmaReady : Prop
  numericalOmegaMZ2SigmaReady : Prop
  numericalMuZ2SigmaReady : Prop
  numericalSlipZ2SigmaReady : Prop
  numericalFrictionZ2SigmaReady : Prop
  initialConditionPolicyDeclared : Prop
  sigma8NormalizationPolicyDeclared : Prop
  archivedHolstGrowthSolverReuseForbidden : Prop
  archivedZ4GrowthSolverReuseForbidden : Prop
  z2SigmaGrowthPredictionVectorReady : Prop

def growthPredictionVectorPrerequisites
    (g : Z2SigmaGrowthPredictionVectorGate) : Prop :=
  g.growthPerturbationEquationsDerived /\
  g.numericalHZ2SigmaReady /\
  g.numericalOmegaMZ2SigmaReady /\
  g.numericalMuZ2SigmaReady /\
  g.numericalSlipZ2SigmaReady /\
  g.numericalFrictionZ2SigmaReady /\
  g.initialConditionPolicyDeclared /\
  g.sigma8NormalizationPolicyDeclared /\
  g.archivedHolstGrowthSolverReuseForbidden /\
  g.archivedZ4GrowthSolverReuseForbidden

theorem growth_prediction_vector_requires_numeric_closure
    (g : Z2SigmaGrowthPredictionVectorGate)
    (hReady : g.z2SigmaGrowthPredictionVectorReady)
    (hImplies :
      g.z2SigmaGrowthPredictionVectorReady -> growthPredictionVectorPrerequisites g) :
    growthPredictionVectorPrerequisites g := by
  exact hImplies hReady

end P0EFTJanusZ2SigmaGrowthPredictionVectorGate
end JanusFormal
