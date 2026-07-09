namespace JanusFormal
namespace P0EFTJanusZ4NeutrinoFreeStreamingClosure

set_option autoImplicit false

structure NeutrinoFreeStreamingClosure where
  collisionlessHierarchyRecursionDeclared : Prop
  freeStreamingResidualVanishes : Prop
  finiteHierarchyTargetDeclared : Prop
  quadrupoleFeedsAnisotropicStress : Prop
  z4MetricSourceInputsExplicit : Prop
  physicalBoltzmannIntegratorImplemented : Prop
  planckLikelihoodReady : Prop

def neutrinoFreeStreamingClosureReady (n : NeutrinoFreeStreamingClosure) : Prop :=
  n.collisionlessHierarchyRecursionDeclared /\
  n.freeStreamingResidualVanishes /\
  n.finiteHierarchyTargetDeclared /\
  n.quadrupoleFeedsAnisotropicStress /\
  n.z4MetricSourceInputsExplicit

def neutrinoBoltzmannReady (n : NeutrinoFreeStreamingClosure) : Prop :=
  neutrinoFreeStreamingClosureReady n /\
  n.physicalBoltzmannIntegratorImplemented

def neutrinoPlanckReady (n : NeutrinoFreeStreamingClosure) : Prop :=
  neutrinoBoltzmannReady n /\
  n.planckLikelihoodReady

theorem free_streaming_closure_has_zero_residual
    (n : NeutrinoFreeStreamingClosure)
    (h : neutrinoFreeStreamingClosureReady n) :
    n.freeStreamingResidualVanishes := by
  exact h.right.left

theorem free_streaming_closure_does_not_imply_boltzmann_readiness
    (n : NeutrinoFreeStreamingClosure)
    (_h : neutrinoFreeStreamingClosureReady n)
    (hMissing : Not n.physicalBoltzmannIntegratorImplemented) :
    Not (neutrinoBoltzmannReady n) := by
  intro h
  exact hMissing h.right

theorem free_streaming_closure_does_not_imply_planck_readiness
    (n : NeutrinoFreeStreamingClosure)
    (_h : neutrinoFreeStreamingClosureReady n)
    (hMissing : Not n.physicalBoltzmannIntegratorImplemented) :
    Not (neutrinoPlanckReady n) := by
  intro h
  exact hMissing h.left.right

end P0EFTJanusZ4NeutrinoFreeStreamingClosure
end JanusFormal
