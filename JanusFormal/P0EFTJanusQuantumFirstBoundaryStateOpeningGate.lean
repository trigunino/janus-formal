namespace JanusFormal
namespace P0EFTJanusQuantumFirstBoundaryStateOpeningGate

set_option autoImplicit false

structure QuantumFirstBoundaryStateOpeningGate where
  boundaryStatePostulateDeclared : Prop
  geometryDerivedAfterQuantization : Prop
  cp1RouteAllowed : Prop
  tqftRouteAllowed : Prop
  alphaFitForbidden : Prop
  classicalJanusLimitRequired : Prop

def quantumFirstProgramOpen (g : QuantumFirstBoundaryStateOpeningGate) : Prop :=
  g.boundaryStatePostulateDeclared /\
  g.geometryDerivedAfterQuantization /\
  g.cp1RouteAllowed /\
  g.tqftRouteAllowed /\
  g.alphaFitForbidden /\
  g.classicalJanusLimitRequired

end P0EFTJanusQuantumFirstBoundaryStateOpeningGate
end JanusFormal
