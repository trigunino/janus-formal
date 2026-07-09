namespace JanusFormal
namespace P0EFTJanusComplexRealitySourceFormulaCurationGate

set_option autoImplicit false

structure SourceFormulaCurationGate where
  hermiteMetricCurated : Prop
  complexPoincareGroupCurated : Prop
  lieAlgebraActionCurated : Prop
  momentSpaceCurated : Prop
  souriauPairingCurated : Prop
  coadjointActionCurated : Prop
  massSignSliceCurated : Prop
  alphaFixedBySource : Prop

def formulaCurationReady (g : SourceFormulaCurationGate) : Prop :=
  g.hermiteMetricCurated /\
  g.complexPoincareGroupCurated /\
  g.lieAlgebraActionCurated /\
  g.momentSpaceCurated /\
  g.souriauPairingCurated /\
  g.coadjointActionCurated /\
  g.massSignSliceCurated /\
  Not g.alphaFixedBySource

theorem source_curation_does_not_fix_alpha
    (g : SourceFormulaCurationGate)
    (h : formulaCurationReady g) :
    Not g.alphaFixedBySource := by
  rcases h with ⟨_, _, _, _, _, _, _, hNoAlpha⟩
  exact hNoAlpha

end P0EFTJanusComplexRealitySourceFormulaCurationGate
end JanusFormal
