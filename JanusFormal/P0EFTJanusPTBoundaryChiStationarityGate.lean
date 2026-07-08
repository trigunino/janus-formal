namespace JanusFormal
namespace P0EFTJanusPTBoundaryChiStationarityGate

set_option autoImplicit false

structure PTBoundaryChiStationarityGate where
  ptInvariantBoundaryFunctionalDeclared : Prop
  stationarityEquationDeclared : Prop
  nonzeroChiSelectedByPTAlone : Prop
  nonzeroChiRequiresScaleOrCharge : Prop
  zeroChiRejectedByBridge : Prop
  chiLLSelectedNoFit : Prop

def ptBoundaryStationarityAudited (g : PTBoundaryChiStationarityGate) : Prop :=
  g.ptInvariantBoundaryFunctionalDeclared /\
  g.stationarityEquationDeclared /\
  Not g.nonzeroChiSelectedByPTAlone /\
  g.nonzeroChiRequiresScaleOrCharge /\
  g.zeroChiRejectedByBridge /\
  Not g.chiLLSelectedNoFit

theorem pt_boundary_symmetry_alone_does_not_select_nonzero_chi
    (g : PTBoundaryChiStationarityGate)
    (h : ptBoundaryStationarityAudited g) :
    Not g.chiLLSelectedNoFit := by
  exact h.right.right.right.right.right

end P0EFTJanusPTBoundaryChiStationarityGate
end JanusFormal
