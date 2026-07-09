namespace JanusFormal
namespace P0EFTJanusZ2SigmaTorsionSourceExhaustionGate

set_option autoImplicit false

structure SigmaTorsionSourceExhaustionGate where
  spinCurrentOnSigma : Prop
  nonzeroNiehYanCharge : Prop
  torsionfulBoundaryCondition : Prop
  singularDefectSource : Prop

def torsionSourceOnSigma (g : SigmaTorsionSourceExhaustionGate) : Prop :=
  g.spinCurrentOnSigma \/
  g.nonzeroNiehYanCharge \/
  g.torsionfulBoundaryCondition \/
  g.singularDefectSource

def openTorsionfulHolstNiehYanSigma (g : SigmaTorsionSourceExhaustionGate) : Prop :=
  torsionSourceOnSigma g

def archiveTorsionfulBranchRecommended (g : SigmaTorsionSourceExhaustionGate) : Prop :=
  Not (torsionSourceOnSigma g)

theorem no_source_blocks_torsionful_branch
    (g : SigmaTorsionSourceExhaustionGate)
    (hSpin : Not g.spinCurrentOnSigma)
    (hNY : Not g.nonzeroNiehYanCharge)
    (hBC : Not g.torsionfulBoundaryCondition)
    (hDefect : Not g.singularDefectSource) :
    archiveTorsionfulBranchRecommended g := by
  intro h
  rcases h with h | h | h | h
  · exact hSpin h
  · exact hNY h
  · exact hBC h
  · exact hDefect h

theorem any_source_opens_torsionful_branch
    (g : SigmaTorsionSourceExhaustionGate)
    (h : torsionSourceOnSigma g) :
    openTorsionfulHolstNiehYanSigma g := h

end P0EFTJanusZ2SigmaTorsionSourceExhaustionGate
end JanusFormal
