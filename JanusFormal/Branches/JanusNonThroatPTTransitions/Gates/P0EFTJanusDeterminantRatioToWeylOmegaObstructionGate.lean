namespace JanusFormal
namespace P0EFTJanusDeterminantRatioToWeylOmegaObstructionGate

set_option autoImplicit false

structure DeterminantRatioToWeylOmegaObstructionGate where
  JanusDeterminantRatioAvailable : Prop
  FLRWVolumeRatioFormulaDeclared : Prop
  ConformalCaseRelationDeclared : Prop
  DeterminantRatioFixesVolumeScale : Prop
  DeterminantRatioFixesFullMetricConformalFactor : Prop
  NearPTConformalityProved : Prop
  UniqueOmegaFromRatioDerived : Prop

def DeterminantRatioOmegaClosed
    (g : DeterminantRatioToWeylOmegaObstructionGate) : Prop :=
  g.JanusDeterminantRatioAvailable /\
  g.FLRWVolumeRatioFormulaDeclared /\
  g.ConformalCaseRelationDeclared /\
  g.DeterminantRatioFixesVolumeScale /\
  g.DeterminantRatioFixesFullMetricConformalFactor /\
  g.NearPTConformalityProved /\
  g.UniqueOmegaFromRatioDerived

def DeterminantRatioOmegaFrontier
    (g : DeterminantRatioToWeylOmegaObstructionGate) : Prop :=
  g.JanusDeterminantRatioAvailable /\
  g.FLRWVolumeRatioFormulaDeclared /\
  g.ConformalCaseRelationDeclared /\
  g.DeterminantRatioFixesVolumeScale /\
  Not g.DeterminantRatioFixesFullMetricConformalFactor /\
  Not g.NearPTConformalityProved /\
  Not g.UniqueOmegaFromRatioDerived

theorem determinant_ratio_volume_is_not_unique_omega
    (g : DeterminantRatioToWeylOmegaObstructionGate)
    (hFrontier : DeterminantRatioOmegaFrontier g) :
    Not (DeterminantRatioOmegaClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.1 h.2.2.2.2.1

end P0EFTJanusDeterminantRatioToWeylOmegaObstructionGate
end JanusFormal
