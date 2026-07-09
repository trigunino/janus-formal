import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31Sym4BoundaryStateLawDerivationAttemptGate

namespace JanusFormal
namespace P0EFTJanusBoundaryDimensionToAminMapAuditGate

set_option autoImplicit false

structure BoundaryDimensionToAminMapAuditGate where
  NEquals1001 : Prop
  linearMapReachesPredrag : Prop
  areaMapReachesPredrag : Prop
  volumeMapReachesPredrag : Prop
  entropyMapReachesPredrag : Prop
  linearResolutionMapDerived : Prop

def dimensionToAminMapClosed
    (g : BoundaryDimensionToAminMapAuditGate) : Prop :=
  g.NEquals1001 /\
  g.linearMapReachesPredrag /\
  g.linearResolutionMapDerived

def dimensionToAminAuditFrontier
    (g : BoundaryDimensionToAminMapAuditGate) : Prop :=
  g.NEquals1001 /\
  g.linearMapReachesPredrag /\
  Not g.areaMapReachesPredrag /\
  Not g.volumeMapReachesPredrag /\
  Not g.entropyMapReachesPredrag /\
  Not g.linearResolutionMapDerived

theorem N_without_linear_map_does_not_close_amin
    (g : BoundaryDimensionToAminMapAuditGate)
    (hFrontier : dimensionToAminAuditFrontier g) :
    Not (dimensionToAminMapClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2 h.2.2

end P0EFTJanusBoundaryDimensionToAminMapAuditGate
end JanusFormal
