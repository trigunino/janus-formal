namespace JanusFormal

structure EThroatRemainingNonCircularFrontiers where
  boundaryPhaseSpaceDerived : Prop
  boundaryHilbertSpaceDerived : Prop
  microcanonicalStateLawDerived : Prop
  tqftBoundaryTheoryDerived : Prop
  tqftLevelDerived : Prop
  primitiveSectorDerived : Prop

def EThroatRemainingNonCircularFrontiers.microcanonicalReady
    (f : EThroatRemainingNonCircularFrontiers) : Prop :=
  f.boundaryPhaseSpaceDerived ∧
    f.boundaryHilbertSpaceDerived ∧
    f.microcanonicalStateLawDerived

def EThroatRemainingNonCircularFrontiers.tqftReady
    (f : EThroatRemainingNonCircularFrontiers) : Prop :=
  f.tqftBoundaryTheoryDerived ∧
    f.tqftLevelDerived ∧
    f.primitiveSectorDerived

def EThroatRemainingNonCircularFrontiers.selectsNonCircularN
    (f : EThroatRemainingNonCircularFrontiers) : Prop :=
  f.microcanonicalReady ∨ f.tqftReady

theorem remaining_frontiers_need_boundary_law
    (f : EThroatRemainingNonCircularFrontiers)
    (hMicro : ¬ f.microcanonicalReady)
    (hTQFT : ¬ f.tqftReady) :
    ¬ f.selectsNonCircularN := by
  intro h
  cases h with
  | inl hm => exact hMicro hm
  | inr ht => exact hTQFT ht

end JanusFormal
