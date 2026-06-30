import Mathlib

namespace JanusFormal
namespace SolderLaw

set_option autoImplicit false
set_option linter.unnecessarySimpa false

def Filter (A : Type) : Type := Set A
def HasUnique (A : Type) (p : A -> Prop) : Prop := ExistsUnique p

structure SolderState where
  aPT : Rat
  bridgeL : Rat
  kTop : Rat
deriving DecidableEq

def ptCompatible : Filter SolderState := fun _ => True
def sameLCompatible : Filter SolderState := fun _ => True
def stableBranch : Filter SolderState := fun _ => True
def noFit : Filter SolderState := fun _ => True

def filterOnlySolder : Set SolderState :=
  fun s => ptCompatible s ∧ sameLCompatible s ∧ stableBranch s ∧ noFit s

def solderSelector (s : SolderState) : Rat × Rat := (s.aPT, s.bridgeL)

theorem filter_only_solder_not_unique :
    Not (HasUnique SolderState filterOnlySolder) := by
  intro h
  rcases h with ⟨s0, hs0, huniq⟩
  let sA : SolderState := { aPT := 0, bridgeL := 0, kTop := 0 }
  let sB : SolderState := { aPT := 1, bridgeL := 0, kTop := 0 }
  have hA : filterOnlySolder sA := by
    simp [filterOnlySolder, ptCompatible, sameLCompatible, stableBranch, noFit]
  have hB : filterOnlySolder sB := by
    simp [filterOnlySolder, ptCompatible, sameLCompatible, stableBranch, noFit]
  have hAeq : sA = s0 := huniq sA hA
  have hBeq : sB = s0 := huniq sB hB
  have hAB : sA = sB := hAeq.trans hBeq.symm
  have hval : sA.aPT = sB.aPT := congrArg SolderState.aPT hAB
  have hzero : (0 : Rat) = 1 := by
    simpa [sA, sB] using hval
  exact zero_ne_one hzero

theorem filter_only_allows_distinct_solder_selectors :
    Exists (fun s1 =>
      Exists (fun s2 =>
        filterOnlySolder s1 ∧ filterOnlySolder s2 ∧
          solderSelector s1 ≠ solderSelector s2)) := by
  let sA : SolderState := { aPT := 0, bridgeL := 0, kTop := 0 }
  let sB : SolderState := { aPT := 1, bridgeL := 0, kTop := 0 }
  have hA : filterOnlySolder sA := by
    simp [filterOnlySolder, ptCompatible, sameLCompatible, stableBranch, noFit]
  have hB : filterOnlySolder sB := by
    simp [filterOnlySolder, ptCompatible, sameLCompatible, stableBranch, noFit]
  have hsel : solderSelector sA ≠ solderSelector sB := by
    intro h
    have hfst : (solderSelector sA).1 = (solderSelector sB).1 := congrArg Prod.fst h
    have hzero : (0 : Rat) = 1 := by
      simpa [solderSelector, sA, sB] using hfst
    exact zero_ne_one hzero
  exact ⟨sA, ⟨sB, ⟨hA, ⟨hB, hsel⟩⟩⟩⟩

def BridgeSelected {A L : Type} (source : A -> Prop) (bridge : A -> L) (l : L) : Prop :=
  ∃ a, source a ∧ bridge a = l

theorem unique_source_law_implies_unique_bridge
    {A L : Type} (source : A -> Prop) (bridge : A -> L)
    (hsource : ExistsUnique source) :
    ExistsUnique (BridgeSelected source bridge) := by
  rcases hsource with ⟨a0, ha0, huniq⟩
  refine ⟨bridge a0, ?_, ?_⟩
  · exact ⟨a0, ha0, rfl⟩
  · intro l hl
    rcases hl with ⟨a, ha, hbridge⟩
    have haeq : a = a0 := huniq a ha
    rw [← hbridge, haeq]

theorem unique_bridge_and_injective_bridge_imply_unique_source
    {A L : Type} (source : A -> Prop) (bridge : A -> L)
    (hbridgeUnique : ExistsUnique (BridgeSelected source bridge))
    (hinj : Function.Injective bridge) :
    ExistsUnique source := by
  rcases hbridgeUnique with ⟨l0, hl0, huniqL⟩
  rcases hl0 with ⟨a0, ha0, hbridge0⟩
  refine ⟨a0, ha0, ?_⟩
  intro a ha
  have hsel : BridgeSelected source bridge (bridge a) := ⟨a, ha, rfl⟩
  have hEqL : bridge a = l0 := huniqL (bridge a) hsel
  apply hinj
  exact hEqL.trans hbridge0.symm

def boolSource : Bool -> Prop := fun _ => True
def constantBridgeToUnit : Bool -> Unit := fun _ => ()
def selectedUnitBridge : Unit -> Prop :=
  BridgeSelected boolSource constantBridgeToUnit

theorem unique_bridge_does_not_imply_unique_source_without_injectivity :
    ExistsUnique selectedUnitBridge ∧ Not (HasUnique Bool boolSource) := by
  constructor
  · refine ⟨(), ?_, ?_⟩
    · exact ⟨false, trivial, rfl⟩
    · intro u hu
      cases u
      rfl
  · intro h
    rcases h with ⟨b, hb, huniq⟩
    have hf : false = b := huniq false trivial
    have ht : true = b := huniq true trivial
    have hft : false = true := hf.trans ht.symm
    cases hft

inductive ConstraintKind where
  | filter
  | sourceEquation
  | missingEquation
deriving DecidableEq

structure SolderCondition where
  name : String
  kind : ConstraintKind
  selectsUnique : Prop

def ptCondition : SolderCondition :=
  { name := "PT", kind := ConstraintKind.filter, selectsUnique := False }

def sameLCondition : SolderCondition :=
  { name := "same_L", kind := ConstraintKind.filter, selectsUnique := False }

def stabilityCondition : SolderCondition :=
  { name := "stability", kind := ConstraintKind.filter, selectsUnique := False }

def sourceEquationCondition : SolderCondition :=
  { name := "source_action_EL", kind := ConstraintKind.missingEquation, selectsUnique := False }

theorem pt_sameL_stability_are_filters :
    ptCondition.kind = ConstraintKind.filter ∧
    sameLCondition.kind = ConstraintKind.filter ∧
    stabilityCondition.kind = ConstraintKind.filter := by
  exact ⟨rfl, ⟨rfl, rfl⟩⟩

theorem source_equation_is_missing :
    sourceEquationCondition.kind = ConstraintKind.missingEquation := by
  rfl

def PredictionClosedByFiltersOnly : Prop :=
  HasUnique SolderState filterOnlySolder

theorem prediction_closed_by_filters_only_false :
    Not PredictionClosedByFiltersOnly := by
  exact filter_only_solder_not_unique

def minimalSolderLawConclusion : Prop :=
  Not (HasUnique SolderState filterOnlySolder) ∧
  Not PredictionClosedByFiltersOnly ∧
  (∀ {A L : Type} (source : A -> Prop) (bridge : A -> L),
    ExistsUnique source -> ExistsUnique (BridgeSelected source bridge))

theorem minimal_solder_law_summary : minimalSolderLawConclusion := by
  constructor
  · exact filter_only_solder_not_unique
  · constructor
    · exact prediction_closed_by_filters_only_false
    · intro A L source bridge hsource
      exact unique_source_law_implies_unique_bridge source bridge hsource

end SolderLaw
end JanusFormal
