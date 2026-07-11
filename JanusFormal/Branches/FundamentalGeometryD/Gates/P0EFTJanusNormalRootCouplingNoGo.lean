import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift

namespace JanusFormal
namespace P0EFTJanusNormalRootCouplingNoGo

set_option autoImplicit false

open P0EFTJanusNormalOrientationZ4Lift

/-- A normal square root together with an independently assigned matter phase. -/
structure RootMatterCoupling where
  normalRoot : NormalRootPhase
  matterPhase : ZMod 4
  normalRootLaw : IsNormalSquareRoot normalRoot

/-- Couple the same normal root to any chosen matter phase. -/
def couplingWithMatterPhase
    (normalRoot : NormalRootPhase)
    (hRoot : IsNormalSquareRoot normalRoot)
    (matterPhase : ZMod 4) : RootMatterCoupling :=
  { normalRoot := normalRoot
    matterPhase := matterPhase
    normalRootLaw := hRoot }

/-- The same geometric root supports trivial and quarter matter actions. -/
theorem same_normal_root_supports_distinct_matter_couplings :
    ∃ first second : RootMatterCoupling,
      first.normalRoot = second.normalRoot /\
      first.matterPhase = 0 /\
      second.matterPhase = 1 /\
      first.matterPhase ≠ second.matterPhase := by
  exact ⟨couplingWithMatterPhase 1 one_is_normal_square_root 0,
    couplingWithMatterPhase 1 one_is_normal_square_root 1,
    rfl, rfl, rfl, by native_decide⟩

/-- Forgetting matter coupling leaves only normal-root topology. -/
def forgetMatterCoupling
    (s : RootMatterCoupling) : NormalRootPhase :=
  s.normalRoot

/-- Equal geometric root data do not imply equal matter phases. -/
theorem normal_root_does_not_determine_matter_action :
    ∃ first second : RootMatterCoupling,
      forgetMatterCoupling first = forgetMatterCoupling second /\
      first.matterPhase ≠ second.matterPhase := by
  rcases same_normal_root_supports_distinct_matter_couplings with
    ⟨first, second, hRoot, _, _, hDifferent⟩
  exact ⟨first, second, hRoot, hDifferent⟩

/-- PT conjugates the geometric root but still leaves the coupling law to be specified. -/
def ptConjugateCoupling
    (s : RootMatterCoupling) : RootMatterCoupling :=
  { normalRoot := ptConjugatePhase s.normalRoot
    matterPhase := -s.matterPhase
    normalRootLaw :=
      pt_preserves_normal_square_roots
        s.normalRoot s.normalRootLaw }

/-- PT conjugation is involutive on the algebraic coupling data. -/
theorem pt_conjugate_coupling_involutive
    (s : RootMatterCoupling) :
    ptConjugateCoupling (ptConjugateCoupling s) = s := by
  cases s
  ext <;> simp [ptConjugateCoupling, ptConjugatePhase]

/--
The square root of the one-sided normal line supplies a flat phase local system,
but it does not say which physical bundle carries that phase.  Assigning it
only to `Sym^2_0`, to spinors, to ghosts or to another internal multiplet is an
additional representation/coupling theorem, not a consequence of the normal
line alone.
-/
structure NormalRootCouplingPhysicalStatus where
  normalRootLineConstructed : Prop
  candidateMatterBundlesClassified : Prop
  couplingHomomorphismDerived : Prop
  traceSectorActionDerived : Prop
  tracelessSectorActionDerived : Prop
  spinorAndGhostActionsDerived : Prop
  ptCompatibilityProved : Prop
  uniquenessOrSelectionPrincipleDerived : Prop


def normalRootCouplingPhysicalClosed
    (s : NormalRootCouplingPhysicalStatus) : Prop :=
  s.normalRootLineConstructed /\
  s.candidateMatterBundlesClassified /\
  s.couplingHomomorphismDerived /\
  s.traceSectorActionDerived /\
  s.tracelessSectorActionDerived /\
  s.spinorAndGhostActionsDerived /\
  s.ptCompatibilityProved /\
  s.uniquenessOrSelectionPrincipleDerived

end P0EFTJanusNormalRootCouplingNoGo
end JanusFormal
