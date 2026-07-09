import JanusFormal.Legacy.P0EFT.Gates.P0EFTRadionAmplitudeClosure

namespace JanusFormal
namespace P0EFTChiInfinityStationaryClosure

set_option autoImplicit false

structure ChiInfinityStationaryClosure where
  coshPotentialDerivativeComputed : Prop
  coshAloneForcesChiInfinityZero : Prop
  nonzeroChiInfinityRequiresBackgroundSource : Prop
  stationaryEquationWithJbgEncoded : Prop
  jbgDerivedFromJanusJunction : Prop
  chiInfinityFixedByJanusBackground : Prop
  amplitudeFullyClosed : Prop
  jbgTraceJumpDerived : Prop

def stationaryNoGoForCoshAlone (c : ChiInfinityStationaryClosure) : Prop :=
  c.coshPotentialDerivativeComputed /\
  c.coshAloneForcesChiInfinityZero /\
  c.nonzeroChiInfinityRequiresBackgroundSource

def chiInfinityClosedWithJbg (c : ChiInfinityStationaryClosure) : Prop :=
  stationaryNoGoForCoshAlone c /\
  c.stationaryEquationWithJbgEncoded /\
  c.jbgTraceJumpDerived /\
  c.jbgDerivedFromJanusJunction /\
  c.chiInfinityFixedByJanusBackground

def amplitudeClosedAfterChiInfinity (c : ChiInfinityStationaryClosure) : Prop :=
  chiInfinityClosedWithJbg c /\ c.amplitudeFullyClosed

theorem cosh_alone_cannot_fix_nonzero_chi_infinity
    (c : ChiInfinityStationaryClosure)
    (hDeriv : c.coshPotentialDerivativeComputed)
    (hZero : c.coshAloneForcesChiInfinityZero)
    (hNeed : c.nonzeroChiInfinityRequiresBackgroundSource) :
    stationaryNoGoForCoshAlone c := by
  exact And.intro hDeriv (And.intro hZero hNeed)

theorem missing_jbg_blocks_chi_infinity_closure
    (c : ChiInfinityStationaryClosure)
    (hMissing : Not c.jbgDerivedFromJanusJunction) :
    Not (chiInfinityClosedWithJbg c) := by
  intro h
  exact hMissing h.right.right.right.left

theorem chi_infinity_closes_after_junction_source
    (c : ChiInfinityStationaryClosure)
    (hNoGo : stationaryNoGoForCoshAlone c)
    (hEq : c.stationaryEquationWithJbgEncoded)
    (hTrace : c.jbgTraceJumpDerived)
    (hJ : c.jbgDerivedFromJanusJunction)
    (hChi : c.chiInfinityFixedByJanusBackground) :
    chiInfinityClosedWithJbg c := by
  exact And.intro hNoGo (And.intro hEq (And.intro hTrace (And.intro hJ hChi)))

theorem amplitude_closes_after_chi_infinity
    (c : ChiInfinityStationaryClosure)
    (hChi : chiInfinityClosedWithJbg c)
    (hAmp : c.amplitudeFullyClosed) :
    amplitudeClosedAfterChiInfinity c := by
  exact And.intro hChi hAmp

end P0EFTChiInfinityStationaryClosure
end JanusFormal
