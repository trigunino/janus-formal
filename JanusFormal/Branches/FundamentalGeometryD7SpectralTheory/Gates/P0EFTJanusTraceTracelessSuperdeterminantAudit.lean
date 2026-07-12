import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusSymmetricTensorOneFiveCandidate

namespace JanusFormal
namespace P0EFTJanusTraceTracelessSuperdeterminantAudit

set_option autoImplicit false

open P0EFTJanusSymmetricTensorOneFiveCandidate

/-- Integer bookkeeping for a gauge-fixed determinant sector. -/
structure SectorSuperWeight where
  rawBundleRank : ℕ
  bosonicCopies : ℕ
  fermionicGhostCopies : ℕ

/-- Signed exponent in a formal superdeterminant. -/
def effectiveSuperWeight (s : SectorSuperWeight) : ℤ :=
  (s.bosonicCopies : ℤ) * s.rawBundleRank -
    (s.fermionicGhostCopies : ℤ) * s.rawBundleRank

/-- Same raw rank can lead to different effective determinant weights. -/
theorem raw_rank_does_not_fix_superweight :
    ∃ first second : SectorSuperWeight,
      first.rawBundleRank = second.rawBundleRank /\
      effectiveSuperWeight first ≠ effectiveSuperWeight second := by
  refine ⟨
    { rawBundleRank := 5
      bosonicCopies := 1
      fermionicGhostCopies := 0 },
    { rawBundleRank := 5
      bosonicCopies := 1
      fermionicGhostCopies := 1 },
    rfl, ?_⟩
  norm_num [effectiveSuperWeight]

/-- Off-shell trace/traceless rank package. -/
def naiveTraceSector : SectorSuperWeight :=
  { rawBundleRank := periodicTraceDeterminantWeight
    bosonicCopies := 1
    fermionicGhostCopies := 0 }


def naiveTracelessSector : SectorSuperWeight :=
  { rawBundleRank := quarterTracelessDeterminantWeight
    bosonicCopies := 1
    fermionicGhostCopies := 0 }

/-- Without gauge or ghost corrections the raw ratio is indeed `1:5`. -/
theorem naive_trace_traceless_superweights_are_one_five :
    effectiveSuperWeight naiveTraceSector = 1 /\
      effectiveSuperWeight naiveTracelessSector = 5 := by
  norm_num [effectiveSuperWeight,
    naiveTraceSector, naiveTracelessSector,
    periodicTraceDeterminantWeight,
    quarterTracelessDeterminantWeight]

/-- A ghost copy can cancel the whole rank-five raw sector. -/
def ghostCancelledTracelessSector : SectorSuperWeight :=
  { rawBundleRank := quarterTracelessDeterminantWeight
    bosonicCopies := 1
    fermionicGhostCopies := 1 }

@[simp] theorem ghost_cancelled_traceless_weight_zero :
    effectiveSuperWeight ghostCancelledTracelessSector = 0 := by
  norm_num [effectiveSuperWeight,
    ghostCancelledTracelessSector,
    quarterTracelessDeterminantWeight]

/-- The same geometric `1+5` bundle split therefore does not imply a `1:5` superdeterminant. -/
theorem trace_traceless_rank_does_not_imply_one_five_superdeterminant :
    periodicTraceDeterminantWeight = 1 /\
      quarterTracelessDeterminantWeight = 5 /\
      effectiveSuperWeight ghostCancelledTracelessSector ≠ 5 := by
  exact ⟨trace_traceless_determinant_weights_are_one_to_five.1,
    trace_traceless_determinant_weights_are_one_to_five.2,
    by norm_num [effectiveSuperWeight,
      ghostCancelledTracelessSector,
      quarterTracelessDeterminantWeight]⟩

/--
The identity `Sym^2 = 1 + 5` is an off-shell fiber-rank theorem.  Promoting it
to the exponent ratio of a physical one-loop determinant requires the complete
quadratic complex: gauge fixing, constraints, Jacobians, vector/scalar ghosts,
zero modes and the operator spectrum in each sector.
-/
structure TraceTracelessSuperdeterminantStatus where
  symmetricTensorBundleConstructed : Prop
  traceTracelessSplitGlobalized : Prop
  quadraticActionDiagonalized : Prop
  diffeomorphismGaugeFixed : Prop
  vectorGhostOperatorDerived : Prop
  scalarJacobianDerived : Prop
  zeroModesSeparated : Prop
  signedDeterminantExponentsComputed : Prop
  oneFiveRatioSurvivesFullComplex : Prop
  stableVacuumRecomputed : Prop


def traceTracelessSuperdeterminantClosed
    (s : TraceTracelessSuperdeterminantStatus) : Prop :=
  s.symmetricTensorBundleConstructed /\
  s.traceTracelessSplitGlobalized /\
  s.quadraticActionDiagonalized /\
  s.diffeomorphismGaugeFixed /\
  s.vectorGhostOperatorDerived /\
  s.scalarJacobianDerived /\
  s.zeroModesSeparated /\
  s.signedDeterminantExponentsComputed /\
  s.oneFiveRatioSurvivesFullComplex /\
  s.stableVacuumRecomputed

end P0EFTJanusTraceTracelessSuperdeterminantAudit
end JanusFormal
