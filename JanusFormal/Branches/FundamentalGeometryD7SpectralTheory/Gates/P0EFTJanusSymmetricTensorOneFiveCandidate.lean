import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPeriodicQuarterCompetition

namespace JanusFormal
namespace P0EFTJanusSymmetricTensorOneFiveCandidate

set_option autoImplicit false

open P0EFTJanusPeriodicQuarterCompetition

/-- Fiber rank of symmetric two-tensors in dimension `d`. -/
def symmetricTwoTensorRank (dimension : ℕ) : ℕ :=
  dimension * (dimension + 1) / 2

/-- Fiber rank of traceless symmetric two-tensors. -/
def tracelessSymmetricTwoTensorRank (dimension : ℕ) : ℕ :=
  symmetricTwoTensorRank dimension - 1

@[simp] theorem symmetric_two_tensor_rank_three :
    symmetricTwoTensorRank 3 = 6 := by
  norm_num [symmetricTwoTensorRank]

@[simp] theorem traceless_symmetric_two_tensor_rank_three :
    tracelessSymmetricTwoTensorRank 3 = 5 := by
  norm_num [tracelessSymmetricTwoTensorRank,
    symmetricTwoTensorRank]

/-- The three-dimensional symmetric tensor splits into trace rank one and traceless rank five. -/
theorem three_dimensional_trace_traceless_rank_decomposition :
    1 + tracelessSymmetricTwoTensorRank 3 =
      symmetricTwoTensorRank 3 := by
  norm_num [tracelessSymmetricTwoTensorRank,
    symmetricTwoTensorRank]

/-- One-fold trace component. -/
abbrev TraceComponent := ℝ

/-- One-fold traceless symmetric component proxy. -/
abbrev TracelessComponent := Fin 5 → ℝ

/-- PT-doubled trace components. -/
abbrev TwoFoldTraceField := TraceComponent × TraceComponent

/-- PT-doubled traceless components. -/
abbrev TwoFoldTracelessField :=
  TracelessComponent × TracelessComponent

/-- Full doubled symmetric-tensor proxy. -/
abbrev TwoFoldSymmetricTensorField :=
  TwoFoldTraceField × TwoFoldTracelessField

/-- Negation on the doubled traceless sector only. -/
def tracelessHalfTurn
    (field : TwoFoldSymmetricTensorField) :
    TwoFoldSymmetricTensorField :=
  (field.1,
    (fun index => -field.2.1 index,
      fun index => -field.2.2 index))

/-- Internal quarter turn acts trivially on the trace pair and as `J(A,B)=(-B,A)` on traceless fields. -/
def traceTracelessQuarterTurn
    (field : TwoFoldSymmetricTensorField) :
    TwoFoldSymmetricTensorField :=
  (field.1,
    (fun index => -field.2.2 index,
      field.2.1))

/-- Squaring the internal action gives a traceless half-turn. -/
theorem trace_traceless_quarter_turn_square
    (field : TwoFoldSymmetricTensorField) :
    traceTracelessQuarterTurn
        (traceTracelessQuarterTurn field) =
      tracelessHalfTurn field := by
  ext index <;>
    simp [traceTracelessQuarterTurn, tracelessHalfTurn]

/-- Four applications give the identity. -/
theorem trace_traceless_quarter_turn_four
    (field : TwoFoldSymmetricTensorField) :
    traceTracelessQuarterTurn
      (traceTracelessQuarterTurn
        (traceTracelessQuarterTurn
          (traceTracelessQuarterTurn field))) = field := by
  rw [trace_traceless_quarter_turn_square,
    trace_traceless_quarter_turn_square]
  ext index <;> simp [tracelessHalfTurn]

/-- Real ranks of the doubled trace and traceless sectors. -/
def doubledTraceRealRank : ℕ := 2

def doubledTracelessRealRank : ℕ := 2 * 5

def doubledSymmetricRealRank : ℕ := 2 * 6

@[simp] theorem doubled_trace_real_rank_is_two :
    doubledTraceRealRank = 2 := by rfl

@[simp] theorem doubled_traceless_real_rank_is_ten :
    doubledTracelessRealRank = 10 := by
  norm_num [doubledTracelessRealRank]

@[simp] theorem doubled_symmetric_real_rank_is_twelve :
    doubledSymmetricRealRank = 12 := by
  norm_num [doubledSymmetricRealRank]

/-- After pairing the two real folds, the determinant complex ranks are one and five. -/
def periodicTraceDeterminantWeight : ℕ := 1

def quarterTracelessDeterminantWeight : ℕ := 5

@[simp] theorem trace_traceless_determinant_weights_are_one_to_five :
    periodicTraceDeterminantWeight = 1 /\
      quarterTracelessDeterminantWeight = 5 := by
  norm_num [periodicTraceDeterminantWeight,
    quarterTracelessDeterminantWeight]

/-- The resulting same-sign bosonic determinant algebra has the `r=1/3` root. -/
@[simp] theorem trace_traceless_one_five_stationary_root :
    stationarityPolynomial
      periodicTraceDeterminantWeight
      quarterTracelessDeterminantWeight
      (1 / 3) = 0 := by
  norm_num [periodicTraceDeterminantWeight,
    quarterTracelessDeterminantWeight,
    stationarityPolynomial]

/--
The integer five therefore has a natural three-dimensional geometric source:
it is the off-shell fiber rank of `Sym^2_0(T*Sigma)`, not the number of physical
massive-spin-two polarizations.  The PT-doubled real trace/traceless bundles
become complex determinant ranks `1:5` under an internal quarter-turn action.

A physical graviton calculation must still include constraints, Jacobians and
vector/scalar ghosts; those can change the superdeterminant weights.
-/
structure SymmetricTensorOneFivePhysicalStatus where
  twoFoldSymmetricTensorBundleDerived : Prop
  traceTracelessSplittingGlobalized : Prop
  internalQuarterTurnDerivedFromOrbifold : Prop
  traceSectorPeriodicProved : Prop
  tracelessSectorQuarterHolonomyProved : Prop
  gaussianRealityConditionHandled : Prop
  gaugeFixingDerived : Prop
  vectorAndScalarGhostsIncluded : Prop
  netSuperdeterminantWeightsComputed : Prop
  oneFiveRatioSurvivesGaugeReduction : Prop
  stableOneThirdRootSurvivesFullSpectrum : Prop
  finiteCountertermsFixedMicroscopically : Prop


def symmetricTensorOneFivePhysicalClosure
    (s : SymmetricTensorOneFivePhysicalStatus) : Prop :=
  s.twoFoldSymmetricTensorBundleDerived /\
  s.traceTracelessSplittingGlobalized /\
  s.internalQuarterTurnDerivedFromOrbifold /\
  s.traceSectorPeriodicProved /\
  s.tracelessSectorQuarterHolonomyProved /\
  s.gaussianRealityConditionHandled /\
  s.gaugeFixingDerived /\
  s.vectorAndScalarGhostsIncluded /\
  s.netSuperdeterminantWeightsComputed /\
  s.oneFiveRatioSurvivesGaugeReduction /\
  s.stableOneThirdRootSurvivesFullSpectrum /\
  s.finiteCountertermsFixedMicroscopically

end P0EFTJanusSymmetricTensorOneFiveCandidate
end JanusFormal
