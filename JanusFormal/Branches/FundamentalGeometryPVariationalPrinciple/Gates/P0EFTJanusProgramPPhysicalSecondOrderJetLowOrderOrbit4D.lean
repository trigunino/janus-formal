import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanStructuredJetActionGroupoidRealization

/-!
# Low-order orbit projection of the Program P physical jet carrier

For each outer sector and paired Abelian column, this gate forgets a framed
background second jet to the installed algebraic structured jet and its exact
`(II, F)` quotient.  It then installs the genuine residual orthogonal-frame
and rank-two SpinC action groupoid on that reduced projection.

Only projected observables are considered here.  No deck action, matter-field
SpinC action, action on the full physical carrier, or invariant-theory
exhaustion is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalSecondOrderJetLowOrderOrbit4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

universe u v w

/-- Algebraic low-order structured jet underlying one physical Abelian
column of the framed background jet. -/
def StructuredBackgroundSecondJet.toAlgebraicStructuredJet
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    LowOrderStructuredJet Tangent Real :=
  forgetContinuousLowOrderStructuredJet
    (jet.toStructuredJet sector column)

/-- Exact algebraic `(II, F)` quotient of one physical Abelian column. -/
def StructuredBackgroundSecondJet.toLowOrderReducedData
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    LowOrderReducedData Tangent Real :=
  reduceLowOrderJet
    (StructuredBackgroundSecondJet.toAlgebraicStructuredJet
      jet sector column)

/-- The algebraic quotient agrees exactly with the already installed
continuous actual-jet extraction. -/
theorem StructuredBackgroundSecondJet.toLowOrderReducedData_eq_actualJetToLowOrderReducedData
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    StructuredBackgroundSecondJet.toLowOrderReducedData
        jet sector column =
      actualJetToLowOrderReducedData
        (jet.toActualJanusLocalJetData sector column) := by
  apply LowOrderReducedData.ext
  · rfl
  · rfl

@[simp]
theorem StructuredBackgroundSecondJet.toLowOrderReducedData_secondFundamental
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    (StructuredBackgroundSecondJet.toLowOrderReducedData
      jet sector column).secondFundamental =
      fun first second => jet.normalQuadratic sector first second :=
  rfl

@[simp]
theorem StructuredBackgroundSecondJet.toLowOrderReducedData_gaugeCurvature_apply
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2)
    (first second : Tangent) :
    (StructuredBackgroundSecondJet.toLowOrderReducedData
      jet sector column).gaugeCurvature first second =
      (jet.gaugeConnection sector column).firstDerivative first second -
        (jet.gaugeConnection sector column).firstDerivative second first :=
  rfl

/-- Combined quadratic-source and Abelian gauge equivalence at one selected
sector and physical gauge column. -/
def StructuredBackgroundSecondJet.LowOrderEquivalentAt
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (first second : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) : Prop :=
  CombinedEquivalent
    (StructuredBackgroundSecondJet.toAlgebraicStructuredJet
      first sector column)
    (StructuredBackgroundSecondJet.toAlgebraicStructuredJet
      second sector column)

/-- The exact orbit classifier on the projected physical background is
equality of its `(II, F)` data. -/
theorem StructuredBackgroundSecondJet.lowOrderEquivalentAt_iff_reduced_eq
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (first second : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    StructuredBackgroundSecondJet.LowOrderEquivalentAt
        first second sector column ↔
      StructuredBackgroundSecondJet.toLowOrderReducedData
          first sector column =
        StructuredBackgroundSecondJet.toLowOrderReducedData
          second sector column := by
  exact combined_equivalent_iff_reduced_eq _ _

/-- The residual orthogonal-frame and SpinC symmetry produces an honest arrow
on the reduced physical background projection. -/
def StructuredBackgroundSecondJet.residualSpinCArrow
    {Tangent : Type u}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2)
    (symmetry : LowOrderSpinCFrame Tangent Real) :
    ActionArrow (Symmetry := LowOrderSpinCFrame Tangent Real)
      (StructuredBackgroundSecondJet.toLowOrderReducedData
        jet sector column)
      (symmetry • StructuredBackgroundSecondJet.toLowOrderReducedData
        jet sector column) where
  element := symmetry
  maps_source := rfl

/-- Invariance under the installed residual orthogonal-frame and SpinC action
on reduced low-order data. -/
def IsResidualSpinCInvariant
    {Tangent : Type u} {Normal : Type v} {Target : Type w}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace Real Normal]
    (observable : LowOrderReducedData Tangent Normal → Target) : Prop :=
  ∀ (symmetry : LowOrderSpinCFrame Tangent Normal) data,
    observable (symmetry • data) = observable data

/-- A low-order evaluator with both exact source/gauge descent and residual
frame-SpinC invariance.  It is an evaluator of the projected background, not a
classification of all Program P local functionals. -/
structure ProjectedLowOrderInvariantEvaluator
    (Tangent : Type u) (Target : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent] where
  toFun : LowOrderStructuredJet Tangent Real → Target
  combinedInvariant : IsCombinedInvariant toFun
  reducedResidualInvariant :
    IsResidualSpinCInvariant (reducedObservable toFun)

/-- Evaluation on a physical background column factors through its exact
`(II, F)` quotient. -/
theorem ProjectedLowOrderInvariantEvaluator.evaluate_eq_reduced
    {Tangent : Type u} {Target : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    [FiniteDimensional Real Tangent]
    (evaluator : ProjectedLowOrderInvariantEvaluator Tangent Target)
    (jet : StructuredBackgroundSecondJet Tangent)
    (sector : Sector) (column : Fin 2) :
    evaluator.toFun
        (StructuredBackgroundSecondJet.toAlgebraicStructuredJet
          jet sector column) =
      reducedObservable evaluator.toFun
        (StructuredBackgroundSecondJet.toLowOrderReducedData
          jet sector column) := by
  exact combined_invariant_factors_through_reduced
    evaluator.toFun evaluator.combinedInvariant
    (StructuredBackgroundSecondJet.toAlgebraicStructuredJet
      jet sector column)

/-- The descended observable is constant along every installed residual
frame-SpinC arrow. -/
theorem ProjectedLowOrderInvariantEvaluator.reduced_eq_under_residualSpinC
    {Tangent : Type u} {Target : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    (evaluator : ProjectedLowOrderInvariantEvaluator Tangent Target)
    (symmetry : LowOrderSpinCFrame Tangent Real)
    (data : LowOrderReducedData Tangent Real) :
    reducedObservable evaluator.toFun (symmetry • data) =
      reducedObservable evaluator.toFun data :=
  evaluator.reducedResidualInvariant symmetry data

/-- The residual-invariant reduction is unique among reductions that factor
the evaluator through the combined source/gauge quotient. -/
theorem ProjectedLowOrderInvariantEvaluator.existsUnique_reduction
    {Tangent : Type u} {Target : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace Real Tangent]
    (evaluator : ProjectedLowOrderInvariantEvaluator Tangent Target) :
    ∃! reduced : LowOrderReducedData Tangent Real → Target,
      (∀ jet,
        evaluator.toFun jet = reduced (reduceLowOrderJet jet)) ∧
      IsResidualSpinCInvariant reduced := by
  refine ⟨reducedObservable evaluator.toFun, ?_, ?_⟩
  · exact ⟨combined_invariant_factors_through_reduced
      evaluator.toFun evaluator.combinedInvariant,
      evaluator.reducedResidualInvariant⟩
  · intro other hOther
    funext data
    have hAtSlice := hOther.1 (reducedSlice data)
    calc
      other data = other (reduceLowOrderJet (reducedSlice data)) := by
        rw [reduce_reducedSlice]
      _ = evaluator.toFun (reducedSlice data) := hAtSlice.symm
      _ = reducedObservable evaluator.toFun data := rfl

/-- Bulk shortcut to the reduced background data. -/
def BulkPhysicalSecondOrderJet.toLowOrderReducedData
    {period : Real} {hPeriod : period ≠ 0}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (jet : BulkPhysicalSecondOrderJet period hPeriod configuration)
    (sector : Sector) (column : Fin 2) :
    LowOrderReducedData EuclideanR4 Real :=
  StructuredBackgroundSecondJet.toLowOrderReducedData
    jet.background sector column

/-- Throat shortcut to the reduced background data. -/
def ThroatPhysicalSecondOrderJet.toLowOrderReducedData
    {period : Real} {hPeriod : period ≠ 0}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (jet : ThroatPhysicalSecondOrderJet period hPeriod configuration)
    (sector : Sector) (column : Fin 2) :
    LowOrderReducedData EuclideanR3 Real :=
  StructuredBackgroundSecondJet.toLowOrderReducedData
    jet.background sector column

end
end P0EFTJanusProgramPPhysicalSecondOrderJetLowOrderOrbit4D
end JanusFormal
