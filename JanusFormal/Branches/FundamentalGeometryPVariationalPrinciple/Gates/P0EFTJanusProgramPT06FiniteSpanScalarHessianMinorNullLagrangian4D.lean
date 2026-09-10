import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D

/-!
# Finite span of scalar Hessian-minor null Lagrangians

This gate closes Gate911's scalar two-direction Hessian minors under finite
real linear combinations.  It supplies the summed order-two current, proves
that its genuine Gate879 horizontal differential is the pulled-back summed
density, and transports Gate880 nullity to the finite span.

Scaling, disjoint-union addition, and one-point families expose the vector
space operations on represented sums.  This is only the finite span of the
three scalar Hessian minors; it is not a classification of the full
second-order polynomial Euler kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FiniteSpanScalarHessianMinorNullLagrangian4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v w

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Real
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Real
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Real

/-- A finite weighted family of Gate911 scalar Hessian minors. -/
structure ProgramPT06FiniteSpanScalarHessianMinorData4D
    (Rank : Type u) where
  coefficient : Rank -> Real
  generator : Rank -> ProgramPT06ScalarHessianMinor4D

private theorem localFunctionTotalDerivative_fintype_sum_const_smul
    {Rank : Type u} [Fintype Rank]
    {Fiber : Type v} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat} (coefficient : Rank -> Real)
    (localFunction : Rank ->
      TruncatedThroatSpatialMultiindexJet Fiber order -> Target)
    (hDifferentiable : forall rank, Differentiable Real (localFunction rank))
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun source => ∑ rank : Rank,
          coefficient rank • localFunction rank source) jet =
      ∑ rank : Rank, coefficient rank •
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (localFunction rank) jet := by
  unfold programPT06ThroatSpatialLocalFunctionTotalDerivative
  change
    (fderiv Real
      (fun source => ∑ rank : Rank,
        (coefficient rank • localFunction rank) source)
      (truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet))
        (throatSpatialTotalDerivative direction jet) = _
  rw [fderiv_fun_sum (u := Finset.univ) (fun rank _ =>
    (hDifferentiable rank _).const_smul (coefficient rank))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro rank _
  rw [(((hDifferentiable rank _).hasFDerivAt).const_smul
    (coefficient rank)).fderiv]
  rfl

private theorem verticalPartialDerivative_fintype_sum_const_smul
    {Rank : Type u} [Fintype Rank]
    {Fiber : Type v} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat} (coefficient : Rank -> Real)
    (localFunction : Rank ->
      TruncatedThroatSpatialMultiindexJet Fiber order -> Target)
    (hDifferentiable : forall rank, Differentiable Real (localFunction rank))
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (fun source => ∑ rank : Rank,
          coefficient rank • localFunction rank source) jet index =
      ∑ rank : Rank, coefficient rank •
        programPT06ThroatSpatialVerticalPartialDerivative
          (localFunction rank) jet index := by
  ext variation
  simp only [programPT06ThroatSpatialVerticalPartialDerivative_apply]
  change
    (fderiv Real
      (fun source => ∑ rank : Rank,
        (coefficient rank • localFunction rank) source) jet)
        (programPT06ThroatSpatialJetCoordinateInjection index variation) = _
  rw [fderiv_fun_sum (u := Finset.univ) (fun rank _ =>
    (hDifferentiable rank _).const_smul (coefficient rank))]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro rank _
  rw [(((hDifferentiable rank _).hasFDerivAt).const_smul
    (coefficient rank)).fderiv]
  rfl

private theorem verticalPartialDerivative_contDiff_top
    {Fiber : Type v} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat}
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order -> Target)
    (hLocalFunction : ContDiff Real ⊤ localFunction)
    (index : ThroatSpatialTruncatedIndex order) :
    ContDiff Real ⊤ (fun jet =>
      programPT06ThroatSpatialVerticalPartialDerivative
        localFunction jet index) := by
  unfold programPT06ThroatSpatialVerticalPartialDerivative
  have hDerivative :
      ContDiff Real ⊤ (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := ⊤) (by simp)
  exact hDerivative.clm_comp contDiff_const

private theorem localFunctionTotalDerivative_contDiff_top
    {Fiber : Type v} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat}
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order -> Target)
    (hLocalFunction : ContDiff Real ⊤ localFunction)
    (direction : Fin 3) :
    ContDiff Real ⊤
      (programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        localFunction) := by
  unfold programPT06ThroatSpatialLocalFunctionTotalDerivative
  have hDerivative :
      ContDiff Real ⊤ (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := ⊤) (by simp)
  apply (hDerivative.comp ?_).clm_apply
  · unfold throatSpatialTotalDerivative
    fun_prop
  · unfold truncateThroatSpatialMultiindexJet
    fun_prop

/-- One Gate911 current written as a three-direction order-two current. -/
def programPT06ScalarHessianMinorCurrentComponent
    (minor : ProgramPT06ScalarHessianMinor4D) (direction : Fin 3) :
    SecondJet -> Real :=
  if direction = minor.first then
    programPT06ScalarHessianMinorCurrentFirstComponent minor
  else if direction = minor.second then
    programPT06ScalarHessianMinorCurrentSecondComponent minor
  else 0

/-- The genuine Gate879 divergence of the three-direction atom current. -/
def programPT06ScalarHessianMinorCurrentDivergence
    (minor : ProgramPT06ScalarHessianMinor4D) : ThirdJet -> Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06ScalarHessianMinorCurrentComponent minor direction) jet

private theorem programPT06ScalarHessianMinorCurrentComponent_contDiff
    (minor : ProgramPT06ScalarHessianMinor4D) (direction : Fin 3) :
    ContDiff Real ⊤
      (programPT06ScalarHessianMinorCurrentComponent minor direction) := by
  unfold programPT06ScalarHessianMinorCurrentComponent
  split_ifs
  · unfold programPT06ScalarHessianMinorCurrentFirstComponent
    fun_prop
  · unfold programPT06ScalarHessianMinorCurrentSecondComponent
    fun_prop
  · exact contDiff_const

/-- The three-direction atom current is exactly Gate911's displayed current. -/
theorem programPT06ScalarHessianMinorCurrentDivergence_eq_currentDH
    (minor : ProgramPT06ScalarHessianMinor4D) :
    programPT06ScalarHessianMinorCurrentDivergence minor =
      programPT06ScalarHessianMinorCurrentDH minor := by
  funext jet
  rcases minor with ⟨first, second, hDistinct⟩
  fin_cases first <;> fin_cases second
  all_goals try exact (hDistinct rfl).elim
  all_goals
    simp [programPT06ScalarHessianMinorCurrentDivergence,
      programPT06ScalarHessianMinorCurrentComponent,
      programPT06ScalarHessianMinorCurrentDH, Fin.sum_univ_three]
  all_goals ac_rfl

/-- The finite weighted sum of the explicit order-two current components. -/
def programPT06FiniteSpanScalarHessianMinorCurrentComponent
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (direction : Fin 3) : SecondJet -> Real :=
  fun jet => ∑ rank : Rank, data.coefficient rank •
    programPT06ScalarHessianMinorCurrentComponent
      (data.generator rank) direction jet

/-- The genuine Gate879 divergence of the finite summed order-two current. -/
def programPT06FiniteSpanScalarHessianMinorCurrentDivergence
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    ThirdJet -> Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06FiniteSpanScalarHessianMinorCurrentComponent
        data direction) jet

/-- The finite real linear combination of Gate911 Hessian-minor densities. -/
def programPT06FiniteSpanScalarHessianMinorDensityEvaluation
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    SecondJet -> Real :=
  fun jet => ∑ rank : Rank, data.coefficient rank •
    programPT06ScalarHessianMinorDensityEvaluation
      (data.generator rank) jet

private theorem programPT06FiniteSpanScalarHessianMinorCurrentDivergence_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    programPT06FiniteSpanScalarHessianMinorCurrentDivergence data =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06ScalarHessianMinorCurrentDivergence
          (data.generator rank) jet := by
  funext jet
  unfold programPT06FiniteSpanScalarHessianMinorCurrentDivergence
  have hDirection (direction : Fin 3) :
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (programPT06FiniteSpanScalarHessianMinorCurrentComponent
            data direction) jet =
        ∑ rank : Rank, data.coefficient rank •
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (programPT06ScalarHessianMinorCurrentComponent
              (data.generator rank) direction) jet := by
    exact localFunctionTotalDerivative_fintype_sum_const_smul
      data.coefficient
      (fun rank => programPT06ScalarHessianMinorCurrentComponent
        (data.generator rank) direction)
      (fun rank =>
        (programPT06ScalarHessianMinorCurrentComponent_contDiff
          (data.generator rank) direction).differentiable (by simp))
      direction jet
  simp_rw [hDirection]
  calc
    (∑ direction : Fin 3, ∑ rank : Rank, data.coefficient rank •
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06ScalarHessianMinorCurrentComponent
          (data.generator rank) direction) jet) =
        ∑ rank : Rank, ∑ direction : Fin 3, data.coefficient rank •
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (programPT06ScalarHessianMinorCurrentComponent
              (data.generator rank) direction) jet := by
      rw [Finset.sum_comm]
    _ = ∑ rank : Rank, data.coefficient rank •
        programPT06ScalarHessianMinorCurrentDivergence
          (data.generator rank) jet := by
      apply Finset.sum_congr rfl
      intro rank _
      unfold programPT06ScalarHessianMinorCurrentDivergence
      rw [Finset.smul_sum]

/-- The genuine Gate879 differential of the summed current equals the summed
density pulled from order two to order three. -/
theorem programPT06FiniteSpanScalarHessianMinorCurrentDivergence_eq_density
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (jet : ThirdJet) :
    programPT06FiniteSpanScalarHessianMinorCurrentDivergence data jet =
      programPT06FiniteSpanScalarHessianMinorDensityEvaluation data
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06FiniteSpanScalarHessianMinorCurrentDivergence_eq_sum]
  unfold programPT06FiniteSpanScalarHessianMinorDensityEvaluation
  apply Finset.sum_congr rfl
  intro rank _
  rw [programPT06ScalarHessianMinorCurrentDivergence_eq_currentDH,
    programPT06ScalarHessianMinorCurrentDH_eq_density]

private theorem programPT06ScalarHessianMinorDensity_contDiff
    (minor : ProgramPT06ScalarHessianMinor4D) :
    ContDiff Real ⊤
      (programPT06ScalarHessianMinorDensityEvaluation minor) := by
  unfold programPT06ScalarHessianMinorDensityEvaluation
  fun_prop

private theorem programPT06FiniteSpanScalarHessianMinorVerticalPartialZero_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data) =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalVerticalPartialZero
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) jet := by
  funext jet
  exact verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06ScalarHessianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      (programPT06ScalarHessianMinorDensity_contDiff
        (data.generator rank)).differentiable (by simp))
    jet programPT06SecondOrderZeroMultiIndex

private theorem programPT06FiniteSpanScalarHessianMinorVerticalPartialOne_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data)
        direction =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalVerticalPartialOne
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) direction jet := by
  funext jet
  exact verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06ScalarHessianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      (programPT06ScalarHessianMinorDensity_contDiff
        (data.generator rank)).differentiable (by simp))
    jet (programPT06SecondOrderFirstMultiIndex direction)

private theorem programPT06FiniteSpanScalarHessianMinorVerticalPartialTwo_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data)
        first second =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) first second jet := by
  funext jet
  exact verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06ScalarHessianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      (programPT06ScalarHessianMinorDensity_contDiff
        (data.generator rank)).differentiable (by simp))
    jet (programPT06SecondOrderSecondMultiIndex first second)

private theorem programPT06ScalarHessianMinorVerticalPartialOne_contDiff
    (minor : ProgramPT06ScalarHessianMinor4D) (direction : Fin 3) :
    ContDiff Real ⊤
      (programPT06SecondOrderLocalVerticalPartialOne
        (programPT06ScalarHessianMinorDensityEvaluation minor) direction) := by
  exact verticalPartialDerivative_contDiff_top
    (programPT06ScalarHessianMinorDensityEvaluation minor)
    (programPT06ScalarHessianMinorDensity_contDiff minor)
    (programPT06SecondOrderFirstMultiIndex direction)

private theorem programPT06ScalarHessianMinorVerticalPartialTwo_contDiff
    (minor : ProgramPT06ScalarHessianMinor4D) (first second : Fin 3) :
    ContDiff Real ⊤
      (programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06ScalarHessianMinorDensityEvaluation minor)
        first second) := by
  exact verticalPartialDerivative_contDiff_top
    (programPT06ScalarHessianMinorDensityEvaluation minor)
    (programPT06ScalarHessianMinorDensity_contDiff minor)
    (programPT06SecondOrderSecondMultiIndex first second)

private theorem programPT06FiniteSpanScalarHessianMinorEulerFirstTerm_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (direction : Fin 3) (jet : ThirdJet) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data)
        direction jet =
      ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) direction jet := by
  unfold programPT06SecondOrderLocalEulerFirstTotalTerm
  rw [programPT06FiniteSpanScalarHessianMinorVerticalPartialOne_eq_sum]
  exact localFunctionTotalDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06SecondOrderLocalVerticalPartialOne
      (programPT06ScalarHessianMinorDensityEvaluation
        (data.generator rank)) direction)
    (fun rank =>
      (programPT06ScalarHessianMinorVerticalPartialOne_contDiff
        (data.generator rank) direction).differentiable (by simp))
    direction jet

private theorem programPT06FiniteSpanScalarHessianMinorEulerSecondInner_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (first second : Fin 3) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative second
        (programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data)
          first second) =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06ThroatSpatialLocalFunctionTotalDerivative second
          (programPT06SecondOrderLocalVerticalPartialTwo
            (programPT06ScalarHessianMinorDensityEvaluation
              (data.generator rank)) first second) jet := by
  rw [programPT06FiniteSpanScalarHessianMinorVerticalPartialTwo_eq_sum]
  funext jet
  exact localFunctionTotalDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06SecondOrderLocalVerticalPartialTwo
      (programPT06ScalarHessianMinorDensityEvaluation
        (data.generator rank)) first second)
    (fun rank =>
      (programPT06ScalarHessianMinorVerticalPartialTwo_contDiff
        (data.generator rank) first second).differentiable (by simp))
    second jet

private theorem programPT06FiniteSpanScalarHessianMinorEulerSecondTerm_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (first second : Fin 3) (jet : FourthJet) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data)
        first second jet =
      ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) first second jet := by
  unfold programPT06SecondOrderLocalEulerSecondTotalTerm
  rw [programPT06FiniteSpanScalarHessianMinorEulerSecondInner_eq_sum]
  exact localFunctionTotalDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank =>
      programPT06ThroatSpatialLocalFunctionTotalDerivative second
        (programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) first second))
    (fun rank =>
      (localFunctionTotalDerivative_contDiff_top
        (programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) first second)
        (programPT06ScalarHessianMinorVerticalPartialTwo_contDiff
          (data.generator rank) first second) second).differentiable (by simp))
    first jet

private theorem programPT06SecondOrderLocalEuler_finiteSpanScalarHessianMinor_eq_sum
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data) jet =
      ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalEuler
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) jet := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06FiniteSpanScalarHessianMinorVerticalPartialZero_eq_sum]
  simp_rw [programPT06FiniteSpanScalarHessianMinorEulerFirstTerm_eq_sum,
    programPT06FiniteSpanScalarHessianMinorEulerSecondTerm_eq_sum]
  have hFirst :
      (∑ direction : Fin 3, ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06ScalarHessianMinorDensityEvaluation
            (data.generator rank)) direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) =
        ∑ rank : Rank, data.coefficient rank •
          (∑ direction : Fin 3,
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06ScalarHessianMinorDensityEvaluation
                (data.generator rank)) direction
              (truncateThroatSpatialMultiindexJet
                (by omega : 3 ≤ 4) jet)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro rank _
    rw [Finset.smul_sum]
  rw [hFirst]
  have hSecond :
      (∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          (∑ rank : Rank, data.coefficient rank •
            programPT06SecondOrderLocalEulerSecondTotalTerm
              (programPT06ScalarHessianMinorDensityEvaluation
                (data.generator rank)) first second jet)) =
        ∑ rank : Rank, data.coefficient rank •
          (∑ first : Fin 3, ∑ second : Fin 3,
            programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                (programPT06ScalarHessianMinorDensityEvaluation
                  (data.generator rank)) first second jet) := by
    calc
      _ = ∑ first : Fin 3, ∑ second : Fin 3, ∑ rank : Rank,
          data.coefficient rank •
            (programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                (programPT06ScalarHessianMinorDensityEvaluation
                  (data.generator rank)) first second jet) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro rank _
        module
      _ = ∑ first : Fin 3, ∑ rank : Rank, ∑ second : Fin 3,
          data.coefficient rank •
            (programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                (programPT06ScalarHessianMinorDensityEvaluation
                  (data.generator rank)) first second jet) := by
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.sum_comm]
      _ = ∑ rank : Rank, ∑ first : Fin 3, ∑ second : Fin 3,
          data.coefficient rank •
            (programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                (programPT06ScalarHessianMinorDensityEvaluation
                  (data.generator rank)) first second jet) := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro rank _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.smul_sum]
  rw [hSecond, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rank _
  rw [programPT06SecondOrderLocalEuler_formula]
  module

/-- Gate880 annihilates the finite real span of Gate911 Hessian minors. -/
theorem programPT06SecondOrderLocalEuler_finiteSpanScalarHessianMinor_eq_zero
    {Rank : Type u} [Fintype Rank]
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteSpanScalarHessianMinorDensityEvaluation data) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_finiteSpanScalarHessianMinor_eq_sum]
  apply Finset.sum_eq_zero
  intro rank _
  rw [programPT06SecondOrderLocalEuler_scalarHessianMinor_eq_zero]
  simp

/-- Scale every coefficient in a represented finite span. -/
def programPT06FiniteSpanScalarHessianMinorScale
    {Rank : Type u} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    ProgramPT06FiniteSpanScalarHessianMinorData4D Rank where
  coefficient := fun rank => scalar * data.coefficient rank
  generator := data.generator

/-- Add represented finite spans by disjoint union of their index types. -/
def programPT06FiniteSpanScalarHessianMinorAdd
    {LeftRank : Type u} [Fintype LeftRank]
    {RightRank : Type v} [Fintype RightRank]
    (left : ProgramPT06FiniteSpanScalarHessianMinorData4D LeftRank)
    (right : ProgramPT06FiniteSpanScalarHessianMinorData4D RightRank) :
    ProgramPT06FiniteSpanScalarHessianMinorData4D
      (LeftRank ⊕ RightRank) where
  coefficient := Sum.elim left.coefficient right.coefficient
  generator := Sum.elim left.generator right.generator

/-- Embed one Gate911 generator as a one-term family. -/
def programPT06FiniteSpanScalarHessianMinorOfGenerator
    (generator : ProgramPT06ScalarHessianMinor4D) :
    ProgramPT06FiniteSpanScalarHessianMinorData4D PUnit where
  coefficient := fun _ => 1
  generator := fun _ => generator

theorem programPT06FiniteSpanScalarHessianMinorDensity_scale
    {Rank : Type u} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank) :
    programPT06FiniteSpanScalarHessianMinorDensityEvaluation
        (programPT06FiniteSpanScalarHessianMinorScale scalar data) =
      scalar • programPT06FiniteSpanScalarHessianMinorDensityEvaluation data := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorDensityEvaluation,
    programPT06FiniteSpanScalarHessianMinorScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rank _
  ring

theorem programPT06FiniteSpanScalarHessianMinorCurrent_scale
    {Rank : Type u} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSpanScalarHessianMinorData4D Rank)
    (direction : Fin 3) :
    programPT06FiniteSpanScalarHessianMinorCurrentComponent
        (programPT06FiniteSpanScalarHessianMinorScale scalar data) direction =
      scalar •
        programPT06FiniteSpanScalarHessianMinorCurrentComponent
          data direction := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorCurrentComponent,
    programPT06FiniteSpanScalarHessianMinorScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rank _
  ring

theorem programPT06FiniteSpanScalarHessianMinorDensity_add
    {LeftRank : Type u} [Fintype LeftRank]
    {RightRank : Type v} [Fintype RightRank]
    (left : ProgramPT06FiniteSpanScalarHessianMinorData4D LeftRank)
    (right : ProgramPT06FiniteSpanScalarHessianMinorData4D RightRank) :
    programPT06FiniteSpanScalarHessianMinorDensityEvaluation
        (programPT06FiniteSpanScalarHessianMinorAdd left right) =
      programPT06FiniteSpanScalarHessianMinorDensityEvaluation left +
        programPT06FiniteSpanScalarHessianMinorDensityEvaluation right := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorDensityEvaluation,
    programPT06FiniteSpanScalarHessianMinorAdd, Fintype.sum_sum_type]

theorem programPT06FiniteSpanScalarHessianMinorCurrent_add
    {LeftRank : Type u} [Fintype LeftRank]
    {RightRank : Type v} [Fintype RightRank]
    (left : ProgramPT06FiniteSpanScalarHessianMinorData4D LeftRank)
    (right : ProgramPT06FiniteSpanScalarHessianMinorData4D RightRank)
    (direction : Fin 3) :
    programPT06FiniteSpanScalarHessianMinorCurrentComponent
        (programPT06FiniteSpanScalarHessianMinorAdd left right) direction =
      programPT06FiniteSpanScalarHessianMinorCurrentComponent left direction +
        programPT06FiniteSpanScalarHessianMinorCurrentComponent
          right direction := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorCurrentComponent,
    programPT06FiniteSpanScalarHessianMinorAdd, Fintype.sum_sum_type]

@[simp] theorem programPT06FiniteSpanScalarHessianMinorDensity_ofGenerator
    (generator : ProgramPT06ScalarHessianMinor4D) :
    programPT06FiniteSpanScalarHessianMinorDensityEvaluation
        (programPT06FiniteSpanScalarHessianMinorOfGenerator generator) =
      programPT06ScalarHessianMinorDensityEvaluation generator := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorDensityEvaluation,
    programPT06FiniteSpanScalarHessianMinorOfGenerator]

@[simp] theorem programPT06FiniteSpanScalarHessianMinorCurrent_ofGenerator
    (generator : ProgramPT06ScalarHessianMinor4D) (direction : Fin 3) :
    programPT06FiniteSpanScalarHessianMinorCurrentComponent
        (programPT06FiniteSpanScalarHessianMinorOfGenerator generator)
        direction =
      programPT06ScalarHessianMinorCurrentComponent generator direction := by
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorCurrentComponent,
    programPT06FiniteSpanScalarHessianMinorOfGenerator]

@[simp] theorem programPT06FiniteSpanScalarHessianMinorDivergence_ofGenerator
    (generator : ProgramPT06ScalarHessianMinor4D) :
    programPT06FiniteSpanScalarHessianMinorCurrentDivergence
        (programPT06FiniteSpanScalarHessianMinorOfGenerator generator) =
      programPT06ScalarHessianMinorCurrentDH generator := by
  rw [programPT06FiniteSpanScalarHessianMinorCurrentDivergence_eq_sum]
  funext jet
  simp [programPT06FiniteSpanScalarHessianMinorOfGenerator,
    programPT06ScalarHessianMinorCurrentDivergence_eq_currentDH]

end
end P0EFTJanusProgramPT06FiniteSpanScalarHessianMinorNullLagrangian4D
end JanusFormal
