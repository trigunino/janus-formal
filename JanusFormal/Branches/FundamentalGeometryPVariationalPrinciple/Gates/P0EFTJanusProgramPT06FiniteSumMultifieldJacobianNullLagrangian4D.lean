import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MultifieldJacobianMinorNullLagrangian4D

/-!
# Finite sums of multifield Jacobian-minor null Lagrangians

This gate takes a finite family of Gate912 oriented Jacobian minors and real
coefficients.  Its density and its order-one current are the corresponding
finite weighted sums.  Linearity of the genuine Gate879 total derivative,
proved here from the certified differentiability of the summands, identifies
the current divergence with the density.  The same finite-sum calculation at
the vertical and total derivatives transports Gate912's direct cancellation
to the genuine Gate880 Euler operator.

Disjoint union, coefficient scaling, and the one-point family give addition,
scalar multiplication, and an embedding of every Gate912 generator.  Thus the
construction covers the finite real span of the displayed rank-two minors.
It is not a classification of all first-order null Lagrangians or of the full
polynomial Euler kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FiniteSumMultifieldJacobianNullLagrangian4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06MultifieldJacobianMinorNullLagrangian4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v w z

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A finite weighted family of Gate912 oriented Jacobian minors. -/
structure ProgramPT06FiniteSumMultifieldJacobianData4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber] (Rank : Type v) where
  coefficient : Rank -> Real
  generator : Rank -> ProgramPT06MultifieldJacobianMinorData4D Fiber

omit [FiniteDimensional Real Fiber] in
private theorem localFunctionTotalDerivative_fintype_sum_const_smul
    {Rank : Type v} [Fintype Rank]
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

omit [FiniteDimensional Real Fiber] in
private theorem verticalPartialDerivative_fintype_sum_const_smul
    {Rank : Type v} [Fintype Rank]
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

/-- The finite weighted sum of the explicit Gate912 current components. -/
def programPT06FiniteSumMultifieldJacobianCurrentComponent
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (direction : Fin 3) : FirstJet (Fiber := Fiber) -> Real :=
  fun jet => ∑ rank : Rank, data.coefficient rank •
    programPT06MultifieldJacobianMinorCurrentComponent
      (data.generator rank) direction jet

/-- The genuine Gate879 divergence of the finite summed current. -/
def programPT06FiniteSumMultifieldJacobianCurrentDivergence
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06FiniteSumMultifieldJacobianCurrentComponent data direction) jet

/-- The finite weighted sum of the Gate912 Jacobian-minor densities. -/
def programPT06FiniteSumMultifieldJacobianDensityEvaluation
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet => ∑ rank : Rank, data.coefficient rank •
    programPT06MultifieldJacobianMinorDensityEvaluation
      (data.generator rank) jet

private theorem programPT06FiniteSumMultifieldJacobianCurrentComponent_differentiable
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06FiniteSumMultifieldJacobianCurrentComponent data direction) := by
  unfold programPT06FiniteSumMultifieldJacobianCurrentComponent
  apply Differentiable.fun_sum (u := Finset.univ)
  intro rank _
  exact
    (programPT06MultifieldJacobianMinorCurrentComponent_differentiable
      (data.generator rank) direction).const_smul (data.coefficient rank)

private theorem programPT06FiniteSumMultifieldJacobianCurrentDivergence_eq_sum
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    programPT06FiniteSumMultifieldJacobianCurrentDivergence data =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06MultifieldJacobianMinorCurrentDivergence
          (data.generator rank) jet := by
  funext jet
  unfold programPT06FiniteSumMultifieldJacobianCurrentDivergence
  have hDirection (direction : Fin 3) :
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (programPT06FiniteSumMultifieldJacobianCurrentComponent
            data direction) jet =
        ∑ rank : Rank, data.coefficient rank •
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (programPT06MultifieldJacobianMinorCurrentComponent
              (data.generator rank) direction) jet := by
    exact localFunctionTotalDerivative_fintype_sum_const_smul
      data.coefficient
      (fun rank => programPT06MultifieldJacobianMinorCurrentComponent
        (data.generator rank) direction)
      (fun rank =>
        programPT06MultifieldJacobianMinorCurrentComponent_differentiable
          (data.generator rank) direction) direction jet
  simp_rw [hDirection]
  calc
    (∑ direction : Fin 3, ∑ rank : Rank, data.coefficient rank •
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06MultifieldJacobianMinorCurrentComponent
          (data.generator rank) direction) jet) =
        ∑ rank : Rank, ∑ direction : Fin 3, data.coefficient rank •
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (programPT06MultifieldJacobianMinorCurrentComponent
              (data.generator rank) direction) jet := by
      rw [Finset.sum_comm]
    _ = ∑ rank : Rank, data.coefficient rank •
        programPT06MultifieldJacobianMinorCurrentDivergence
          (data.generator rank) jet := by
      apply Finset.sum_congr rfl
      intro rank _
      unfold programPT06MultifieldJacobianMinorCurrentDivergence
      rw [Finset.smul_sum]

/-- The genuine Gate879 horizontal differential of the summed current is
exactly the summed Jacobian-minor density. -/
theorem programPT06FiniteSumMultifieldJacobianCurrentDivergence_eq_density
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    programPT06FiniteSumMultifieldJacobianCurrentDivergence data =
      programPT06FiniteSumMultifieldJacobianDensityEvaluation data := by
  rw [programPT06FiniteSumMultifieldJacobianCurrentDivergence_eq_sum]
  funext jet
  simp_rw [programPT06MultifieldJacobianMinorCurrentDivergence_eq_density]
  rfl

private theorem programPT06FiniteSumMultifieldJacobianDensity_differentiable
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    Differentiable Real
      (programPT06FiniteSumMultifieldJacobianDensityEvaluation data) := by
  unfold programPT06FiniteSumMultifieldJacobianDensityEvaluation
  apply Differentiable.fun_sum (u := Finset.univ)
  intro rank _
  exact
    (programPT06MultifieldJacobianMinorDensityEvaluation_differentiable
      (data.generator rank)).const_smul (data.coefficient rank)

private theorem programPT06FiniteSumMultifieldJacobianVerticalPartialOne_eq_sum
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data)
        direction =
      fun jet => ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalVerticalPartialOne
          (programPT06MultifieldJacobianMinorDensityEvaluation
            (data.generator rank)) direction jet := by
  funext jet
  exact verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06MultifieldJacobianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      programPT06MultifieldJacobianMinorDensityEvaluation_differentiable
        (data.generator rank)) jet
    (programPT06SecondOrderFirstMultiIndex direction)

private theorem programPT06FiniteSumMultifieldJacobianVerticalPartialZero_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    programPT06SecondOrderLocalVerticalPartialZero
      (programPT06FiniteSumMultifieldJacobianDensityEvaluation data) = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (fun source => ∑ rank : Rank, data.coefficient rank •
      programPT06MultifieldJacobianMinorDensityEvaluation
        (data.generator rank) source) jet
      programPT06SecondOrderZeroMultiIndex = 0
  rw [verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06MultifieldJacobianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      programPT06MultifieldJacobianMinorDensityEvaluation_differentiable
        (data.generator rank))]
  change (∑ rank : Rank, data.coefficient rank •
    programPT06SecondOrderLocalVerticalPartialZero
      (programPT06MultifieldJacobianMinorDensityEvaluation
        (data.generator rank)) jet) = 0
  simp [programPT06JacobianMinorVerticalPartialZero]

private theorem programPT06FiniteSumMultifieldJacobianVerticalPartialTwo_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data)
        first second = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (fun source => ∑ rank : Rank, data.coefficient rank •
      programPT06MultifieldJacobianMinorDensityEvaluation
        (data.generator rank) source) jet
      (programPT06SecondOrderSecondMultiIndex first second) = 0
  rw [verticalPartialDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06MultifieldJacobianMinorDensityEvaluation
      (data.generator rank))
    (fun rank =>
      programPT06MultifieldJacobianMinorDensityEvaluation_differentiable
        (data.generator rank))]
  change (∑ rank : Rank, data.coefficient rank •
    programPT06SecondOrderLocalVerticalPartialTwo
      (programPT06MultifieldJacobianMinorDensityEvaluation
        (data.generator rank)) first second jet) = 0
  simp [programPT06JacobianMinorVerticalPartialTwo]

private theorem programPT06FiniteSumMultifieldJacobianEulerFirstTerm_eq_sum
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data)
        direction jet =
      ∑ rank : Rank, data.coefficient rank •
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06MultifieldJacobianMinorDensityEvaluation
            (data.generator rank)) direction jet := by
  unfold programPT06SecondOrderLocalEulerFirstTotalTerm
  rw [programPT06FiniteSumMultifieldJacobianVerticalPartialOne_eq_sum]
  exact localFunctionTotalDerivative_fintype_sum_const_smul
    data.coefficient
    (fun rank => programPT06SecondOrderLocalVerticalPartialOne
      (programPT06MultifieldJacobianMinorDensityEvaluation
        (data.generator rank)) direction)
    (fun rank =>
      programPT06JacobianMinorVerticalPartialOne_differentiable
        (data.generator rank) direction) direction jet

private theorem programPT06FiniteSumMultifieldJacobianEulerFirstSum_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (jet : ThirdJet (Fiber := Fiber)) :
    (∑ direction : Fin 3,
      programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data)
        direction jet) = 0 := by
  simp_rw [programPT06FiniteSumMultifieldJacobianEulerFirstTerm_eq_sum]
  calc
    (∑ direction : Fin 3, ∑ rank : Rank, data.coefficient rank •
      programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06MultifieldJacobianMinorDensityEvaluation
          (data.generator rank)) direction jet) =
        ∑ rank : Rank, ∑ direction : Fin 3, data.coefficient rank •
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06MultifieldJacobianMinorDensityEvaluation
              (data.generator rank)) direction jet := by
      rw [Finset.sum_comm]
    _ = ∑ rank : Rank, data.coefficient rank •
        (∑ direction : Fin 3,
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06MultifieldJacobianMinorDensityEvaluation
              (data.generator rank)) direction jet) := by
      apply Finset.sum_congr rfl
      intro rank _
      rw [Finset.smul_sum]
    _ = 0 := by
      simp [programPT06JacobianMinorEulerFirstSum]

private theorem programPT06FiniteSumMultifieldJacobianEulerSecondTerm_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06FiniteSumMultifieldJacobianVerticalPartialTwo_eq_zero]
  simp

/-- Gate880 annihilates every finite real sum of Gate912 minors. -/
theorem programPT06SecondOrderLocalEuler_finiteSumMultifieldJacobian_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteSumMultifieldJacobianDensityEvaluation data) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06FiniteSumMultifieldJacobianVerticalPartialZero_eq_zero,
    programPT06FiniteSumMultifieldJacobianEulerFirstSum_eq_zero]
  simp [programPT06FiniteSumMultifieldJacobianEulerSecondTerm_eq_zero]

/-- Gate880 also annihilates the genuine Gate879 divergence presentation. -/
theorem programPT06SecondOrderLocalEuler_finiteSumMultifieldJacobianDivergence_eq_zero
    {Rank : Type v} [Fintype Rank]
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteSumMultifieldJacobianCurrentDivergence data) jet = 0 := by
  rw [programPT06FiniteSumMultifieldJacobianCurrentDivergence_eq_density]
  exact programPT06SecondOrderLocalEuler_finiteSumMultifieldJacobian_eq_zero
    data jet

/-- Scale all coefficients of a represented finite sum. -/
def programPT06FiniteSumMultifieldJacobianScale
    {Rank : Type v} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank where
  coefficient := fun rank => scalar * data.coefficient rank
  generator := data.generator

/-- Form the sum of two represented families by a disjoint union of ranks. -/
def programPT06FiniteSumMultifieldJacobianAdd
    {LeftRank : Type v} [Fintype LeftRank]
    {RightRank : Type w} [Fintype RightRank]
    (left : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber LeftRank)
    (right : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber RightRank) :
    ProgramPT06FiniteSumMultifieldJacobianData4D Fiber
      (LeftRank ⊕ RightRank) where
  coefficient := Sum.elim left.coefficient right.coefficient
  generator := Sum.elim left.generator right.generator

/-- Embed one Gate912 generator as a one-term finite family. -/
def programPT06FiniteSumMultifieldJacobianOfGenerator
    (generator : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    ProgramPT06FiniteSumMultifieldJacobianData4D Fiber PUnit where
  coefficient := fun _ => 1
  generator := fun _ => generator

/-- Scaling the representation scales its density. -/
theorem programPT06FiniteSumMultifieldJacobianDensity_scale
    {Rank : Type v} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank) :
    programPT06FiniteSumMultifieldJacobianDensityEvaluation
        (programPT06FiniteSumMultifieldJacobianScale scalar data) =
      scalar • programPT06FiniteSumMultifieldJacobianDensityEvaluation data := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianDensityEvaluation,
    programPT06FiniteSumMultifieldJacobianScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rank _
  ring

/-- Scaling the representation scales every current component. -/
theorem programPT06FiniteSumMultifieldJacobianCurrent_scale
    {Rank : Type v} [Fintype Rank] (scalar : Real)
    (data : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber Rank)
    (direction : Fin 3) :
    programPT06FiniteSumMultifieldJacobianCurrentComponent
        (programPT06FiniteSumMultifieldJacobianScale scalar data) direction =
      scalar •
        programPT06FiniteSumMultifieldJacobianCurrentComponent data direction := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianCurrentComponent,
    programPT06FiniteSumMultifieldJacobianScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rank _
  ring

/-- Disjoint-union addition adds the two represented densities. -/
theorem programPT06FiniteSumMultifieldJacobianDensity_add
    {LeftRank : Type v} [Fintype LeftRank]
    {RightRank : Type w} [Fintype RightRank]
    (left : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber LeftRank)
    (right : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber RightRank) :
    programPT06FiniteSumMultifieldJacobianDensityEvaluation
        (programPT06FiniteSumMultifieldJacobianAdd left right) =
      programPT06FiniteSumMultifieldJacobianDensityEvaluation left +
        programPT06FiniteSumMultifieldJacobianDensityEvaluation right := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianDensityEvaluation,
    programPT06FiniteSumMultifieldJacobianAdd, Fintype.sum_sum_type]

/-- Disjoint-union addition adds every represented current component. -/
theorem programPT06FiniteSumMultifieldJacobianCurrent_add
    {LeftRank : Type v} [Fintype LeftRank]
    {RightRank : Type w} [Fintype RightRank]
    (left : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber LeftRank)
    (right : ProgramPT06FiniteSumMultifieldJacobianData4D Fiber RightRank)
    (direction : Fin 3) :
    programPT06FiniteSumMultifieldJacobianCurrentComponent
        (programPT06FiniteSumMultifieldJacobianAdd left right) direction =
      programPT06FiniteSumMultifieldJacobianCurrentComponent left direction +
        programPT06FiniteSumMultifieldJacobianCurrentComponent
          right direction := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianCurrentComponent,
    programPT06FiniteSumMultifieldJacobianAdd, Fintype.sum_sum_type]

/-- The one-point representation recovers its generator density. -/
@[simp] theorem programPT06FiniteSumMultifieldJacobianDensity_ofGenerator
    (generator : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    programPT06FiniteSumMultifieldJacobianDensityEvaluation
        (programPT06FiniteSumMultifieldJacobianOfGenerator generator) =
      programPT06MultifieldJacobianMinorDensityEvaluation generator := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianDensityEvaluation,
    programPT06FiniteSumMultifieldJacobianOfGenerator]

/-- The one-point representation recovers its generator current. -/
@[simp] theorem programPT06FiniteSumMultifieldJacobianCurrent_ofGenerator
    (generator : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) :
    programPT06FiniteSumMultifieldJacobianCurrentComponent
        (programPT06FiniteSumMultifieldJacobianOfGenerator generator) direction =
      programPT06MultifieldJacobianMinorCurrentComponent
        generator direction := by
  funext jet
  simp [programPT06FiniteSumMultifieldJacobianCurrentComponent,
    programPT06FiniteSumMultifieldJacobianOfGenerator]

end
end P0EFTJanusProgramPT06FiniteSumMultifieldJacobianNullLagrangian4D
end JanusFormal
