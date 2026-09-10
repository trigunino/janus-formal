import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

/-!
# Euler soundness for regular C2 first-order currents

This gate extends the value-only current of Gate897 to a scalar current
component depending on the full genuine first jet.  Its horizontal boundary
is the actual Gate879 total derivative, and its chain-rule density is proved
from the supplied Frechet derivative.

For a first-jet current, Gate880 differentiates parts of its boundary twice.
Consequently a bare `C2` certificate is not enough for Mathlib's pointwise,
totalized `fderiv`: the needed third derivatives may fail to exist.  The
additional Cartan regularity structure below records exactly the two
higher-order chain-rule contractions and commutation of the relevant mixed
total derivatives.  Under these explicit hypotheses, Hessian symmetry and
mixed-total-derivative commutation prove that the Euler expression vanishes.

The result is directed (one horizontal component at a time), but that
component may depend on every value and first-derivative coordinate.  It does
not construct the Cartan certificate from a `C3` hypothesis or classify the
full Euler kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06C2FirstOrderCurrentEulerSoundness4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A scalar function on the full first jet with certified first and second
Frechet derivatives. -/
structure ProgramPT06C2FirstOrderCurrentComponent4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  value : ThroatSpatialMultiindexJet1 Fiber -> Real
  gradient : ThroatSpatialMultiindexJet1 Fiber ->
    (ThroatSpatialMultiindexJet1 Fiber →L[Real] Real)
  hessian : ThroatSpatialMultiindexJet1 Fiber ->
    (ThroatSpatialMultiindexJet1 Fiber →L[Real]
      (ThroatSpatialMultiindexJet1 Fiber →L[Real] Real))
  value_hasFDerivAt : forall jet,
    HasFDerivAt value (gradient jet) jet
  gradient_hasFDerivAt : forall jet,
    HasFDerivAt gradient (hessian jet) jet
  hessian_symmetric : forall jet first second,
    hessian jet first second = hessian jet second first

/-- Every globally `C2` first-jet scalar function supplies the preceding
certificate through its actual Frechet derivatives. -/
def programPT06C2FirstOrderCurrentComponentOfContDiff
    (value : FirstJet (Fiber := Fiber) -> Real)
    (hValue : ContDiff Real 2 value) :
    ProgramPT06C2FirstOrderCurrentComponent4D Fiber where
  value := value
  gradient := fderiv Real value
  hessian := fderiv Real (fderiv Real value)
  value_hasFDerivAt := fun jet =>
    (hValue.differentiable (by norm_num) jet).hasFDerivAt
  gradient_hasFDerivAt := fun jet =>
    ((hValue.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) jet).hasFDerivAt
  hessian_symmetric := fun jet first second =>
    second_derivative_symmetric
      (fun point => (hValue.differentiable (by norm_num) point).hasFDerivAt)
      (((hValue.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) jet).hasFDerivAt)
      first second

/-- One full first-jet current component placed in a selected horizontal
direction. -/
structure ProgramPT06DirectedC2FirstOrderCurrent4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  direction : Fin 3
  component : ProgramPT06C2FirstOrderCurrentComponent4D Fiber

/-- Continuous linear truncation from second to first jets. -/
private def firstJetTruncation :
    SecondJet (Fiber := Fiber) →L[Real] FirstJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index =>
    (ContinuousLinearMap.proj
      (show ThroatSpatialTruncatedIndex 2 from
        ⟨index.1, index.2.trans (by omega)⟩) :
      SecondJet (Fiber := Fiber) →L[Real] Fiber)

@[simp] private theorem firstJetTruncation_apply
    (jet : SecondJet (Fiber := Fiber)) :
    firstJetTruncation (Fiber := Fiber) jet =
      truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet := by
  rfl

/-- Continuous linear total-derivative shift from second to first jets. -/
private def firstJetTotalShift (direction : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] FirstJet (Fiber := Fiber) :=
  programPT06FirstTotalDerivativeContinuousLinearMap direction

@[simp] private theorem firstJetTotalShift_apply
    (direction : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    firstJetTotalShift (Fiber := Fiber) direction jet =
      throatSpatialTotalDerivative direction jet := by
  exact programPT06FirstTotalDerivativeContinuousLinearMap_apply direction jet

/-- The genuine Gate879 horizontal derivative of the directed component. -/
def programPT06DirectedC2FirstOrderCurrentDivergence
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) -> Real :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative
    current.direction current.component.value

/-- Explicit chain-rule evaluation of the same density. -/
def programPT06DirectedC2FirstOrderDensityEvaluation
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet =>
    current.component.gradient (firstJetTruncation (Fiber := Fiber) jet)
      (firstJetTotalShift (Fiber := Fiber) current.direction jet)

/-- The explicit density is the true Gate879 total derivative. -/
theorem programPT06DirectedC2FirstOrderCurrentDivergence_eq_density
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) :
    programPT06DirectedC2FirstOrderCurrentDivergence current =
      programPT06DirectedC2FirstOrderDensityEvaluation current := by
  funext jet
  rw [programPT06DirectedC2FirstOrderCurrentDivergence,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
      current.direction current.component.value jet
      (current.component.gradient
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))
      (current.component.value_hasFDerivAt
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))]
  rfl

private def programPT06DirectedC2FirstOrderDensityDerivative
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  (ContinuousLinearMap.apply Real Real
      (firstJetTotalShift (Fiber := Fiber) current.direction jet)).comp
        ((current.component.hessian
          (firstJetTruncation (Fiber := Fiber) jet)).comp
            (firstJetTruncation (Fiber := Fiber))) +
    (current.component.gradient
      (firstJetTruncation (Fiber := Fiber) jet)).comp
        (firstJetTotalShift (Fiber := Fiber) current.direction)

private theorem programPT06DirectedC2FirstOrderGradientOnSecondJet_hasFDerivAt
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (fun candidate : SecondJet (Fiber := Fiber) =>
        current.component.gradient
          (firstJetTruncation (Fiber := Fiber) candidate))
      ((current.component.hessian
        (firstJetTruncation (Fiber := Fiber) jet)).comp
          (firstJetTruncation (Fiber := Fiber))) jet := by
  exact (current.component.gradient_hasFDerivAt
    (firstJetTruncation (Fiber := Fiber) jet)).comp jet
      (firstJetTruncation (Fiber := Fiber)).hasFDerivAt

/-- The chain-rule density has the derivative forced by the current's
certified Hessian. -/
theorem programPT06DirectedC2FirstOrderDensityEvaluation_hasFDerivAt
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06DirectedC2FirstOrderDensityEvaluation current)
      (programPT06DirectedC2FirstOrderDensityDerivative current jet) jet := by
  have hRaw :=
    (programPT06DirectedC2FirstOrderGradientOnSecondJet_hasFDerivAt
      current jet).clm_apply
        ((firstJetTotalShift (Fiber := Fiber)
          current.direction).hasFDerivAt (x := jet))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06DirectedC2FirstOrderDensityDerivative]
  abel

/-- First-jet variation induced by the second-jet value slot.  Defining it
through truncation avoids any choice of coordinates. -/
def programPT06FirstJetValueInjection :
    Fiber →L[Real] FirstJet (Fiber := Fiber) :=
  (firstJetTruncation (Fiber := Fiber)).comp
    (programPT06ThroatSpatialJetCoordinateInjection
      programPT06SecondOrderZeroMultiIndex)

/-- First-jet variation induced by one second-jet first-order slot. -/
def programPT06FirstJetFirstInjection (direction : Fin 3) :
    Fiber →L[Real] FirstJet (Fiber := Fiber) :=
  (firstJetTruncation (Fiber := Fiber)).comp
    (programPT06ThroatSpatialJetCoordinateInjection
      (programPT06SecondOrderFirstMultiIndex direction))

/-- Gradient coefficient of a current in an arbitrary first-jet variation
slot. -/
def programPT06C2FirstOrderCurrentPartial
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (injection : Fiber →L[Real] FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  fun jet => current.component.gradient jet |>.comp injection

/-- Value-slot partial of the current component. -/
def programPT06C2FirstOrderCurrentValuePartial
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) :
    FirstJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  programPT06C2FirstOrderCurrentPartial current
    (programPT06FirstJetValueInjection (Fiber := Fiber))

/-- First-order-slot partial of the current component. -/
def programPT06C2FirstOrderCurrentFirstPartial
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (direction : Fin 3) :
    FirstJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  programPT06C2FirstOrderCurrentPartial current
    (programPT06FirstJetFirstInjection (Fiber := Fiber) direction)

private def programPT06C2FirstOrderCurrentPartialDerivative
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (injection : Fiber →L[Real] FirstJet (Fiber := Fiber))
    (jet : FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  ((ContinuousLinearMap.compL Real Fiber
    (FirstJet (Fiber := Fiber)) Real).flip injection).comp
      (current.component.hessian jet)

private theorem programPT06C2FirstOrderCurrentPartial_hasFDerivAt
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (injection : Fiber →L[Real] FirstJet (Fiber := Fiber))
    (jet : FirstJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06C2FirstOrderCurrentPartial current injection)
      (programPT06C2FirstOrderCurrentPartialDerivative
        current injection jet) jet := by
  have h :=
    ((ContinuousLinearMap.compL Real Fiber
      (FirstJet (Fiber := Fiber)) Real).flip injection).hasFDerivAt.comp jet
        (current.component.gradient_hasFDerivAt jet)
  convert h using 1
  · funext candidate
    rfl
  · rfl

/-- A first-jet gradient coefficient differentiated horizontally once. -/
def programPT06C2FirstOrderCurrentPartialTotalDerivative
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (direction : Fin 3)
    (injection : Fiber →L[Real] FirstJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative direction
    (programPT06C2FirstOrderCurrentPartial current injection)

private theorem programPT06C2FirstOrderCurrentPartialTotalDerivative_formula
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (direction : Fin 3)
    (injection : Fiber →L[Real] FirstJet (Fiber := Fiber))
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06C2FirstOrderCurrentPartialTotalDerivative
        current direction injection jet =
      (current.component.hessian
        (firstJetTruncation (Fiber := Fiber) jet)
        (firstJetTotalShift (Fiber := Fiber) direction jet)).comp injection := by
  rw [programPT06C2FirstOrderCurrentPartialTotalDerivative,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
      direction
      (programPT06C2FirstOrderCurrentPartial current injection) jet
      (programPT06C2FirstOrderCurrentPartialDerivative current injection
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))
      (programPT06C2FirstOrderCurrentPartial_hasFDerivAt current injection
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06C2FirstOrderCurrentPartialDerivative]

/-- Hessian symmetry identifies the density's value vertical partial with
the horizontal derivative of the current's value partial. -/
theorem programPT06DirectedC2FirstOrderDensityVerticalPartialZero
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06DirectedC2FirstOrderDensityEvaluation current) =
      programPT06C2FirstOrderCurrentPartialTotalDerivative
        current current.direction (programPT06FirstJetValueInjection (Fiber := Fiber)) := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedC2FirstOrderDensityEvaluation current) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedC2FirstOrderDensityEvaluation current) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06DirectedC2FirstOrderDensityDerivative current jet)
    (programPT06DirectedC2FirstOrderDensityEvaluation_hasFDerivAt current jet),
    programPT06C2FirstOrderCurrentPartialTotalDerivative_formula]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedC2FirstOrderDensityDerivative,
    programPT06FirstJetValueInjection, current.component.hessian_symmetric]

/-- The mixed total derivative with the selected current direction taken
first. -/
def programPT06C2FirstOrderCurrentMixedTotalLeft
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (direction : Fin 3) :
    ThirdJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative direction
    (programPT06C2FirstOrderCurrentPartialTotalDerivative
      current current.direction
      (programPT06FirstJetFirstInjection (Fiber := Fiber) direction))

/-- The same two total derivatives in the opposite order. -/
def programPT06C2FirstOrderCurrentMixedTotalRight
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (direction : Fin 3) :
    ThirdJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative current.direction
    (programPT06C2FirstOrderCurrentPartialTotalDerivative
      current direction
      (programPT06FirstJetFirstInjection (Fiber := Fiber) direction))

/-- Additional regularity needed by Gate880 beyond a bare `C2` current.

The first two fields are the differentiated Cartan chain rules, including
the symmetric-second-slot weight from Gate880.  The last field is the mixed
total-derivative commutation that cancels the remaining terms.  Smooth
currents are expected to supply these identities, but they are deliberately
not inferred from `C2`, because Gate880 differentiates the boundary twice. -/
structure ProgramPT06DirectedC2FirstOrderCartanRegularity4D
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber) : Prop where
  firstEulerSum : forall jet : FourthJet (Fiber := Fiber),
    (∑ direction : Fin 3,
      programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06DirectedC2FirstOrderDensityEvaluation current)
        direction
        (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
      programPT06C2FirstOrderCurrentPartialTotalDerivative
          current current.direction (programPT06FirstJetValueInjection (Fiber := Fiber))
          (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) +
        ∑ direction : Fin 3,
          programPT06C2FirstOrderCurrentMixedTotalLeft current direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
  secondEulerSum : forall jet : FourthJet (Fiber := Fiber),
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          (programPT06DirectedC2FirstOrderDensityEvaluation current)
          first second jet) =
      ∑ direction : Fin 3,
        programPT06C2FirstOrderCurrentMixedTotalRight current direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
  mixedTotalDerivative_comm : forall direction jet,
    programPT06C2FirstOrderCurrentMixedTotalLeft current direction jet =
      programPT06C2FirstOrderCurrentMixedTotalRight current direction jet

/-- Gate880 soundness for a full first-jet `C2` current carrying the explicit
higher Cartan regularity needed by the pointwise totalized derivative. -/
theorem programPT06SecondOrderLocalEuler_directedC2FirstOrderDensity_eq_zero
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (regularity : ProgramPT06DirectedC2FirstOrderCartanRegularity4D current)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedC2FirstOrderDensityEvaluation current) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06DirectedC2FirstOrderDensityVerticalPartialZero,
    regularity.firstEulerSum, regularity.secondEulerSum]
  have hMixed :
      (∑ direction : Fin 3,
        programPT06C2FirstOrderCurrentMixedTotalLeft current direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
        ∑ direction : Fin 3,
          programPT06C2FirstOrderCurrentMixedTotalRight current direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet) := by
    apply Finset.sum_congr rfl
    intro direction _
    exact regularity.mixedTotalDerivative_comm direction _
  rw [hMixed]
  abel

/-- The same soundness statement for the actual Gate879 horizontal
derivative, rather than its explicit chain-rule presentation. -/
theorem programPT06SecondOrderLocalEuler_directedC2FirstOrderDivergence_eq_zero
    (current : ProgramPT06DirectedC2FirstOrderCurrent4D Fiber)
    (regularity : ProgramPT06DirectedC2FirstOrderCartanRegularity4D current)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedC2FirstOrderCurrentDivergence current) jet = 0 := by
  rw [programPT06DirectedC2FirstOrderCurrentDivergence_eq_density]
  exact programPT06SecondOrderLocalEuler_directedC2FirstOrderDensity_eq_zero
    current regularity jet

end
end P0EFTJanusProgramPT06C2FirstOrderCurrentEulerSoundness4D
end JanusFormal
