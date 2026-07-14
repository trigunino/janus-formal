import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusGaussCodazziBianchiIdentities

namespace JanusFormal
namespace P0EFTJanusCodazziJetExactness

set_option autoImplicit false

noncomputable section

open P0EFTJanusGaussCodazziBianchiIdentities

universe u v w

/-- Pointwise covariant derivative of a symmetric normal-valued second
fundamental form. Symmetry is retained in the final two slots. -/
@[ext]
structure CovariantSecondFundamentalJet
    (Tangent : Type u) (Normal : Type v)
    [AddCommGroup Normal] [Module ℝ Normal] where
  coefficient : Tangent → Tangent → Tangent → Normal
  lastTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient x z y

/-- Fully symmetric normal-valued third-order correction. Algebraically this is
the kernel direction left after alternating `∇B` in its first two indices. -/
@[ext]
structure SymmetricNormalThirdJet
    (Tangent : Type u) (Normal : Type v)
    [AddCommGroup Normal] [Module ℝ Normal] where
  coefficient : Tangent → Tangent → Tangent → Normal
  firstTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient y x z
  lastTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient x z y

/-- Codazzi tensor represented by a covariant second-fundamental-form jet. -/
def codazziTensor
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    Tangent → Tangent → Tangent → Normal :=
  codazziDefect jet.coefficient

/-- Addition of a fully symmetric third-order correction. -/
def applySymmetricThirdJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (gauge : SymmetricNormalThirdJet Tangent Normal)
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    CovariantSecondFundamentalJet Tangent Normal where
  coefficient x y z := jet.coefficient x y z + gauge.coefficient x y z
  lastTwoSymmetric := by
    intro x y z
    change
      jet.coefficient x y z + gauge.coefficient x y z =
        jet.coefficient x z y + gauge.coefficient x z y
    rw [jet.lastTwoSymmetric x y z, gauge.lastTwoSymmetric x y z]

/-- Fully symmetric corrections lie in the kernel of the Codazzi alternation. -/
theorem codazziTensor_applySymmetricThirdJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (gauge : SymmetricNormalThirdJet Tangent Normal)
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    codazziTensor (applySymmetricThirdJet gauge jet) = codazziTensor jet := by
  funext x y z
  change
    (jet.coefficient x y z + gauge.coefficient x y z) -
        (jet.coefficient y x z + gauge.coefficient y x z) =
      jet.coefficient x y z - jet.coefficient y x z
  rw [gauge.firstTwoSymmetric x y z]
  module

/-- Equivalence modulo a fully symmetric normal-valued third jet. -/
def SymmetricThirdEquivalent
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal) : Prop :=
  ∃ gauge : SymmetricNormalThirdJet Tangent Normal,
    applySymmetricThirdJet gauge first = second

/-- Equality of Codazzi tensors makes the difference fully symmetric. -/
def symmetricThirdJetBetweenEqualCodazzi
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal)
    (hCodazzi : codazziTensor first = codazziTensor second) :
    SymmetricNormalThirdJet Tangent Normal where
  coefficient x y z := -first.coefficient x y z + second.coefficient x y z
  firstTwoSymmetric := by
    intro x y z
    have hAt := congrFun (congrFun (congrFun hCodazzi x) y) z
    simp only [codazziTensor, codazziDefect] at hAt
    linear_combination (norm := module) -hAt
  lastTwoSymmetric := by
    intro x y z
    rw [first.lastTwoSymmetric x y z, second.lastTwoSymmetric x y z]

/-- The difference correction maps the first `∇B` jet to the second. -/
theorem symmetricThirdJetBetweenEqualCodazzi_maps
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal)
    (hCodazzi : codazziTensor first = codazziTensor second) :
    applySymmetricThirdJet
        (symmetricThirdJetBetweenEqualCodazzi first second hCodazzi)
        first = second := by
  apply CovariantSecondFundamentalJet.ext
  funext x y z
  simp only [applySymmetricThirdJet, symmetricThirdJetBetweenEqualCodazzi]
  module

/-- Exact kernel theorem for the Codazzi alternation. -/
theorem symmetricThirdEquivalent_iff_codazziTensor_eq
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal) :
    SymmetricThirdEquivalent first second ↔
      codazziTensor first = codazziTensor second := by
  constructor
  · rintro ⟨gauge, hGauge⟩
    calc
      codazziTensor first =
          codazziTensor (applySymmetricThirdJet gauge first) :=
        (codazziTensor_applySymmetricThirdJet gauge first).symm
      _ = codazziTensor second := congrArg codazziTensor hGauge
  · intro hCodazzi
    exact
      ⟨symmetricThirdJetBetweenEqualCodazzi first second hCodazzi,
        symmetricThirdJetBetweenEqualCodazzi_maps first second hCodazzi⟩

/-- Intrinsic target of the Codazzi alternation: skew in the first two slots and
cyclically closed. -/
@[ext]
structure ClosedCodazziTensor
    (Tangent : Type u) (Normal : Type v)
    [AddCommGroup Normal] [Module ℝ Normal] where
  tensor : Tangent → Tangent → Tangent → Normal
  skewFirst : ∀ x y z, tensor y x z = -tensor x y z
  cyclic : ∀ x y z,
    tensor x y z + tensor y z x + tensor z x y = 0

/-- Reduction to the closed Codazzi tensor. -/
def reduceCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    ClosedCodazziTensor Tangent Normal where
  tensor := codazziTensor jet
  skewFirst := by
    intro x y z
    exact codazziDefect_swap_first jet.coefficient x y z
  cyclic := by
    intro x y z
    exact codazziDefect_cyclic_zero
      jet.coefficient jet.lastTwoSymmetric x y z

/-- Algebraic Poincaré section for the Codazzi alternation. -/
def canonicalCovariantSecondFundamentalJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (data : ClosedCodazziTensor Tangent Normal) :
    CovariantSecondFundamentalJet Tangent Normal where
  coefficient x y z :=
    (1 / 3 : ℝ) • (data.tensor x y z + data.tensor x z y)
  lastTwoSymmetric := by
    intro x y z
    module

/-- The canonical `∇B` jet has exactly the prescribed closed Codazzi tensor. -/
theorem codazziTensor_canonical
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (data : ClosedCodazziTensor Tangent Normal) :
    codazziTensor (canonicalCovariantSecondFundamentalJet data) = data.tensor := by
  funext x y z
  change
    (1 / 3 : ℝ) • (data.tensor x y z + data.tensor x z y) -
        (1 / 3 : ℝ) • (data.tensor y x z + data.tensor y z x) =
      data.tensor x y z
  rw [data.skewFirst z x y, data.skewFirst x y z]
  have hCyclic := data.cyclic x y z
  linear_combination (norm := module) (-1 / 3 : ℝ) • hCyclic

/-- The canonical section is a right inverse of the Codazzi reduction. -/
theorem reduceCodazziJet_canonical
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (data : ClosedCodazziTensor Tangent Normal) :
    reduceCodazziJet (canonicalCovariantSecondFundamentalJet data) = data := by
  apply ClosedCodazziTensor.ext
  exact codazziTensor_canonical data

/-- Fibers of the Codazzi reduction are exactly fully symmetric third-jet
orbits. -/
theorem symmetricThirdEquivalent_iff_reduceCodazziJet_eq
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal) :
    SymmetricThirdEquivalent first second ↔
      reduceCodazziJet first = reduceCodazziJet second := by
  rw [symmetricThirdEquivalent_iff_codazziTensor_eq]
  constructor
  · intro hCodazzi
    apply ClosedCodazziTensor.ext
    exact hCodazzi
  · intro hReduced
    exact congrArg ClosedCodazziTensor.tensor hReduced

/-- Every `∇B` jet is equivalent to the canonical section of its closed Codazzi
tensor. -/
theorem equivalent_to_canonicalCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    SymmetricThirdEquivalent jet
      (canonicalCovariantSecondFundamentalJet (reduceCodazziJet jet)) := by
  apply (symmetricThirdEquivalent_iff_reduceCodazziJet_eq _ _).2
  exact (reduceCodazziJet_canonical (reduceCodazziJet jet)).symm

/-- Invariant observable for the Codazzi quotient. -/
def IsSymmetricThirdInvariant
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    {Target : Type w}
    (observable : CovariantSecondFundamentalJet Tangent Normal → Target) : Prop :=
  ∀ first second,
    SymmetricThirdEquivalent first second →
      observable first = observable second

/-- Restriction to the canonical closed-Codazzi slice. -/
def reducedObservable
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    {Target : Type w}
    (observable : CovariantSecondFundamentalJet Tangent Normal → Target) :
    ClosedCodazziTensor Tangent Normal → Target :=
  fun data => observable (canonicalCovariantSecondFundamentalJet data)

/-- Universal factorization through the closed Codazzi tensor. -/
theorem invariant_has_unique_closedCodazzi_reduction
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    {Target : Type w}
    (observable : CovariantSecondFundamentalJet Tangent Normal → Target)
    (hInvariant : IsSymmetricThirdInvariant observable) :
    ∃! reduced : ClosedCodazziTensor Tangent Normal → Target,
      ∀ jet, observable jet = reduced (reduceCodazziJet jet) := by
  refine ⟨reducedObservable observable, ?_, ?_⟩
  · intro jet
    exact hInvariant jet
      (canonicalCovariantSecondFundamentalJet (reduceCodazziJet jet))
      (equivalent_to_canonicalCodazziJet jet)
  · intro other hOther
    funext data
    have hAtSlice := hOther (canonicalCovariantSecondFundamentalJet data)
    calc
      other data = other
          (reduceCodazziJet (canonicalCovariantSecondFundamentalJet data)) := by
        rw [reduceCodazziJet_canonical]
      _ = observable (canonicalCovariantSecondFundamentalJet data) :=
        hAtSlice.symm
      _ = reducedObservable observable data := rfl

/-- Exact boundary after the low-order Codazzi Spencer quotient. -/
structure CodazziJetExactnessStatus where
  covariantSecondFundamentalJetsDefined : Prop
  symmetricThirdKernelDefined : Prop
  codazziAlternationKernelClassified : Prop
  codazziCyclicNecessityProved : Prop
  algebraicPoincareSectionConstructed : Prop
  codazziCyclicSufficiencyProved : Prop
  quotientUniversalPropertyProved : Prop
  actualCovariantDerivativeOfBInserted : Prop
  ambientNormalCurvatureInserted : Prop
  smoothJetBundleConstructed : Prop
  higherSpencerExactnessProved : Prop

/-- Closure of the geometric Codazzi-jet stage. -/
def codazziJetExactnessClosed
    (s : CodazziJetExactnessStatus) : Prop :=
  s.covariantSecondFundamentalJetsDefined /\
  s.symmetricThirdKernelDefined /\
  s.codazziAlternationKernelClassified /\
  s.codazziCyclicNecessityProved /\
  s.algebraicPoincareSectionConstructed /\
  s.codazziCyclicSufficiencyProved /\
  s.quotientUniversalPropertyProved /\
  s.actualCovariantDerivativeOfBInserted /\
  s.ambientNormalCurvatureInserted /\
  s.smoothJetBundleConstructed /\
  s.higherSpencerExactnessProved

/-- Algebraic exactness does not identify the tensor with the genuine covariant
derivative of the Janus second fundamental form. -/
theorem missing_geometric_covariantDerivative_blocks_codazzi_stage
    (s : CodazziJetExactnessStatus)
    (hMissing : Not s.actualCovariantDerivativeOfBInserted) :
    Not (codazziJetExactnessClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusCodazziJetExactness
end JanusFormal
