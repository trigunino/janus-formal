import Mathlib.Tactic.LinearCombination
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusGaussCodazziBianchiIdentities

namespace JanusFormal
namespace P0EFTJanusAbelianBianchiJetExactness

set_option autoImplicit false

noncomputable section

open P0EFTJanusGaussCodazziBianchiIdentities

universe u w

/-- Pointwise second derivative of a local abelian connection one-form. The first
two slots are partial-derivative indices and therefore commute. -/
@[ext]
structure AbelianConnectionSecondJet (Tangent : Type u) where
  coefficient : Tangent → Tangent → Tangent → ℝ
  firstTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient y x z

/-- Third jet of an abelian gauge parameter. Symmetry in the first and last
adjacent pairs generates full symmetry of its three derivative indices. -/
@[ext]
structure SymmetricScalarThirdJet (Tangent : Type u) where
  coefficient : Tangent → Tangent → Tangent → ℝ
  firstTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient y x z
  lastTwoSymmetric :
    ∀ x y z, coefficient x y z = coefficient x z y

/-- First derivative of the abelian curvature represented by a connection
second jet. -/
def bianchiTensor
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    Tangent → Tangent → Tangent → ℝ :=
  abelianCurvatureDerivative jet.coefficient

/-- Addition of a genuine scalar gauge third jet. -/
def applySymmetricScalarThirdJet
    {Tangent : Type u}
    (gauge : SymmetricScalarThirdJet Tangent)
    (jet : AbelianConnectionSecondJet Tangent) :
    AbelianConnectionSecondJet Tangent where
  coefficient x y z := jet.coefficient x y z + gauge.coefficient x y z
  firstTwoSymmetric := by
    intro x y z
    rw [jet.firstTwoSymmetric x y z, gauge.firstTwoSymmetric x y z]

/-- Fully symmetric gauge third jets leave `∇F` unchanged. -/
theorem bianchiTensor_applySymmetricScalarThirdJet
    {Tangent : Type u}
    (gauge : SymmetricScalarThirdJet Tangent)
    (jet : AbelianConnectionSecondJet Tangent) :
    bianchiTensor (applySymmetricScalarThirdJet gauge jet) =
      bianchiTensor jet := by
  funext x y z
  change
    (jet.coefficient x y z + gauge.coefficient x y z) -
        (jet.coefficient x z y + gauge.coefficient x z y) =
      jet.coefficient x y z - jet.coefficient x z y
  rw [gauge.lastTwoSymmetric x y z]
  ring

/-- Equivalence modulo a fully symmetric scalar gauge third jet. -/
def SymmetricScalarThirdEquivalent
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) : Prop :=
  ∃ gauge : SymmetricScalarThirdJet Tangent,
    applySymmetricScalarThirdJet gauge first = second

/-- Equality of `∇F` tensors makes the difference a fully symmetric third jet. -/
def symmetricScalarThirdJetBetweenEqualBianchi
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent)
    (hBianchi : bianchiTensor first = bianchiTensor second) :
    SymmetricScalarThirdJet Tangent where
  coefficient x y z := -first.coefficient x y z + second.coefficient x y z
  firstTwoSymmetric := by
    intro x y z
    rw [first.firstTwoSymmetric x y z, second.firstTwoSymmetric x y z]
  lastTwoSymmetric := by
    intro x y z
    have hAt := congrFun (congrFun (congrFun hBianchi x) y) z
    simp only [bianchiTensor, abelianCurvatureDerivative] at hAt
    linarith

/-- The difference third jet maps the first connection jet to the second. -/
theorem symmetricScalarThirdJetBetweenEqualBianchi_maps
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent)
    (hBianchi : bianchiTensor first = bianchiTensor second) :
    applySymmetricScalarThirdJet
        (symmetricScalarThirdJetBetweenEqualBianchi first second hBianchi)
        first = second := by
  apply AbelianConnectionSecondJet.ext
  funext x y z
  simp only [applySymmetricScalarThirdJet,
    symmetricScalarThirdJetBetweenEqualBianchi]
  ring

/-- Exact kernel theorem for the abelian Bianchi projection. -/
theorem symmetricScalarThirdEquivalent_iff_bianchiTensor_eq
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) :
    SymmetricScalarThirdEquivalent first second ↔
      bianchiTensor first = bianchiTensor second := by
  constructor
  · rintro ⟨gauge, hGauge⟩
    calc
      bianchiTensor first =
          bianchiTensor (applySymmetricScalarThirdJet gauge first) :=
        (bianchiTensor_applySymmetricScalarThirdJet gauge first).symm
      _ = bianchiTensor second := congrArg bianchiTensor hGauge
  · intro hBianchi
    exact
      ⟨symmetricScalarThirdJetBetweenEqualBianchi first second hBianchi,
        symmetricScalarThirdJetBetweenEqualBianchi_maps
          first second hBianchi⟩

/-- Intrinsic target of the first abelian Bianchi projection: skew in the
curvature slots and closed under cyclic alternation. -/
@[ext]
structure ClosedAbelianBianchiTensor (Tangent : Type u) where
  tensor : Tangent → Tangent → Tangent → ℝ
  skewLast : ∀ x y z, tensor x z y = -tensor x y z
  cyclic : ∀ x y z,
    tensor x y z + tensor y z x + tensor z x y = 0

/-- Reduction from a connection second jet to its closed `∇F` tensor. -/
def reduceAbelianBianchiJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    ClosedAbelianBianchiTensor Tangent where
  tensor := bianchiTensor jet
  skewLast := by
    intro x y z
    exact abelianCurvatureDerivative_swap_last jet.coefficient x y z
  cyclic := by
    intro x y z
    exact abelianCurvatureDerivative_cyclic_zero
      jet.coefficient jet.firstTwoSymmetric x y z

/-- Algebraic Poincaré section of the abelian Bianchi projection. -/
def canonicalAbelianConnectionSecondJet
    {Tangent : Type u}
    (data : ClosedAbelianBianchiTensor Tangent) :
    AbelianConnectionSecondJet Tangent where
  coefficient x y z :=
    (1 / 3 : ℝ) * (data.tensor x y z + data.tensor y x z)
  firstTwoSymmetric := by
    intro x y z
    ring

/-- The canonical connection second jet has precisely the prescribed closed
`∇F` tensor. -/
theorem bianchiTensor_canonical
    {Tangent : Type u}
    (data : ClosedAbelianBianchiTensor Tangent) :
    bianchiTensor (canonicalAbelianConnectionSecondJet data) = data.tensor := by
  funext x y z
  change
    (1 / 3 : ℝ) * (data.tensor x y z + data.tensor y x z) -
        (1 / 3 : ℝ) * (data.tensor x z y + data.tensor z x y) =
      data.tensor x y z
  rw [data.skewLast x y z, data.skewLast y z x]
  have hCyclic := data.cyclic x y z
  linarith

/-- The canonical section is a right inverse of the Bianchi reduction. -/
theorem reduceAbelianBianchiJet_canonical
    {Tangent : Type u}
    (data : ClosedAbelianBianchiTensor Tangent) :
    reduceAbelianBianchiJet (canonicalAbelianConnectionSecondJet data) = data := by
  apply ClosedAbelianBianchiTensor.ext
  exact bianchiTensor_canonical data

/-- Fibers of the Bianchi reduction are exactly symmetric gauge-third-jet
orbits. -/
theorem symmetricScalarThirdEquivalent_iff_reduceAbelianBianchiJet_eq
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) :
    SymmetricScalarThirdEquivalent first second ↔
      reduceAbelianBianchiJet first = reduceAbelianBianchiJet second := by
  rw [symmetricScalarThirdEquivalent_iff_bianchiTensor_eq]
  constructor
  · intro hBianchi
    apply ClosedAbelianBianchiTensor.ext
    exact hBianchi
  · intro hReduced
    exact congrArg ClosedAbelianBianchiTensor.tensor hReduced

/-- Every connection second jet is equivalent to the canonical representative
of its closed `∇F` tensor. -/
theorem equivalent_to_canonicalAbelianBianchiJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    SymmetricScalarThirdEquivalent jet
      (canonicalAbelianConnectionSecondJet
        (reduceAbelianBianchiJet jet)) := by
  apply
    (symmetricScalarThirdEquivalent_iff_reduceAbelianBianchiJet_eq _ _).2
  exact
    (reduceAbelianBianchiJet_canonical (reduceAbelianBianchiJet jet)).symm

/-- Invariance under symmetric scalar third-jet gauge directions. -/
def IsSymmetricScalarThirdInvariant
    {Tangent : Type u} {Target : Type w}
    (observable : AbelianConnectionSecondJet Tangent → Target) : Prop :=
  ∀ first second,
    SymmetricScalarThirdEquivalent first second →
      observable first = observable second

/-- Restriction of an observable to the canonical closed-Bianchi slice. -/
def reducedObservable
    {Tangent : Type u} {Target : Type w}
    (observable : AbelianConnectionSecondJet Tangent → Target) :
    ClosedAbelianBianchiTensor Tangent → Target :=
  fun data => observable (canonicalAbelianConnectionSecondJet data)

/-- Universal property of the abelian Bianchi quotient. -/
theorem invariant_has_unique_closedBianchi_reduction
    {Tangent : Type u} {Target : Type w}
    (observable : AbelianConnectionSecondJet Tangent → Target)
    (hInvariant : IsSymmetricScalarThirdInvariant observable) :
    ∃! reduced : ClosedAbelianBianchiTensor Tangent → Target,
      ∀ jet, observable jet = reduced (reduceAbelianBianchiJet jet) := by
  refine ⟨reducedObservable observable, ?_, ?_⟩
  · intro jet
    exact hInvariant jet
      (canonicalAbelianConnectionSecondJet (reduceAbelianBianchiJet jet))
      (equivalent_to_canonicalAbelianBianchiJet jet)
  · intro other hOther
    funext data
    have hAtSlice := hOther (canonicalAbelianConnectionSecondJet data)
    calc
      other data = other
          (reduceAbelianBianchiJet
            (canonicalAbelianConnectionSecondJet data)) := by
        rw [reduceAbelianBianchiJet_canonical]
      _ = observable (canonicalAbelianConnectionSecondJet data) :=
        hAtSlice.symm
      _ = reducedObservable observable data := rfl

/-- Exact boundary after the first abelian Bianchi Spencer quotient. -/
structure AbelianBianchiJetExactnessStatus where
  connectionSecondJetsDefined : Prop
  symmetricGaugeThirdJetsDefined : Prop
  bianchiProjectionKernelClassified : Prop
  skewAndCyclicNecessityProved : Prop
  algebraicPoincareSectionConstructed : Prop
  skewAndCyclicSufficiencyProved : Prop
  quotientUniversalPropertyProved : Prop
  actualCovariantDerivativeOfCurvatureInserted : Prop
  determinantLineConnectionInserted : Prop
  smoothJetBundleConstructed : Prop
  higherSpencerExactnessProved : Prop

/-- Closure of the geometric determinant-connection Bianchi stage. -/
def abelianBianchiJetExactnessClosed
    (s : AbelianBianchiJetExactnessStatus) : Prop :=
  s.connectionSecondJetsDefined /\
  s.symmetricGaugeThirdJetsDefined /\
  s.bianchiProjectionKernelClassified /\
  s.skewAndCyclicNecessityProved /\
  s.algebraicPoincareSectionConstructed /\
  s.skewAndCyclicSufficiencyProved /\
  s.quotientUniversalPropertyProved /\
  s.actualCovariantDerivativeOfCurvatureInserted /\
  s.determinantLineConnectionInserted /\
  s.smoothJetBundleConstructed /\
  s.higherSpencerExactnessProved

/-- Algebraic exactness does not yet identify this jet with the covariant
derivative of the actual SpinC determinant-line curvature. -/
theorem missing_determinant_connection_blocks_bianchi_stage
    (s : AbelianBianchiJetExactnessStatus)
    (hMissing : Not s.determinantLineConnectionInserted) :
    Not (abelianBianchiJetExactnessClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusAbelianBianchiJetExactness
end JanusFormal
