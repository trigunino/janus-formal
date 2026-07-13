import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusGaussCodazziBianchiIdentities

namespace JanusFormal
namespace P0EFTJanusAbelianConnectionSecondJet

set_option autoImplicit false

noncomputable section

open P0EFTJanusGaussCodazziBianchiIdentities

universe u v

/-- Second derivative of a local abelian connection one-form. The first two
indices are partial-derivative indices, hence are symmetric. -/
@[ext]
structure AbelianConnectionSecondJet (Tangent : Type u) where
  coefficient : Tangent → Tangent → Tangent → ℝ
  mixedSymmetric :
    ∀ x y z, coefficient x y z = coefficient y x z

/-- Third jet of an abelian gauge parameter. The two adjacent transposition
symmetries generate full symmetry of the scalar third derivative. -/
@[ext]
structure AbelianGaugeThirdJet (Tangent : Type u) where
  coefficient : Tangent → Tangent → Tangent → ℝ
  symmetricFirst :
    ∀ x y z, coefficient x y z = coefficient y x z
  symmetricLast :
    ∀ x y z, coefficient x y z = coefficient x z y

/-- First derivative of curvature represented by a connection second jet. -/
def curvatureDerivative
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    Tangent → Tangent → Tangent → ℝ :=
  abelianCurvatureDerivative jet.coefficient

/-- Gauge action at this jet order. -/
def applyGaugeThird
    {Tangent : Type u}
    (gauge : AbelianGaugeThirdJet Tangent)
    (jet : AbelianConnectionSecondJet Tangent) :
    AbelianConnectionSecondJet Tangent where
  coefficient x y z := jet.coefficient x y z + gauge.coefficient x y z
  mixedSymmetric := by
    intro x y z
    change
      jet.coefficient x y z + gauge.coefficient x y z =
        jet.coefficient y x z + gauge.coefficient y x z
    rw [jet.mixedSymmetric x y z, gauge.symmetricFirst x y z]

/-- A fully symmetric gauge third derivative does not change `∇F`. -/
theorem curvatureDerivative_applyGaugeThird
    {Tangent : Type u}
    (gauge : AbelianGaugeThirdJet Tangent)
    (jet : AbelianConnectionSecondJet Tangent) :
    curvatureDerivative (applyGaugeThird gauge jet) =
      curvatureDerivative jet := by
  funext x y z
  change
    (jet.coefficient x y z + gauge.coefficient x y z) -
        (jet.coefficient x z y + gauge.coefficient x z y) =
      jet.coefficient x y z - jet.coefficient x z y
  rw [gauge.symmetricLast x y z]
  ring

/-- Gauge equivalence of connection second jets. -/
def GaugeEquivalent
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) : Prop :=
  ∃ gauge : AbelianGaugeThirdJet Tangent,
    applyGaugeThird gauge first = second

/-- If two connection second jets have equal curvature derivative, their
difference is fully symmetric and is therefore a gauge third jet. -/
def gaugeBetweenEqualCurvatureDerivatives
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent)
    (hCurvature : curvatureDerivative first = curvatureDerivative second) :
    AbelianGaugeThirdJet Tangent where
  coefficient x y z := -first.coefficient x y z + second.coefficient x y z
  symmetricFirst := by
    intro x y z
    rw [first.mixedSymmetric x y z, second.mixedSymmetric x y z]
  symmetricLast := by
    intro x y z
    have hAt := congrFun (congrFun (congrFun hCurvature x) y) z
    simp only [curvatureDerivative, abelianCurvatureDerivative] at hAt
    linarith

/-- The explicit difference gauge maps the first jet to the second. -/
theorem gaugeBetweenEqualCurvatureDerivatives_maps
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent)
    (hCurvature : curvatureDerivative first = curvatureDerivative second) :
    applyGaugeThird
        (gaugeBetweenEqualCurvatureDerivatives first second hCurvature)
        first = second := by
  apply AbelianConnectionSecondJet.ext
  funext x y z
  simp only [applyGaugeThird, gaugeBetweenEqualCurvatureDerivatives]
  ring

/-- Exact second-order gauge quotient: two abelian connection second jets are
gauge equivalent exactly when their first curvature derivatives agree. -/
theorem gaugeEquivalent_iff_curvatureDerivative_eq
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) :
    GaugeEquivalent first second ↔
      curvatureDerivative first = curvatureDerivative second := by
  constructor
  · rintro ⟨gauge, hGauge⟩
    calc
      curvatureDerivative first =
          curvatureDerivative (applyGaugeThird gauge first) :=
        (curvatureDerivative_applyGaugeThird gauge first).symm
      _ = curvatureDerivative second := congrArg curvatureDerivative hGauge
  · intro hCurvature
    exact
      ⟨gaugeBetweenEqualCurvatureDerivatives first second hCurvature,
        gaugeBetweenEqualCurvatureDerivatives_maps first second hCurvature⟩

/-- Intrinsic target of the quotient: a three-tensor skew in its last two slots
and satisfying the abelian Bianchi identity. -/
@[ext]
structure ClosedCurvatureDerivative (Tangent : Type u) where
  tensor : Tangent → Tangent → Tangent → ℝ
  skewLast : ∀ x y z, tensor x z y = -tensor x y z
  cyclic : ∀ x y z,
    tensor x y z + tensor y z x + tensor z x y = 0

/-- Reduction from a connection second jet to its closed curvature derivative. -/
def reduceSecondJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    ClosedCurvatureDerivative Tangent where
  tensor := curvatureDerivative jet
  skewLast := by
    intro x y z
    exact abelianCurvatureDerivative_swap_last jet.coefficient x y z
  cyclic := by
    intro x y z
    exact abelianCurvatureDerivative_cyclic_zero
      jet.coefficient jet.mixedSymmetric x y z

/-- Explicit algebraic Poincaré section. The factor `1/3` reconstructs a
first-pair-symmetric connection second derivative from any closed `∇F`. -/
def canonicalSecondJet
    {Tangent : Type u}
    (data : ClosedCurvatureDerivative Tangent) :
    AbelianConnectionSecondJet Tangent where
  coefficient x y z :=
    (data.tensor x y z + data.tensor y x z) / 3
  mixedSymmetric := by
    intro x y z
    ring

/-- The canonical second jet has exactly the prescribed curvature derivative. -/
theorem curvatureDerivative_canonicalSecondJet
    {Tangent : Type u}
    (data : ClosedCurvatureDerivative Tangent) :
    curvatureDerivative (canonicalSecondJet data) = data.tensor := by
  funext x y z
  change
    (data.tensor x y z + data.tensor y x z) / 3 -
        (data.tensor x z y + data.tensor z x y) / 3 =
      data.tensor x y z
  rw [data.skewLast y z x, data.skewLast x y z]
  have hCyclic := data.cyclic x y z
  linarith

/-- The canonical section is a right inverse of the reduction map. -/
theorem reduceSecondJet_canonicalSecondJet
    {Tangent : Type u}
    (data : ClosedCurvatureDerivative Tangent) :
    reduceSecondJet (canonicalSecondJet data) = data := by
  apply ClosedCurvatureDerivative.ext
  exact curvatureDerivative_canonicalSecondJet data

/-- Fibers of the reduction map are exactly gauge orbits. -/
theorem gaugeEquivalent_iff_reduceSecondJet_eq
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) :
    GaugeEquivalent first second ↔
      reduceSecondJet first = reduceSecondJet second := by
  rw [gaugeEquivalent_iff_curvatureDerivative_eq]
  constructor
  · intro hCurvature
    apply ClosedCurvatureDerivative.ext
    exact hCurvature
  · intro hReduced
    exact congrArg ClosedCurvatureDerivative.tensor hReduced

/-- Every connection second jet is gauge equivalent to the canonical section of
its closed curvature derivative. -/
theorem gaugeEquivalent_to_canonicalSecondJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    GaugeEquivalent jet (canonicalSecondJet (reduceSecondJet jet)) := by
  apply (gaugeEquivalent_iff_reduceSecondJet_eq _ _).2
  exact (reduceSecondJet_canonicalSecondJet (reduceSecondJet jet)).symm

/-- Gauge-invariant observable on connection second jets. -/
def IsGaugeInvariant
    {Tangent : Type u}
    {Target : Type v}
    (observable : AbelianConnectionSecondJet Tangent → Target) : Prop :=
  ∀ first second,
    GaugeEquivalent first second →
      observable first = observable second

/-- Restriction of an observable to the canonical closed-curvature slice. -/
def reducedObservable
    {Tangent : Type u}
    {Target : Type v}
    (observable : AbelianConnectionSecondJet Tangent → Target) :
    ClosedCurvatureDerivative Tangent → Target :=
  fun data => observable (canonicalSecondJet data)

/-- Gauge invariance forces factorization through closed `∇F`. -/
theorem gaugeInvariant_factors_through_closedCurvature
    {Tangent : Type u}
    {Target : Type v}
    (observable : AbelianConnectionSecondJet Tangent → Target)
    (hInvariant : IsGaugeInvariant observable) :
    ∀ jet,
      observable jet = reducedObservable observable (reduceSecondJet jet) := by
  intro jet
  exact hInvariant jet (canonicalSecondJet (reduceSecondJet jet))
    (gaugeEquivalent_to_canonicalSecondJet jet)

/-- Conversely, every function of closed curvature derivatives is gauge
invariant. -/
theorem closedCurvature_factorization_isGaugeInvariant
    {Tangent : Type u}
    {Target : Type v}
    (reduced : ClosedCurvatureDerivative Tangent → Target) :
    IsGaugeInvariant
      (fun jet : AbelianConnectionSecondJet Tangent =>
        reduced (reduceSecondJet jet)) := by
  intro first second hEquivalent
  exact congrArg reduced
    ((gaugeEquivalent_iff_reduceSecondJet_eq first second).1 hEquivalent)

/-- Universal property of the second-order abelian gauge quotient. -/
theorem gaugeInvariant_has_unique_closedCurvature_reduction
    {Tangent : Type u}
    {Target : Type v}
    (observable : AbelianConnectionSecondJet Tangent → Target)
    (hInvariant : IsGaugeInvariant observable) :
    ∃! reduced : ClosedCurvatureDerivative Tangent → Target,
      ∀ jet, observable jet = reduced (reduceSecondJet jet) := by
  refine
    ⟨reducedObservable observable,
      gaugeInvariant_factors_through_closedCurvature observable hInvariant, ?_⟩
  intro other hOther
  funext data
  have hAtSlice := hOther (canonicalSecondJet data)
  calc
    other data = other (reduceSecondJet (canonicalSecondJet data)) := by
      rw [reduceSecondJet_canonicalSecondJet]
    _ = observable (canonicalSecondJet data) := hAtSlice.symm
    _ = reducedObservable observable data := rfl

/-- Exact boundary after closing the abelian second-jet quotient. -/
structure AbelianConnectionSecondJetStatus where
  connectionSecondJetsDefined : Prop
  gaugeThirdJetsDefined : Prop
  curvatureDerivativeGaugeInvariant : Prop
  gaugeOrbitsClassifiedByCurvatureDerivative : Prop
  bianchiNecessaryConditionProved : Prop
  algebraicPoincareSectionConstructed : Prop
  bianchiSufficiencyProved : Prop
  universalInvariantFactorizationProved : Prop
  smoothFiniteDimensionalJetBundlesConstructed : Prop
  determinantLineConnectionInserted : Prop
  higherCovariantJetsClassified : Prop

/-- Closure of the geometric second-order determinant-connection stage. -/
def abelianConnectionSecondJetClosed
    (s : AbelianConnectionSecondJetStatus) : Prop :=
  s.connectionSecondJetsDefined /\
  s.gaugeThirdJetsDefined /\
  s.curvatureDerivativeGaugeInvariant /\
  s.gaugeOrbitsClassifiedByCurvatureDerivative /\
  s.bianchiNecessaryConditionProved /\
  s.algebraicPoincareSectionConstructed /\
  s.bianchiSufficiencyProved /\
  s.universalInvariantFactorizationProved /\
  s.smoothFiniteDimensionalJetBundlesConstructed /\
  s.determinantLineConnectionInserted /\
  s.higherCovariantJetsClassified

/-- The algebraic quotient does not yet insert the actual determinant-line
connection and its smooth jet bundle. -/
theorem missing_determinant_connection_blocks_geometric_stage
    (s : AbelianConnectionSecondJetStatus)
    (hMissing : Not s.determinantLineConnectionInserted) :
    Not (abelianConnectionSecondJetClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusAbelianConnectionSecondJet
end JanusFormal
