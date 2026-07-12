import Mathlib

namespace JanusFormal
namespace P0EFTJanusGaussCodazziHelmholtzBridge

set_option autoImplicit false

/-- Residuals of the four standard compatibility identities for immersion jets. -/
@[ext] structure GeometricCompatibilityResiduals where
  gauss : ℝ
  codazzi : ℝ
  ricci : ℝ
  bianchi : ℝ

/-- All geometric compatibility identities hold. -/
def GeometricallyCompatible
    (residuals : GeometricCompatibilityResiduals) : Prop :=
  residuals.gauss = 0 /\
  residuals.codazzi = 0 /\
  residuals.ricci = 0 /\
  residuals.bianchi = 0

/-- Two-sector linearized equation operator. -/
@[ext] structure TwoSectorLinearization where
  xx : ℝ
  xy : ℝ
  yx : ℝ
  yy : ℝ

/-- Finite-dimensional Helmholtz reciprocity condition. -/
def HelmholtzReciprocal
    (operator : TwoSectorLinearization) : Prop :=
  operator.xy = operator.yx

/-- A compatible geometric jet together with an independently chosen response. -/
structure CompatibleJetOperatorCandidate where
  residuals : GeometricCompatibilityResiduals
  linearization : TwoSectorLinearization

/-- Completely compatible geometric residuals. -/
def zeroCompatibilityResiduals : GeometricCompatibilityResiduals :=
  { gauss := 0
    codazzi := 0
    ricci := 0
    bianchi := 0 }

/-- A deliberately nonreciprocal linearized response. -/
def nonHelmholtzLinearization : TwoSectorLinearization :=
  { xx := 1
    xy := 1
    yx := 0
    yy := 1 }

/-- Countermodel to the unqualified P.E.1 implication. -/
def compatibleNonVariationalCandidate :
    CompatibleJetOperatorCandidate :=
  { residuals := zeroCompatibilityResiduals
    linearization := nonHelmholtzLinearization }

/-- The geometric identities all hold in the countermodel. -/
theorem countermodel_geometrically_compatible :
    GeometricallyCompatible
      compatibleNonVariationalCandidate.residuals := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Its linearized response nevertheless fails Helmholtz reciprocity. -/
theorem countermodel_not_helmholtz :
    Not (HelmholtzReciprocal
      compatibleNonVariationalCandidate.linearization) := by
  norm_num [HelmholtzReciprocal,
    compatibleNonVariationalCandidate,
    nonHelmholtzLinearization]

/--
Therefore Gauss--Codazzi--Ricci--Bianchi compatibility does not, by itself,
imply that an independently chosen linearized equation operator is variational.
-/
theorem geometric_compatibility_alone_does_not_imply_helmholtz :
    Exists fun candidate : CompatibleJetOperatorCandidate =>
      GeometricallyCompatible candidate.residuals /\
      Not (HelmholtzReciprocal candidate.linearization) := by
  exact ⟨compatibleNonVariationalCandidate,
    countermodel_geometrically_compatible,
    countermodel_not_helmholtz⟩

/--
Abstract Green pairing for a constrained linearized field theory.  The value
`pairedLinearization first second` represents the integrated pairing
`<first, J second>`.
-/
structure ConstraintGeneratedHelmholtzBridge
    (Variation Constraint : Type*)
    [Zero Constraint] where
  compatibility : Variation → Constraint
  pairedLinearization : Variation → Variation → ℝ
  constraintTransgression : Constraint → Variation → ℝ
  boundaryFlux : Variation → Variation → ℝ
  transgressionAtZero :
    ∀ variation,
      constraintTransgression 0 variation = 0
  defectFactorization :
    ∀ first second,
      pairedLinearization first second -
          pairedLinearization second first =
        constraintTransgression (compatibility first) second -
          constraintTransgression (compatibility second) first +
          boundaryFlux first second

/-- Linearized variation tangent to the compatible-jet locus. -/
def IsCompatibleVariation
    {Variation Constraint : Type*}
    [Zero Constraint]
    (bridge : ConstraintGeneratedHelmholtzBridge Variation Constraint)
    (variation : Variation) : Prop :=
  bridge.compatibility variation = 0

/-- Pair of variations obeying a domain condition that kills the Green boundary term. -/
def BoundaryFluxVanishes
    {Variation Constraint : Type*}
    [Zero Constraint]
    (bridge : ConstraintGeneratedHelmholtzBridge Variation Constraint)
    (first second : Variation) : Prop :=
  bridge.boundaryFlux first second = 0

/-- Restricted Helmholtz symmetry on compatible variations. -/
def RestrictedHelmholtz
    {Variation Constraint : Type*}
    [Zero Constraint]
    (bridge : ConstraintGeneratedHelmholtzBridge Variation Constraint) : Prop :=
  ∀ first second,
    IsCompatibleVariation bridge first →
    IsCompatibleVariation bridge second →
    BoundaryFluxVanishes bridge first second →
      bridge.pairedLinearization first second =
        bridge.pairedLinearization second first

/--
Corrected P.E.1 lemma: if the antisymmetric Helmholtz defect factors through the
linearized compatibility operator, modulo a boundary flux, then the operator is
formally self-adjoint on compatible variations and a boundary-compatible domain.
-/
theorem compatibility_generated_defect_implies_restricted_helmholtz
    {Variation Constraint : Type*}
    [Zero Constraint]
    (bridge : ConstraintGeneratedHelmholtzBridge Variation Constraint) :
    RestrictedHelmholtz bridge := by
  intro first second hFirst hSecond hBoundary
  have hDefect := bridge.defectFactorization first second
  rw [hFirst, hSecond,
    bridge.transgressionAtZero,
    bridge.transgressionAtZero,
    hBoundary] at hDefect
  linarith

/-- Two-component variation used to exhibit a nontrivial constrained bridge. -/
@[ext] structure Variation2 where
  first : ℝ
  second : ℝ

/-- Pairing with the globally nonreciprocal matrix `[[1,1],[0,1]]`. -/
def badMatrixPairing
    (left right : Variation2) : ℝ :=
  left.first * (right.first + right.second) +
    left.second * right.second

/-- Compatibility map; admissible variations satisfy `first = 0`. -/
def exampleCompatibility
    (variation : Variation2) : ℝ :=
  variation.first

/-- Transgression generating the antisymmetric defect. -/
def exampleTransgression
    (constraint : ℝ)
    (variation : Variation2) : ℝ :=
  constraint * variation.second

/-- Closed/periodic boundary model. -/
def zeroBoundaryFlux
    (_first _second : Variation2) : ℝ :=
  0

/-- Explicit factorization of the nonreciprocal defect through the constraint. -/
def constrainedNonreciprocalBridge :
    ConstraintGeneratedHelmholtzBridge Variation2 ℝ where
  compatibility := exampleCompatibility
  pairedLinearization := badMatrixPairing
  constraintTransgression := exampleTransgression
  boundaryFlux := zeroBoundaryFlux
  transgressionAtZero := by
    intro variation
    simp [exampleTransgression]
  defectFactorization := by
    intro first second
    rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    simp [badMatrixPairing, exampleCompatibility,
      exampleTransgression, zeroBoundaryFlux]
    ring

/-- Globally, the example matrix is not Helmholtz reciprocal. -/
theorem example_globally_nonreciprocal :
    badMatrixPairing
        { first := 1, second := 0 }
        { first := 0, second := 1 } ≠
      badMatrixPairing
        { first := 0, second := 1 }
        { first := 1, second := 0 } := by
  norm_num [badMatrixPairing]

/-- On the compatibility kernel, the same response is symmetric. -/
theorem example_restricted_helmholtz :
    RestrictedHelmholtz constrainedNonreciprocalBridge :=
  compatibility_generated_defect_implies_restricted_helmholtz
    constrainedNonreciprocalBridge

/-- Direct pointwise statement for the explicit compatibility kernel. -/
theorem example_pairing_symmetric_on_compatible_variations
    (first second : Variation2)
    (hFirst : first.first = 0)
    (hSecond : second.first = 0) :
    badMatrixPairing first second =
      badMatrixPairing second first := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp at hFirst hSecond
  subst firstX
  subst secondX
  simp [badMatrixPairing]

/--
Geometric/PDE obligations needed to apply the corrected lemma to the actual
Janus immersion family.
-/
structure JanusPE1PhysicalStatus where
  constrainedImmersionJetBundleConstructed : Prop
  gaussCodazziRicciBianchiMapConstructed : Prop
  compatibilityMapLinearized : Prop
  naturalEulerOperatorConstructed : Prop
  greenPairingAndFormalAdjointConstructed : Prop
  antisymmetricDefectComputed : Prop
  defectFactorsThroughCompatibilityIdeal : Prop
  residualBoundaryFluxIdentified : Prop
  physicalDomainKillsBoundaryFlux : Prop
  restrictedFormalSelfAdjointnessProved : Prop
  nonlinearHelmholtzConditionsStillRequired : Prop


def janusPE1PhysicalClosure
    (s : JanusPE1PhysicalStatus) : Prop :=
  s.constrainedImmersionJetBundleConstructed /\
  s.gaussCodazziRicciBianchiMapConstructed /\
  s.compatibilityMapLinearized /\
  s.naturalEulerOperatorConstructed /\
  s.greenPairingAndFormalAdjointConstructed /\
  s.antisymmetricDefectComputed /\
  s.defectFactorsThroughCompatibilityIdeal /\
  s.residualBoundaryFluxIdentified /\
  s.physicalDomainKillsBoundaryFlux /\
  s.restrictedFormalSelfAdjointnessProved /\
  s.nonlinearHelmholtzConditionsStillRequired

/--
Final P.E.1 verdict:

* the unqualified implication `GCRB => Helmholtz` is false;
* the sharp bridge is a factorization theorem for the antisymmetric defect
  through the linearized compatibility map, modulo boundary flux;
* this yields only restricted linearized Helmholtz symmetry.  Full nonlinear
  variational reconstruction still requires the variational bicomplex/Helmholtz
  conditions of Program P-C.
-/
structure PE1Verdict where
  unqualifiedImplicationRefuted : Prop
  constrainedDefectFactorizationSufficient : Prop
  boundaryDomainRequired : Prop
  restrictedNotGlobalSelfAdjointness : Prop
  nonlinearHelmholtzStillIndependent : Prop


def pe1VerdictClosed (s : PE1Verdict) : Prop :=
  s.unqualifiedImplicationRefuted /\
  s.constrainedDefectFactorizationSufficient /\
  s.boundaryDomainRequired /\
  s.restrictedNotGlobalSelfAdjointness /\
  s.nonlinearHelmholtzStillIndependent

end P0EFTJanusGaussCodazziHelmholtzBridge
end JanusFormal
