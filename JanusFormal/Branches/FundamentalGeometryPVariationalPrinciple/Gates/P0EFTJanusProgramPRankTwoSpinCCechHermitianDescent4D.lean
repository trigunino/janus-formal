import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRankTwoSpinCHermitianClassification4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanGlobalSpinCJetRealization

/-! # Rank-two SpinC Cech Hermitian descent -/

namespace JanusFormal
namespace P0EFTJanusProgramPRankTwoSpinCCechHermitianDescent4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D
open P0EFTJanusProgramPRankTwoSpinCHermitianClassification4D
open P0EFTJanusCliffordSpin2DoubleCover
open P0EFTJanusEuclideanGlobalSpinCJetRealization

universe u v

variable (period : Real) (hPeriod : period ≠ 0)

variable {Base : Type u} {Index : Type v} [TopologicalSpace Base]

/-- Circle transition of the complex spinor line associated to a supplied
rank-two Clifford SpinC Cech bundle. -/
def associatedRankTwoSpinorTransition
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2)
    (first second : Index) (base : Base) : Circle :=
  cliffordSpinC2SpinorCharacter (bundle.transition first second base)

def associatedRankTwoSpinorCircleBundle
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2) :
    CechPrincipalBundleData Base Index Circle where
  domain := bundle.domain
  domain_isOpen := bundle.domain_isOpen
  cover := bundle.cover
  transition := associatedRankTwoSpinorTransition bundle
  transition_self := by
    intro index base hBase
    simp [associatedRankTwoSpinorTransition, bundle.transition_self index base hBase]
  transition_inverse := by
    intro first second base hFirst hSecond
    change cliffordSpinC2SpinorCharacter
          (bundle.transition first second base) *
        cliffordSpinC2SpinorCharacter
          (bundle.transition second first base) = 1
    rw [← map_mul, bundle.transition_inverse first second base hFirst hSecond]
    simp
  transition_cocycle := by
    intro first second third base hFirst hSecond hThird
    change cliffordSpinC2SpinorCharacter
          (bundle.transition first second base) *
        cliffordSpinC2SpinorCharacter
          (bundle.transition second third base) =
      cliffordSpinC2SpinorCharacter
        (bundle.transition first third base)
    rw [← map_mul,
      bundle.transition_cocycle first second third base hFirst hSecond hThird]

/-- A section in local trivializations, with the transition law supplied by
the descended SpinC character. -/
structure CechRankTwoSpinorSection
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2) where
  component : Index → Base → Complex
  compatible : ∀ first second base,
    base ∈ bundle.domain first → base ∈ bundle.domain second →
      component first base =
        rankTwoSpinCSpinorAction (bundle.transition first second base)
          (component second base)

def zeroCechRankTwoSpinorSection
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2) :
    CechRankTwoSpinorSection bundle where
  component := fun _ _ => 0
  compatible := by
    intro first second base hFirst hSecond
    simp [rankTwoSpinCSpinorAction]

/-- The Hermitian pairing of compatible spinors is independent of the active
chart on every overlap. -/
theorem cechRankTwoSpinorHermitianPairing_chartIndependent
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2)
    (first second : CechRankTwoSpinorSection bundle)
    (firstChart secondChart : Index) (base : Base)
    (hFirst : base ∈ bundle.domain firstChart)
    (hSecond : base ∈ bundle.domain secondChart) :
    rankTwoSpinorHermitianPairing
        (first.component firstChart base) (second.component firstChart base) =
      rankTwoSpinorHermitianPairing
        (first.component secondChart base)
        (second.component secondChart base) := by
  rw [first.compatible firstChart secondChart base hFirst hSecond,
    second.compatible firstChart secondChart base hFirst hSecond]
  exact rankTwoSpinorHermitianPairing_invariant _ _ _

structure ProgramPRankTwoSpinCCechHermitianDescentCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2) where
  classificationCertificate :
    ProgramPRankTwoSpinCHermitianClassificationCertificate4D
      period hPeriod domain
  associatedCircleBundle : CechPrincipalBundleData Base Index Circle
  associatedCircleBundle_eq :
    associatedCircleBundle = associatedRankTwoSpinorCircleBundle bundle
  hermitianChartIndependent :
    ∀ (first second : CechRankTwoSpinorSection bundle)
      firstChart secondChart base,
      base ∈ bundle.domain firstChart → base ∈ bundle.domain secondChart →
        rankTwoSpinorHermitianPairing
            (first.component firstChart base)
            (second.component firstChart base) =
          rankTwoSpinorHermitianPairing
            (first.component secondChart base)
            (second.component secondChart base)

def programPRankTwoSpinCCechHermitianDescentCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (bundle : CechPrincipalBundleData Base Index CliffordSpinC2) :
    ProgramPRankTwoSpinCCechHermitianDescentCertificate4D
      period hPeriod domain bundle where
  classificationCertificate :=
    programPRankTwoSpinCHermitianClassificationCertificate4D
      period hPeriod domain
  associatedCircleBundle := associatedRankTwoSpinorCircleBundle bundle
  associatedCircleBundle_eq := rfl
  hermitianChartIndependent := by
    intro first second firstChart secondChart base hFirst hSecond
    exact cechRankTwoSpinorHermitianPairing_chartIndependent bundle first second
      firstChart secondChart base hFirst hSecond

/-- Closed one-chart instance; nontrivial Janus topology still requires a
geometrically derived multi-chart principal bundle. -/
theorem canonicalOneChartRankTwoSpinCCechHermitianCertificate_nonempty :
    Nonempty
      (ProgramPRankTwoSpinCCechHermitianDescentCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)
        (trivialCechPrincipalBundle Real CliffordSpinC2)) :=
  ⟨programPRankTwoSpinCCechHermitianDescentCertificate4D period hPeriod _ _⟩

end
end P0EFTJanusProgramPRankTwoSpinCCechHermitianDescent4D
end JanusFormal
