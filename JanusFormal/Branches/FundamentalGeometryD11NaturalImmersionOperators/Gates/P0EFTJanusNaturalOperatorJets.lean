import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalBundleFunctor

namespace JanusFormal
namespace P0EFTJanusNaturalOperatorJets

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor

universe u v x y z

/-- Jet functor for sections of one natural bundle. -/
structure NaturalJetFunctor
    (immersionCategory : SpinCImmersionCategory)
    (sectionFunctor : NaturalSectionFunctor immersionCategory) where
  Jet : immersionCategory.category.Obj → ℕ → Type z
  jetExtension :
    ∀ object (order : ℕ),
      sectionFunctor.Section object → Jet object order
  pullbackJet :
    ∀ {source target}
      (morphism :
        AdmissibleMorphism immersionCategory source target)
      (order : ℕ),
      Jet target order → Jet source order
  jetPullbackNaturality :
    ∀ {source target}
      (morphism :
        AdmissibleMorphism immersionCategory source target)
      (order : ℕ)
      (sectionValue : sectionFunctor.Section target),
      pullbackJet morphism order
          (jetExtension target order sectionValue) =
        jetExtension source order
          (sectionFunctor.pullback morphism sectionValue)
  pullbackJetIdentity :
    ∀ object (order : ℕ) (jetValue : Jet object order),
      pullbackJet (admissibleIdentity immersionCategory object)
          order jetValue = jetValue
  pullbackJetComposition :
    ∀ {first second third}
      (secondMorphism :
        AdmissibleMorphism immersionCategory second third)
      (firstMorphism :
        AdmissibleMorphism immersionCategory first second)
      (order : ℕ)
      (jetValue : Jet third order),
      pullbackJet
          (admissibleCompose immersionCategory
            secondMorphism firstMorphism)
          order jetValue =
        pullbackJet firstMorphism order
          (pullbackJet secondMorphism order jetValue)

/-- Finite-order factorization certificate for one natural operator. -/
structure FiniteOrderCertificate
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor) where
  order : ℕ
  evaluateJet :
    ∀ object,
      sourceJets.Jet object order →
        targetFunctor.Section object
  factorization :
    ∀ object (sectionValue : sourceFunctor.Section object),
      operator.apply object sectionValue =
        evaluateJet object
          (sourceJets.jetExtension object order sectionValue)
  jetNaturality :
    ∀ {source target}
      (morphism :
        AdmissibleMorphism immersionCategory source target)
      (jetValue : sourceJets.Jet target order),
      targetFunctor.pullback morphism
          (evaluateJet target jetValue) =
        evaluateJet source
          (sourceJets.pullbackJet morphism order jetValue)

/-- Equality of sections through order `k` in the abstract jet model. -/
def SameJetThrough
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor : NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (object : immersionCategory.category.Obj)
    (order : ℕ)
    (first second : sourceFunctor.Section object) : Prop :=
  sourceJets.jetExtension object order first =
    sourceJets.jetExtension object order second

/-- A finite-order operator depends only on the certified jet. -/
theorem finite_order_depends_only_on_jet
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor)
    (certificate :
      FiniteOrderCertificate immersionCategory sourceFunctor
        targetFunctor sourceJets operator)
    (object : immersionCategory.category.Obj)
    (first second : sourceFunctor.Section object)
    (hSameJet : SameJetThrough immersionCategory sourceFunctor
      sourceJets object certificate.order first second) :
    operator.apply object first = operator.apply object second := by
  rw [certificate.factorization,
    certificate.factorization]
  exact congrArg (certificate.evaluateJet object) hSameJet

/-- The jet evaluator itself defines the same natural operator. -/
def operatorFromJetCertificate
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor)
    (certificate :
      FiniteOrderCertificate immersionCategory sourceFunctor
        targetFunctor sourceJets operator) :
    NaturalOperator immersionCategory sourceFunctor targetFunctor where
  apply := fun object sectionValue =>
    certificate.evaluateJet object
      (sourceJets.jetExtension object certificate.order sectionValue)
  naturality := by
    intro source target morphism sectionValue
    rw [certificate.jetNaturality]
    rw [sourceJets.jetPullbackNaturality]

/-- The reconstructed jet operator agrees pointwise with the original operator. -/
theorem operator_from_jet_certificate_agrees
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor)
    (certificate :
      FiniteOrderCertificate immersionCategory sourceFunctor
        targetFunctor sourceJets operator)
    (object : immersionCategory.category.Obj)
    (sectionValue : sourceFunctor.Section object) :
    (operatorFromJetCertificate immersionCategory sourceFunctor
      targetFunctor sourceJets operator certificate).apply
        object sectionValue =
      operator.apply object sectionValue := by
  exact (certificate.factorization object sectionValue).symm

/-- Abstract Peetre--Slovak bridge, deliberately isolated as an analytic theorem obligation. -/
structure PeetreSlovakBridge
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor) where
  RegularLocal :
    NaturalOperator immersionCategory sourceFunctor targetFunctor → Prop
  finiteOrderOfRegularLocal :
    ∀ operator,
      RegularLocal operator →
      Nonempty
        (FiniteOrderCertificate immersionCategory sourceFunctor
          targetFunctor sourceJets operator)

/-- A regular local operator is finite-order once a Peetre--Slovak bridge is proved. -/
theorem regular_local_has_finite_order
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (bridge :
      PeetreSlovakBridge immersionCategory sourceFunctor
        targetFunctor sourceJets)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor)
    (hRegularLocal : bridge.RegularLocal operator) :
    Nonempty
      (FiniteOrderCertificate immersionCategory sourceFunctor
        targetFunctor sourceJets operator) :=
  bridge.finiteOrderOfRegularLocal operator hRegularLocal

/--
D11 does not claim the nonlinear Peetre--Slovak theorem from pure algebra.  It
provides the exact interface required to import or prove it for the chosen
Fréchet/derived category of SpinC immersions.
-/
structure JetClassificationPhysicalStatus where
  sectionSheavesConstructed : Prop
  jetBundlesConstructed : Prop
  regularityNotionFixed : Prop
  localityNotionFixed : Prop
  weakRegularityProved : Prop
  peetreSlovakHypothesesVerified : Prop
  finiteOrderTheoremProved : Prop
  equivariantJetMapsClassified : Prop
  invariantTheoryReducedToFiniteJets : Prop


def jetClassificationPhysicalClosure
    (s : JetClassificationPhysicalStatus) : Prop :=
  s.sectionSheavesConstructed /\
  s.jetBundlesConstructed /\
  s.regularityNotionFixed /\
  s.localityNotionFixed /\
  s.weakRegularityProved /\
  s.peetreSlovakHypothesesVerified /\
  s.finiteOrderTheoremProved /\
  s.equivariantJetMapsClassified /\
  s.invariantTheoryReducedToFiniteJets

end P0EFTJanusNaturalOperatorJets
end JanusFormal
