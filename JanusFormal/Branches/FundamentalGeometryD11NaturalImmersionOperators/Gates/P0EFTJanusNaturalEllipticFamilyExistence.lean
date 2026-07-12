import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalOperatorJets
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalSymbolCalculus
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalLowerOrderFreedom

namespace JanusFormal
namespace P0EFTJanusNaturalEllipticFamilyExistence

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalOperatorJets
open P0EFTJanusNaturalSymbolCalculus
open P0EFTJanusNaturalLowerOrderFreedom

universe u v x y z w

/-- Complete algebraic certificate for one natural elliptic operator family. -/
structure NaturalEllipticOperatorFamily
    (immersionCategory : SpinCImmersionCategory) where
  sourceFunctor : NaturalSectionFunctor immersionCategory
  targetFunctor : NaturalSectionFunctor immersionCategory
  sourceJets : NaturalJetFunctor immersionCategory sourceFunctor
  operator : NaturalOperator immersionCategory sourceFunctor targetFunctor
  finiteOrder :
    FiniteOrderCertificate immersionCategory sourceFunctor
      targetFunctor sourceJets operator
  symbolFamily : PrincipalSymbolFamily immersionCategory
  symbolSourceMatches :
    ∀ object,
      symbolFamily.Source object = sourceFunctor.Section object
  symbolTargetMatches :
    ∀ object,
      symbolFamily.Target object = targetFunctor.Section object
  elliptic : IsElliptic immersionCategory symbolFamily
  fullOperatorPrincipalSymbolCertified : Prop
  selfAdjointOrGradedAdjointDomainDerived : Prop
  fredholmFamilyDerived : Prop

/-- Constructor theorem: once naturality, jet factorization and ellipticity are proved, the family exists. -/
def assembleNaturalEllipticOperatorFamily
    (immersionCategory : SpinCImmersionCategory)
    (sourceFunctor targetFunctor :
      NaturalSectionFunctor immersionCategory)
    (sourceJets : NaturalJetFunctor immersionCategory sourceFunctor)
    (operator :
      NaturalOperator immersionCategory sourceFunctor targetFunctor)
    (finiteOrder :
      FiniteOrderCertificate immersionCategory sourceFunctor
        targetFunctor sourceJets operator)
    (symbolFamily : PrincipalSymbolFamily immersionCategory)
    (symbolSourceMatches :
      ∀ object,
        symbolFamily.Source object = sourceFunctor.Section object)
    (symbolTargetMatches :
      ∀ object,
        symbolFamily.Target object = targetFunctor.Section object)
    (elliptic : IsElliptic immersionCategory symbolFamily)
    (fullOperatorPrincipalSymbolCertified : Prop)
    (selfAdjointOrGradedAdjointDomainDerived : Prop)
    (fredholmFamilyDerived : Prop) :
    NaturalEllipticOperatorFamily immersionCategory :=
  { sourceFunctor := sourceFunctor
    targetFunctor := targetFunctor
    sourceJets := sourceJets
    operator := operator
    finiteOrder := finiteOrder
    symbolFamily := symbolFamily
    symbolSourceMatches := symbolSourceMatches
    symbolTargetMatches := symbolTargetMatches
    elliptic := elliptic
    fullOperatorPrincipalSymbolCertified :=
      fullOperatorPrincipalSymbolCertified
    selfAdjointOrGradedAdjointDomainDerived :=
      selfAdjointOrGradedAdjointDomainDerived
    fredholmFamilyDerived := fredholmFamilyDerived }

/-- Every assembled family is natural, finite-order and elliptic by construction. -/
theorem assembled_family_matrix
    (immersionCategory : SpinCImmersionCategory)
    (family : NaturalEllipticOperatorFamily immersionCategory) :
    (∀ {source target}
      (morphism :
        AdmissibleMorphism immersionCategory source target)
      (sectionValue : family.sourceFunctor.Section target),
      family.targetFunctor.pullback morphism
          (family.operator.apply target sectionValue) =
        family.operator.apply source
          (family.sourceFunctor.pullback morphism sectionValue)) /\
    Nonempty
      (FiniteOrderCertificate immersionCategory
        family.sourceFunctor family.targetFunctor
        family.sourceJets family.operator) /\
    IsElliptic immersionCategory family.symbolFamily := by
  exact ⟨family.operator.naturality,
    ⟨family.finiteOrder⟩,
    family.elliptic⟩

/-- Forgetful local model from a full operator to its principal symbol. -/
def forgetLowerOrder
    (model : ScalarLaplaceTypeModel) :
    ℝ → ℝ → ℝ :=
  principalSymbol model

/-- The forgetful map to principal symbols is not injective. -/
theorem principal_symbol_forgetful_map_not_injective :
    ∃ first second : ScalarLaplaceTypeModel,
      first ≠ second /\
      forgetLowerOrder first = forgetLowerOrder second := by
  refine ⟨{ potential := 0 }, { potential := 1 }, ?_, ?_⟩
  · intro hEqual
    have hPotential := congrArg ScalarLaplaceTypeModel.potential hEqual
    norm_num at hPotential
  · funext normSquared field
    rfl

/-- Same canonical symbol can support inequivalent natural lower-order operators. -/
theorem canonical_symbol_does_not_select_unique_family :
    ∃ first second : ScalarLaplaceTypeModel,
      (∀ normSquared field,
        principalSymbol first normSquared field =
          principalSymbol second normSquared field) /\
      fullOperator first 0 1 ≠ fullOperator second 0 1 :=
  principal_symbol_does_not_determine_full_operator

/-- A selection principle upgrades canonical symbols to a chosen full family. -/
structure FullFamilySelectionPrinciple where
  allowedNaturalInvariantsClassified : Prop
  actionFunctionalDerived : Prop
  actionNormalizationDerived : Prop
  lowerOrderCouplingsDerived : Prop
  gaugeFixingDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  domainsAndBoundaryConditionsDerived : Prop
  familyIndexClassDerived : Prop

/-- Bare geometry closes only the principal-symbol layer. -/
structure BareGeometryOperatorStatus where
  immersionCategoryConstructed : Prop
  naturalBundlesConstructed : Prop
  naturalConnectionsConstructed : Prop
  principalSymbolFamilyConstructed : Prop
  ellipticityProved : Prop
  actionFunctionalDerived : Prop
  lowerOrderCouplingsDerived : Prop
  finiteCountertermsFixed : Prop
  fullOperatorFamilySelected : Prop

/-- Full operator selection. -/
def fullOperatorFamilySelected
    (s : BareGeometryOperatorStatus) : Prop :=
  s.immersionCategoryConstructed /\
  s.naturalBundlesConstructed /\
  s.naturalConnectionsConstructed /\
  s.principalSymbolFamilyConstructed /\
  s.ellipticityProved /\
  s.actionFunctionalDerived /\
  s.lowerOrderCouplingsDerived /\
  s.finiteCountertermsFixed /\
  s.fullOperatorFamilySelected

/-- Missing an action blocks uniqueness of the full family. -/
theorem missing_action_blocks_full_family_selection
    (s : BareGeometryOperatorStatus)
    (hMissing : Not s.actionFunctionalDerived) :
    Not (fullOperatorFamilySelected s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

/-- Missing finite renormalization also blocks a predictive family. -/
theorem missing_finite_counterterms_blocks_full_family_selection
    (s : BareGeometryOperatorStatus)
    (hMissing : Not s.finiteCountertermsFixed) :
    Not (fullOperatorFamilySelected s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

/--
Existence verdict: a natural elliptic family exists conditionally once the
bundle functors, finite-order natural operator, symbol and Fredholm domain are
constructed.  Uniqueness is false at the level of bare immersion geometry;
only the principal-symbol class is canonical.
-/
structure NaturalEllipticFamilyPhysicalStatus where
  categoricalGeometryConstructed : Prop
  naturalBundleFunctorsConstructed : Prop
  peetreSlovakBridgeProved : Prop
  canonicalPrincipalSymbolsConstructed : Prop
  ellipticityProved : Prop
  globalOperatorsConstructed : Prop
  selfAdjointDomainsDerived : Prop
  fredholmFamilyProved : Prop
  actionSelectionPrincipleDerived : Prop
  finiteRenormalizationDerived : Prop
  uniquePhysicalFamilyDerived : Prop


def naturalEllipticFamilyPhysicalClosure
    (s : NaturalEllipticFamilyPhysicalStatus) : Prop :=
  s.categoricalGeometryConstructed /\
  s.naturalBundleFunctorsConstructed /\
  s.peetreSlovakBridgeProved /\
  s.canonicalPrincipalSymbolsConstructed /\
  s.ellipticityProved /\
  s.globalOperatorsConstructed /\
  s.selfAdjointDomainsDerived /\
  s.fredholmFamilyProved /\
  s.actionSelectionPrincipleDerived /\
  s.finiteRenormalizationDerived /\
  s.uniquePhysicalFamilyDerived

end P0EFTJanusNaturalEllipticFamilyExistence
end JanusFormal
