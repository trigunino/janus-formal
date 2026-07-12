import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusSpinCImmersionCategory

namespace JanusFormal
namespace P0EFTJanusNaturalSymbolCalculus

set_option autoImplicit false

open P0EFTJanusSpinCImmersionCategory

universe u v w x y z

/-- Pointwise principal-symbol family over the immersion category. -/
structure PrincipalSymbolFamily
    (immersionCategory : SpinCImmersionCategory) where
  Covector : immersionCategory.category.Obj → Type w
  Source : immersionCategory.category.Obj → Type x
  Target : immersionCategory.category.Obj → Type y
  zeroCovector : ∀ object, Covector object
  symbol :
    ∀ object,
      Covector object → Source object → Target object

/-- Ellipticity means injectivity of the symbol at every nonzero covector. -/
def IsElliptic
    (immersionCategory : SpinCImmersionCategory)
    (symbolFamily : PrincipalSymbolFamily immersionCategory) : Prop :=
  ∀ object covector,
    covector ≠ symbolFamily.zeroCovector object →
      Function.Injective (symbolFamily.symbol object covector)

/-- Identity principal symbol. -/
def identitySymbolFamily
    (immersionCategory : SpinCImmersionCategory)
    (Covector : immersionCategory.category.Obj → Type w)
    (zeroCovector : ∀ object, Covector object)
    (Fiber : immersionCategory.category.Obj → Type x) :
    PrincipalSymbolFamily immersionCategory where
  Covector := Covector
  Source := Fiber
  Target := Fiber
  zeroCovector := zeroCovector
  symbol := fun _ _ value => value

/-- Identity symbols are elliptic. -/
theorem identity_symbol_elliptic
    (immersionCategory : SpinCImmersionCategory)
    (Covector : immersionCategory.category.Obj → Type w)
    (zeroCovector : ∀ object, Covector object)
    (Fiber : immersionCategory.category.Obj → Type x) :
    IsElliptic immersionCategory
      (identitySymbolFamily immersionCategory
        Covector zeroCovector Fiber) := by
  intro object covector hCovector first second hEqual
  exact hEqual

/-- Composition of two symbol families with common covector data. -/
def composeSymbolFamilies
    (immersionCategory : SpinCImmersionCategory)
    (firstFamily : PrincipalSymbolFamily immersionCategory)
    (secondFamily : PrincipalSymbolFamily immersionCategory)
    (hCovector : secondFamily.Covector = firstFamily.Covector)
    (hZero : HEq secondFamily.zeroCovector firstFamily.zeroCovector)
    (hMiddle : secondFamily.Source = firstFamily.Target) :
    PrincipalSymbolFamily immersionCategory := by
  subst hCovector
  subst hMiddle
  have hZeroEq : secondFamily.zeroCovector = firstFamily.zeroCovector := by
    exact eq_of_heq hZero
  exact
    { Covector := firstFamily.Covector
      Source := firstFamily.Source
      Target := secondFamily.Target
      zeroCovector := firstFamily.zeroCovector
      symbol := fun object covector value =>
        secondFamily.symbol object covector
          (firstFamily.symbol object covector value) }

/-- Composition of elliptic symbols is elliptic. -/
theorem compose_symbol_families_elliptic
    (immersionCategory : SpinCImmersionCategory)
    (firstFamily : PrincipalSymbolFamily immersionCategory)
    (secondFamily : PrincipalSymbolFamily immersionCategory)
    (hCovector : secondFamily.Covector = firstFamily.Covector)
    (hZero : HEq secondFamily.zeroCovector firstFamily.zeroCovector)
    (hMiddle : secondFamily.Source = firstFamily.Target)
    (hFirst : IsElliptic immersionCategory firstFamily)
    (hSecond : IsElliptic immersionCategory secondFamily) :
    IsElliptic immersionCategory
      (composeSymbolFamilies immersionCategory
        firstFamily secondFamily hCovector hZero hMiddle) := by
  subst hCovector
  subst hMiddle
  have hZeroEq : secondFamily.zeroCovector = firstFamily.zeroCovector :=
    eq_of_heq hZero
  subst hZeroEq
  intro object covector hCovectorValue first second hEqual
  apply hFirst object covector hCovectorValue
  apply hSecond object covector hCovectorValue
  exact hEqual

/-- Direct sum/product of two symbol families with common covector data. -/
def productSymbolFamilies
    (immersionCategory : SpinCImmersionCategory)
    (firstFamily secondFamily :
      PrincipalSymbolFamily immersionCategory)
    (hCovector : secondFamily.Covector = firstFamily.Covector)
    (hZero : HEq secondFamily.zeroCovector firstFamily.zeroCovector) :
    PrincipalSymbolFamily immersionCategory := by
  subst hCovector
  have hZeroEq : secondFamily.zeroCovector = firstFamily.zeroCovector :=
    eq_of_heq hZero
  exact
    { Covector := firstFamily.Covector
      Source := fun object =>
        firstFamily.Source object × secondFamily.Source object
      Target := fun object =>
        firstFamily.Target object × secondFamily.Target object
      zeroCovector := firstFamily.zeroCovector
      symbol := fun object covector value =>
        (firstFamily.symbol object covector value.1,
          secondFamily.symbol object covector value.2) }

/-- Product of elliptic symbols is elliptic. -/
theorem product_symbol_families_elliptic
    (immersionCategory : SpinCImmersionCategory)
    (firstFamily secondFamily :
      PrincipalSymbolFamily immersionCategory)
    (hCovector : secondFamily.Covector = firstFamily.Covector)
    (hZero : HEq secondFamily.zeroCovector firstFamily.zeroCovector)
    (hFirst : IsElliptic immersionCategory firstFamily)
    (hSecond : IsElliptic immersionCategory secondFamily) :
    IsElliptic immersionCategory
      (productSymbolFamilies immersionCategory
        firstFamily secondFamily hCovector hZero) := by
  subst hCovector
  have hZeroEq : secondFamily.zeroCovector = firstFamily.zeroCovector :=
    eq_of_heq hZero
  subst hZeroEq
  intro object covector hCovectorValue first second hEqual
  apply Prod.ext
  · apply hFirst object covector hCovectorValue
    exact congrArg Prod.fst hEqual
  · apply hSecond object covector hCovectorValue
    exact congrArg Prod.snd hEqual

/-- Symbol family obtained by multiplying every fiber by a real weight. -/
def scalarSymbolFamily
    (immersionCategory : SpinCImmersionCategory)
    (Covector : immersionCategory.category.Obj → Type w)
    (zeroCovector : ∀ object, Covector object)
    (Fiber : immersionCategory.category.Obj → Type x)
    [∀ object, Zero (Fiber object)]
    [∀ object, SMul ℝ (Fiber object)]
    (weight : ∀ object, Covector object → ℝ) :
    PrincipalSymbolFamily immersionCategory where
  Covector := Covector
  Source := Fiber
  Target := Fiber
  zeroCovector := zeroCovector
  symbol := fun object covector value =>
    weight object covector • value

/-- Faithful nonzero scalar action gives ellipticity of a scalar symbol. -/
theorem scalar_symbol_elliptic
    (immersionCategory : SpinCImmersionCategory)
    (Covector : immersionCategory.category.Obj → Type w)
    (zeroCovector : ∀ object, Covector object)
    (Fiber : immersionCategory.category.Obj → Type x)
    [∀ object, Zero (Fiber object)]
    [∀ object, SMul ℝ (Fiber object)]
    (weight : ∀ object, Covector object → ℝ)
    (hWeight :
      ∀ object covector,
        covector ≠ zeroCovector object →
          weight object covector ≠ 0)
    (hFaithful :
      ∀ object (scalar : ℝ),
        scalar ≠ 0 →
        ∀ first second : Fiber object,
          scalar • first = scalar • second → first = second) :
    IsElliptic immersionCategory
      (scalarSymbolFamily immersionCategory
        Covector zeroCovector Fiber weight) := by
  intro object covector hCovector first second hEqual
  exact hFaithful object (weight object covector)
    (hWeight object covector hCovector) first second hEqual

/-- Lower-order perturbations have no place in the principal-symbol structure. -/
structure FullOperatorOverSymbol
    (immersionCategory : SpinCImmersionCategory)
    (symbolFamily : PrincipalSymbolFamily immersionCategory) where
  FullOperator :
    ∀ object,
      symbolFamily.Source object →
        symbolFamily.Target object
  principalSymbolCertified : Prop
  naturalityCertified : Prop
  lowerOrderDataCertified : Prop

/--
The symbol calculus is canonical once the natural bundles, induced metric and
connections are fixed.  It proves ellipticity under sums and compositions, but
it intentionally forgets all lower-order endomorphisms and boundary domains.
-/
structure NaturalSymbolCalculusPhysicalStatus where
  cotangentFunctorConstructed : Prop
  zeroSectionConstructed : Prop
  principalSymbolsConstructed : Prop
  symbolNaturalityProved : Prop
  deRhamSymbolExactnessProved : Prop
  diracCliffordSquareProved : Prop
  jacobiSymbolIdentified : Prop
  lichnerowiczSymbolIdentified : Prop
  gaugeFixedBlockSymbolConstructed : Prop
  ellipticityProved : Prop


def naturalSymbolCalculusPhysicalClosure
    (s : NaturalSymbolCalculusPhysicalStatus) : Prop :=
  s.cotangentFunctorConstructed /\
  s.zeroSectionConstructed /\
  s.principalSymbolsConstructed /\
  s.symbolNaturalityProved /\
  s.deRhamSymbolExactnessProved /\
  s.diracCliffordSquareProved /\
  s.jacobiSymbolIdentified /\
  s.lichnerowiczSymbolIdentified /\
  s.gaugeFixedBlockSymbolConstructed /\
  s.ellipticityProved

end P0EFTJanusNaturalSymbolCalculus
end JanusFormal
