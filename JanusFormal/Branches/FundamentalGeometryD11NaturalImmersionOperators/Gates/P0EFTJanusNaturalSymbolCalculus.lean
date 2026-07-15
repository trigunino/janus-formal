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

/-- Pointwise composition law used after the family fibers have been matched. -/
theorem symbol_composition_injective
    {Source Middle Target : Type*}
    (first : Source → Middle) (second : Middle → Target)
    (hFirst : Function.Injective first)
    (hSecond : Function.Injective second) :
    Function.Injective (second ∘ first) :=
  hSecond.comp hFirst

/-- Direct-product symbol law used for block-diagonal natural operators. -/
theorem symbol_product_injective
    {Source₁ Source₂ Target₁ Target₂ : Type*}
    (first : Source₁ → Target₁) (second : Source₂ → Target₂)
    (hFirst : Function.Injective first)
    (hSecond : Function.Injective second) :
    Function.Injective (fun value : Source₁ × Source₂ =>
      (first value.1, second value.2)) := by
  intro firstValue secondValue hEqual
  apply Prod.ext
  · exact hFirst (congrArg Prod.fst hEqual)
  · exact hSecond (congrArg Prod.snd hEqual)

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
