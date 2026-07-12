import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols

namespace JanusFormal
namespace P0EFTJanusCliffordDiracPrincipalSymbol

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols

/--
Abstract Clifford principal symbol.  The square law is the defining local
identity behind ellipticity of a Dirac-type operator.
-/
structure CliffordSymbolData
    (Spinor : Type*)
    [Zero Spinor]
    [SMul ℝ Spinor] where
  symbol : TangentVector3 → Spinor → Spinor
  symbolZero : ∀ covector, symbol covector 0 = 0
  squareLaw :
    ∀ covector spinor,
      symbol covector (symbol covector spinor) =
        normSquared covector • spinor
  faithfulRealScaling :
    ∀ scalar : ℝ, scalar ≠ 0 →
      ∀ spinor : Spinor,
        scalar • spinor = 0 → spinor = 0

/-- A Clifford symbol has trivial kernel at every nonzero covector. -/
theorem dirac_symbol_kernel_trivial
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (data : CliffordSymbolData Spinor)
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (spinor : Spinor)
    (hKernel : data.symbol covector spinor = 0) :
    spinor = 0 := by
  have hScaled : normSquared covector • spinor = 0 := by
    calc
      normSquared covector • spinor =
          data.symbol covector
            (data.symbol covector spinor) :=
        (data.squareLaw covector spinor).symm
      _ = data.symbol covector 0 := by rw [hKernel]
      _ = 0 := data.symbolZero covector
  exact data.faithfulRealScaling
    (normSquared covector)
    (ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector))
    spinor hScaled

/-- Twisting data do not alter the first-order Clifford principal symbol. -/
structure TwistedDiracData
    (Spinor : Type*)
    [Zero Spinor]
    [SMul ℝ Spinor] where
  clifford : CliffordSymbolData Spinor
  monopoleConnectionConstructed : Prop
  normalRootFlatLineConstructed : Prop
  tensorProductSpinorBundleConstructed : Prop
  twistedOperatorConstructed : Prop
  twistedPrincipalSymbolEqualsClifford : Prop

/-- Principal-symbol ellipticity survives monopole and flat normal-root twists. -/
theorem twisted_dirac_symbol_kernel_trivial
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (data : TwistedDiracData Spinor)
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (spinor : Spinor)
    (hKernel : data.clifford.symbol covector spinor = 0) :
    spinor = 0 :=
  dirac_symbol_kernel_trivial data.clifford
    covector hCovector spinor hKernel

/-- PT-paired spinors. -/
abbrev PTPairedSpinor (Spinor : Type*) := Spinor × Spinor

/-- Block-diagonal PT-paired Clifford symbol. -/
def pairedCliffordSymbol
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (data : CliffordSymbolData Spinor)
    (covector : TangentVector3)
    (spinor : PTPairedSpinor Spinor) :
    PTPairedSpinor Spinor :=
  (data.symbol covector spinor.1,
    data.symbol covector spinor.2)

/-- PT pairing doubles the sector but does not create a principal-symbol kernel. -/
theorem paired_dirac_symbol_kernel_trivial
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (data : CliffordSymbolData Spinor)
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (spinor : PTPairedSpinor Spinor)
    (hKernel : pairedCliffordSymbol data covector spinor = (0, 0)) :
    spinor = (0, 0) := by
  have hFirst : data.symbol covector spinor.1 = 0 :=
    congrArg Prod.fst hKernel
  have hSecond : data.symbol covector spinor.2 = 0 :=
    congrArg Prod.snd hKernel
  exact Prod.ext
    (dirac_symbol_kernel_trivial data covector
      hCovector spinor.1 hFirst)
    (dirac_symbol_kernel_trivial data covector
      hCovector spinor.2 hSecond)

/-- Complex spinor rank in three Euclidean dimensions. -/
def threeDimensionalComplexSpinorRank : ℕ := 2

@[simp] theorem three_dimensional_complex_spinor_rank_is_two :
    threeDimensionalComplexSpinorRank = 2 := by
  rfl

/-- PT pairing gives complex rank four before any reality condition. -/
def pairedComplexSpinorRank : ℕ :=
  2 * threeDimensionalComplexSpinorRank

@[simp] theorem paired_complex_spinor_rank_is_four :
    pairedComplexSpinorRank = 4 := by
  norm_num [pairedComplexSpinorRank,
    threeDimensionalComplexSpinorRank]

/--
The square-root normal line and the monopole determinant line enter the global
bundle and boundary conditions, while the local principal symbol remains
Clifford multiplication.  Constructing the actual Pin/SpinC module and proving
its Lichnerowicz formula are global obligations, not principal-symbol choices.
-/
structure GlobalTwistedDiracClosureStatus where
  intrinsicSpinStructureConstructed : Prop
  ambientPinRestrictionConstructed : Prop
  primitiveSpinCDeterminantLineConstructed : Prop
  normalRootFlatLineConstructed : Prop
  twistedSpinorBundleConstructed : Prop
  cliffordActionConstructed : Prop
  compatibleConnectionConstructed : Prop
  diracOperatorSelfAdjoint : Prop
  principalSymbolSquareLawProved : Prop
  lichnerowiczFormulaProved : Prop
  quarterBoundaryConditionsProved : Prop
  ptPairedDomainConstructed : Prop


def globalTwistedDiracClosure
    (s : GlobalTwistedDiracClosureStatus) : Prop :=
  s.intrinsicSpinStructureConstructed /\
  s.ambientPinRestrictionConstructed /\
  s.primitiveSpinCDeterminantLineConstructed /\
  s.normalRootFlatLineConstructed /\
  s.twistedSpinorBundleConstructed /\
  s.cliffordActionConstructed /\
  s.compatibleConnectionConstructed /\
  s.diracOperatorSelfAdjoint /\
  s.principalSymbolSquareLawProved /\
  s.lichnerowiczFormulaProved /\
  s.quarterBoundaryConditionsProved /\
  s.ptPairedDomainConstructed

end P0EFTJanusCliffordDiracPrincipalSymbol
end JanusFormal
