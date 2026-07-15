/-
Program D9: consolidated immersed SpinC elliptic-symbol and linear BRST layer.

The first closure is independent of a selected action: it collects the fiber,
symbol, gauge-fixing and linear-complex results.  The second closure records the
global analytic and variational data that must later be supplied by P.
-/

import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCliffordDiracPrincipalSymbol
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusDeRhamSymbolExactness
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusImmersedSpinCOriginSynthesis
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusImmersionFiberAlgebra
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusLinearizedBRSTNilpotence
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusLinearizedDerivedCriticalComplex
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusMetricGaugeSymbolDecomposition
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusModuliActionSelectionNoGo
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusNormalRootMonopoleSeparation

namespace JanusFormal
namespace JanusFundamentalGeometryD9ImmersedSpinCEllipticComplex

set_option autoImplicit false

structure ProgramStatus where
  immersionTangentNormalFiberSplitProved : Prop
  spinCAndNormalRootInputsSeparated : Prop
  deRhamSymbolExactnessProved : Prop
  maxwellGaugeGhostSymbolProved : Prop
  metricDeDonderGhostSymbolProved : Prop
  normalJacobiSymbolProved : Prop
  twistedDiracCliffordSymbolProved : Prop
  completeBlockSymbolElliptic : Prop
  linearBRSTNilpotenceProved : Prop
  linearDerivedCriticalComplexConstructed : Prop
  moduliGeometryDoesNotSelectActionProved : Prop
  globalBundlesConstructed : Prop
  invariantActionAndCriticalPointConstructed : Prop
  hessianAndNoetherOperatorsDerived : Prop
  commonFredholmDomainsConstructed : Prop
  globalEllipticityProved : Prop
  zeroModeCohomologyComputed : Prop
  nonlinearBVClosureProved : Prop
  determinantLineConstructed : Prop

/-- P-independent algebraic and principal-symbol closure. -/
def symbolBRSTFoundationClosed (s : ProgramStatus) : Prop :=
  s.immersionTangentNormalFiberSplitProved ∧
  s.spinCAndNormalRootInputsSeparated ∧ s.deRhamSymbolExactnessProved ∧
  s.maxwellGaugeGhostSymbolProved ∧ s.metricDeDonderGhostSymbolProved ∧
  s.normalJacobiSymbolProved ∧ s.twistedDiracCliffordSymbolProved ∧
  s.completeBlockSymbolElliptic ∧ s.linearBRSTNilpotenceProved ∧
  s.linearDerivedCriticalComplexConstructed ∧
  s.moduliGeometryDoesNotSelectActionProved

/-- Global D9 realization after P supplies the action and Hessian. -/
def globalEllipticComplexClosed (s : ProgramStatus) : Prop :=
  symbolBRSTFoundationClosed s ∧ s.globalBundlesConstructed ∧
  s.invariantActionAndCriticalPointConstructed ∧
  s.hessianAndNoetherOperatorsDerived ∧ s.commonFredholmDomainsConstructed ∧
  s.globalEllipticityProved ∧ s.zeroModeCohomologyComputed ∧
  s.nonlinearBVClosureProved ∧ s.determinantLineConstructed

theorem missing_action_does_not_block_symbol_foundation
    (s : ProgramStatus) (h : symbolBRSTFoundationClosed s) :
    symbolBRSTFoundationClosed
      { s with invariantActionAndCriticalPointConstructed := False } := by
  exact h

theorem missing_hessian_blocks_global_complex
    (s : ProgramStatus) (h : Not s.hessianAndNoetherOperatorsDerived) :
    Not (globalEllipticComplexClosed s) := by
  intro hs
  exact h hs.2.2.2.1

theorem missing_fredholm_domains_blocks_global_complex
    (s : ProgramStatus) (h : Not s.commonFredholmDomainsConstructed) :
    Not (globalEllipticComplexClosed s) := by
  intro hs
  exact h hs.2.2.2.2.1

theorem missing_cohomology_blocks_determinant_input
    (s : ProgramStatus) (h : Not s.zeroModeCohomologyComputed) :
    Not (globalEllipticComplexClosed s) := by
  intro hs
  exact h hs.2.2.2.2.2.2.1

end JanusFundamentalGeometryD9ImmersedSpinCEllipticComplex
end JanusFormal
