/-
Program D7: spectral geometry and the renormalized effective action on the Janus
throat.

D7 separates four layers:

1. universal heat-kernel coefficients for a closed Laplace-type operator;
2. specialization to the rank-two monopole-twisted Dirac candidate on
   `S2_L x S1_(L*T)`;
3. local/nonlocal and PT-even/eta-odd decomposition of the effective action;
4. the remaining analytic and renormalization theorems needed to select a
   modulus and an absolute scale.
-/

import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusUniversalClosedHeatCoefficients
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusProductThroatDiracHeatCoefficients
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusFiniteProductHeatTrace
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusHeatKernelScaleOrbit
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusLocalHeatKernelScaling
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusCircleHeatKernelWinding
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusProductThroatLocalInvariants
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusDiracSeeleyDeWittCandidate
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTruncatedSpectralActionNoGo
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusHeatKernelCountertermScheme
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusRenormalizationSchemeNoGo
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPairedSpectralActionDecomposition
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusHolonomyDeterminantNoGo
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusMixedCircleDeterminantStabilization

namespace JanusFormal
namespace JanusFundamentalGeometryD7SpectralTheory

set_option autoImplicit false

structure ProgramStatus where
  universalClosedA0A2A4Formalized : Prop
  rankTwoDiracTraceReductionFormalized : Prop
  productThroatCurvatureIntegralsComputed : Prop
  productThroatDiracCoefficientsMatched : Prop
  finiteProductHeatTraceFactorizationProved : Prop
  localCircleAffinenessProved : Prop
  localNoMinimumProved : Prop
  circlePoissonLocalNonlocalSplitDerived : Prop
  quarterFirstWindingCancellationDerived : Prop
  ptEvenOddActionDecompositionDerived : Prop
  localSpectralScaleOrbitProved : Prop
  finiteCountertermFitNoGoProved : Prop
  schemeShiftNoGoProved : Prop
  pureQuarterDeterminantRunawayProved : Prop
  competingSectorStabilizationCriterionDerived : Prop
  actualGlobalDiracOperatorConstructed : Prop
  separatedInfiniteSpectrumProved : Prop
  heatTraceAsymptoticsProved : Prop
  zetaAndEtaContinuationProved : Prop
  finiteCountertermsDerivedMicroscopically : Prop
  stableModulusDerivedSchemeIndependently : Prop
  independentUVScaleDerived : Prop
  absoluteAlphaDerivedNoFit : Prop

/-- Algebraic/local D7 milestone. -/
def localSpectralFoundationClosed (s : ProgramStatus) : Prop :=
  s.universalClosedA0A2A4Formalized /\
  s.rankTwoDiracTraceReductionFormalized /\
  s.productThroatCurvatureIntegralsComputed /\
  s.productThroatDiracCoefficientsMatched /\
  s.finiteProductHeatTraceFactorizationProved /\
  s.localCircleAffinenessProved /\
  s.localNoMinimumProved /\
  s.circlePoissonLocalNonlocalSplitDerived /\
  s.quarterFirstWindingCancellationDerived /\
  s.ptEvenOddActionDecompositionDerived /\
  s.localSpectralScaleOrbitProved /\
  s.finiteCountertermFitNoGoProved /\
  s.schemeShiftNoGoProved /\
  s.pureQuarterDeterminantRunawayProved /\
  s.competingSectorStabilizationCriterionDerived

/-- Full analytic D7 closure. -/
def analyticSpectralTheoryClosed (s : ProgramStatus) : Prop :=
  localSpectralFoundationClosed s /\
  s.actualGlobalDiracOperatorConstructed /\
  s.separatedInfiniteSpectrumProved /\
  s.heatTraceAsymptoticsProved /\
  s.zetaAndEtaContinuationProved /\
  s.finiteCountertermsDerivedMicroscopically /\
  s.stableModulusDerivedSchemeIndependently

/-- Absolute predictive closure. -/
def fullD7Closure (s : ProgramStatus) : Prop :=
  analyticSpectralTheoryClosed s /\
  s.independentUVScaleDerived /\
  s.absoluteAlphaDerivedNoFit

/-- Local heat coefficients and a co-scaled cutoff cannot close the absolute scale. -/
theorem local_foundation_without_uv_anchor_does_not_close_absolute_alpha
    (s : ProgramStatus)
    (_hLocal : localSpectralFoundationClosed s)
    (hMissing : Not s.independentUVScaleDerived) :
    Not (fullD7Closure s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- A fitted finite counterterm is not a scheme-independent modulus theorem. -/
theorem fitted_counterterm_without_microscopic_derivation_blocks_analytic_closure
    (s : ProgramStatus)
    (hMissing : Not s.finiteCountertermsDerivedMicroscopically) :
    Not (analyticSpectralTheoryClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

end JanusFundamentalGeometryD7SpectralTheory
end JanusFormal
