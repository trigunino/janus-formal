/-
Program D7: spectral geometry and the renormalized effective action on the Janus
throat.

D7 separates five layers:

1. universal heat-kernel coefficients for a closed Laplace-type operator;
2. specialization to the rank-two monopole-twisted Dirac candidate on
   `S2_L x S1_(L*T)`;
3. local/nonlocal and PT-even/eta-odd decomposition of the effective action;
4. statistics, index multiplicity and internal-symmetry audits of the field
   content entering the determinant;
5. RG scale generation plus the LL/bimetric charge-radius lock.
-/

import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusUniversalClosedHeatCoefficients
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusAbstractDiracPTFredholmFoundation
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusD2GlobalAnalyticBridge
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusD2HeatCountertermBridge
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusHeatRemainderConvergence
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusProductThroatDiracHeatCoefficients
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusFiniteProductHeatTrace
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusHeatKernelScaleOrbit
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusD7AbsoluteAlphaSynthesis
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMinimalTwoTenD7Candidate
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsSelection
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMinimalFiveFermionZ4Sector
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsDeterminantSignNoGo
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusPrimitiveIndexFiveSelection
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusInternalZ4BosonicEscape
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusSpinTwoDimensionalityAudit
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
  productThroatLocalCountertermConstructed : Prop
  commonHolonomyCountertermBridgeConstructed : Prop
  fixedHeatSchemeDeterminantUniqueProved : Prop
  monopoleSphereSpectrumMultiplicityFormalized : Prop
  circleReducedDeterminantCutoffConstructed : Prop
  cutoffRemainderTelescopeProved : Prop
  geometricRemainderConvergenceCriterionProved : Prop
  quadraticRemainderConvergenceCriterionProved : Prop
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
  arithmeticTwoTenCandidateFormalized : Prop
  centralPinBosonicQuarterNoGoProved : Prop
  centralPinOneFiveStandardSignNoGoProved : Prop
  primitiveIndexFiveSelectionDerived : Prop
  intrinsicThreeDimensionalSpinTwoWeightFiveNoGoProved : Prop
  independentInternalZ4BosonicEscapeFormalized : Prop
  actualGlobalDiracOperatorConstructed : Prop
  separatedInfiniteSpectrumProved : Prop
  heatTraceAsymptoticsProved : Prop
  zetaAndEtaContinuationProved : Prop
  finiteCountertermsDerivedMicroscopically : Prop
  stableModulusDerivedSchemeIndependently : Prop
  terminalRGChargeSynthesisFormalized : Prop
  generatedMassDerivedNoFit : Prop
  independentUVScaleDerived : Prop
  diracLLBimetricLockDerived : Prop
  bulkBoundaryChargeCompatibilityDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerivedNoFit : Prop

/-- Algebraic/local/statistics D7 milestone. -/
def localSpectralFoundationClosed (s : ProgramStatus) : Prop :=
  s.universalClosedA0A2A4Formalized /\
  s.rankTwoDiracTraceReductionFormalized /\
  s.productThroatCurvatureIntegralsComputed /\
  s.productThroatDiracCoefficientsMatched /\
  s.productThroatLocalCountertermConstructed /\
  s.commonHolonomyCountertermBridgeConstructed /\
  s.fixedHeatSchemeDeterminantUniqueProved /\
  s.monopoleSphereSpectrumMultiplicityFormalized /\
  s.circleReducedDeterminantCutoffConstructed /\
  s.cutoffRemainderTelescopeProved /\
  s.geometricRemainderConvergenceCriterionProved /\
  s.quadraticRemainderConvergenceCriterionProved /\
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
  s.competingSectorStabilizationCriterionDerived /\
  s.arithmeticTwoTenCandidateFormalized /\
  s.centralPinBosonicQuarterNoGoProved /\
  s.centralPinOneFiveStandardSignNoGoProved /\
  s.primitiveIndexFiveSelectionDerived /\
  s.intrinsicThreeDimensionalSpinTwoWeightFiveNoGoProved /\
  s.independentInternalZ4BosonicEscapeFormalized

/-- Full analytic D7 closure before the absolute-scale interface. -/
def analyticSpectralTheoryClosed (s : ProgramStatus) : Prop :=
  localSpectralFoundationClosed s /\
  s.actualGlobalDiracOperatorConstructed /\
  s.separatedInfiniteSpectrumProved /\
  s.heatTraceAsymptoticsProved /\
  s.zetaAndEtaContinuationProved /\
  s.finiteCountertermsDerivedMicroscopically /\
  s.stableModulusDerivedSchemeIndependently

/-- Absolute predictive D7 closure. -/
def fullD7Closure (s : ProgramStatus) : Prop :=
  analyticSpectralTheoryClosed s /\
  s.terminalRGChargeSynthesisFormalized /\
  s.generatedMassDerivedNoFit /\
  s.independentUVScaleDerived /\
  s.diracLLBimetricLockDerived /\
  s.bulkBoundaryChargeCompatibilityDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerivedNoFit

/-- Local heat coefficients and a co-scaled cutoff cannot close the absolute scale. -/
theorem local_foundation_without_uv_anchor_does_not_close_absolute_alpha
    (s : ProgramStatus)
    (_hLocal : localSpectralFoundationClosed s)
    (hMissing : Not s.independentUVScaleDerived) :
    Not (fullD7Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, hUV, _, _, _, _⟩
  exact hMissing hUV

/-- A fitted finite counterterm is not a scheme-independent modulus theorem. -/
theorem fitted_counterterm_without_microscopic_derivation_blocks_analytic_closure
    (s : ProgramStatus)
    (hMissing : Not s.finiteCountertermsDerivedMicroscopically) :
    Not (analyticSpectralTheoryClosed s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, _, _, hCounterterm, _⟩
  exact hMissing hCounterterm

/-- Missing bulk/boundary charge compatibility prevents the final synthesis. -/
theorem missing_charge_compatibility_blocks_full_d7
    (s : ProgramStatus)
    (hMissing : Not s.bulkBoundaryChargeCompatibilityDerived) :
    Not (fullD7Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, _, _, hCompatibility, _, _⟩
  exact hMissing hCompatibility

end JanusFundamentalGeometryD7SpectralTheory
end JanusFormal
