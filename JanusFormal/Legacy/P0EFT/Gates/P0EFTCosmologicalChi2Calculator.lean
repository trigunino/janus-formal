import JanusFormal.Legacy.P0EFT.Gates.P0EFTObservationalFSigma8Data

namespace JanusFormal
namespace P0EFTCosmologicalChi2Calculator

set_option autoImplicit false

structure CosmologicalChi2Calculator where
  sdssDataLoaded : Prop
  janusCurveLoaded : Prop
  interpolationDefined : Prop
  diagonalChi2Computed : Prop
  bestAmplitudeComputed : Prop
  fullCovarianceUsed : Prop
  desiPlanckIncluded : Prop
  fullLikelihoodReady : Prop

def sdssDiagonalChi2Ready (c : CosmologicalChi2Calculator) : Prop :=
  c.sdssDataLoaded /\
  c.janusCurveLoaded /\
  c.interpolationDefined /\
  c.diagonalChi2Computed /\
  c.bestAmplitudeComputed

def fullLikelihoodReady (c : CosmologicalChi2Calculator) : Prop :=
  sdssDiagonalChi2Ready c /\
  c.fullCovarianceUsed /\
  c.desiPlanckIncluded /\
  c.fullLikelihoodReady

def sdssFullCovarianceReady (c : CosmologicalChi2Calculator) : Prop :=
  sdssDiagonalChi2Ready c /\
  c.fullCovarianceUsed

theorem sdss_diagonal_chi2_is_first_likelihood_gate
    (c : CosmologicalChi2Calculator)
    (hData : c.sdssDataLoaded)
    (hCurve : c.janusCurveLoaded)
    (hInterp : c.interpolationDefined)
    (hChi2 : c.diagonalChi2Computed)
    (hAmp : c.bestAmplitudeComputed) :
    sdssDiagonalChi2Ready c := by
  exact And.intro hData
    (And.intro hCurve
      (And.intro hInterp
        (And.intro hChi2 hAmp)))

theorem missing_full_covariance_blocks_full_likelihood
    (c : CosmologicalChi2Calculator)
    (hMissing : Not c.fullCovarianceUsed) :
    Not (fullLikelihoodReady c) := by
  intro h
  exact hMissing h.right.left

theorem sdss_full_covariance_closes_first_covariance_gate
    (c : CosmologicalChi2Calculator)
    (hDiag : sdssDiagonalChi2Ready c)
    (hFullCov : c.fullCovarianceUsed) :
    sdssFullCovarianceReady c := by
  exact And.intro hDiag hFullCov

theorem missing_desi_planck_blocks_full_likelihood
    (c : CosmologicalChi2Calculator)
    (hMissing : Not c.desiPlanckIncluded) :
    Not (fullLikelihoodReady c) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTCosmologicalChi2Calculator
end JanusFormal
