import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

/-!
# Canonical divergence-free LL geometric Stokes closure

The canonical quotient-time generator and the three round-sphere rotations
preserve the canonical throat measure.  Their proved global IPP therefore
inhabits the existing geometric Stokes interface with zero boundary flux and
makes the weak and strong PT-symmetric LL equations unconditionally equivalent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D
open P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The proved measure-preserving canonical frame supplies the full geometric
Stokes contract, with the correct zero boundary term on the closed throat. -/
def canonicalDivergenceFreeLLFrameGeometricStokesContract
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) :
    CanonicalThroatGeometricStokesContractFor period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields regularity :=
  (canonicalDivergenceFreeLLFrame_globalIPP period hPeriod fields regularity)
    |>.toGeometricStokesContract period hPeriod

/-- The canonical geometric Stokes interface is unconditionally inhabited. -/
theorem canonicalDivergenceFreeLLFrame_geometricStokesContract_nonempty
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) :
    Nonempty (CanonicalThroatGeometricStokesContractFor period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields regularity) :=
  ⟨canonicalDivergenceFreeLLFrameGeometricStokesContract period hPeriod
    fields regularity⟩

/-- For the retained canonical LL frame, the weak integrated Euler equation
and the pointwise strong equation are exactly equivalent. -/
theorem canonicalDivergenceFreeLLFrame_weak_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields :=
  canonicalThroat_globalIPP_weak_iff_strong_for period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) fields regularity
    (canonicalDivergenceFreeLLFrame_globalIPP period hPeriod fields regularity)

/-- Stationarity of the retained PT-symmetric LL action is therefore exactly
the strong canonical-frame PDE, with no residual boundary hypothesis. -/
theorem canonicalDivergenceFreeLLFrame_stationary_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields := by
  let contract := canonicalDivergenceFreeLLFrameGeometricStokesContract
    period hPeriod fields regularity
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  exact ptSymmetricDifferentialLLFluxStationary_iff_strong period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (contract.toStrongLLIntegrationByParts period hPeriod)
    (contract.satisfiesNaturalBoundaryCondition period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D
end JanusFormal
