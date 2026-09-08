import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

/-! # Frozen-volume decomposition of the finite-frame Einstein--Hilbert Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

local notation "Model" =>
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric

local notation "Domain" =>
  generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric

/-- Einstein--Hilbert density with the canonical volume coefficient frozen
at the chart center. -/
def finiteFrameC2FrozenVolumeEinsteinHilbertDensity
    (couplings : EinsteinHilbertCouplings) (variation : Model) :=
  finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric 0 *
    ((1 / (2 * couplings.gravitationalCoupling)) •
      (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric variation -
        finiteFrameC0Constant period hPeriod (2 * couplings.cosmologicalConstant)))

/-- Integrated Einstein--Hilbert action with center-frozen volume. -/
def finiteFrameC2FrozenVolumeEinsteinHilbertAction
    (couplings : EinsteinHilbertCouplings) (variation : Model) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2FrozenVolumeEinsteinHilbertDensity period hPeriod frame baseMetric
      couplings variation)

/-- Exact action contribution caused by moving the canonical volume. -/
def finiteFrameC2EinsteinHilbertVolumeDefectAction
    (couplings : EinsteinHilbertCouplings) (variation : Model) : Real :=
  finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings variation -
    finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings
      variation

theorem finiteFrameC2EinsteinHilbertAction_eq_frozen_add_volumeDefect
    (couplings : EinsteinHilbertCouplings) (variation : Model) :
    finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings variation =
      finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings
          variation +
        finiteFrameC2EinsteinHilbertVolumeDefectAction period hPeriod frame baseMetric couplings
          variation := by
  unfold finiteFrameC2EinsteinHilbertVolumeDefectAction
  abel

theorem finiteFrameC2FrozenVolumeEinsteinHilbertAction_contDiffOn_two
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings)
      Domain := by
  have hCurvature : ContDiffOn Real 2
      (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric) Domain :=
    (finiteFrameProjectedScalarCurvatureC0_contDiffOn_two period hPeriod frame baseMetric).mono
      (fun _ hVariation => hVariation.1)
  have hVolume : ContDiffOn Real 2
      (fun _ : Model => finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric 0) Domain :=
    contDiffOn_const
  have hConstant : ContDiffOn Real 2
      (fun _ : Model => finiteFrameC0Constant period hPeriod
        (2 * couplings.cosmologicalConstant)) Domain :=
    contDiffOn_const
  have hScaled : ContDiffOn Real 2
      (fun variation : Model =>
        (1 / (2 * couplings.gravitationalCoupling)) •
          (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric variation -
            finiteFrameC0Constant period hPeriod (2 * couplings.cosmologicalConstant))) Domain :=
    (hCurvature.sub hConstant).const_smul
      (1 / (2 * couplings.gravitationalCoupling))
  have hDensity : ContDiffOn Real 2
      (finiteFrameC2FrozenVolumeEinsteinHilbertDensity period hPeriod frame baseMetric couplings)
      Domain :=
    hVolume.mul hScaled
  exact (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn hDensity

theorem finiteFrameC2EinsteinHilbertVolumeDefectAction_contDiffOn_two
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (finiteFrameC2EinsteinHilbertVolumeDefectAction period hPeriod frame baseMetric couplings)
      Domain :=
  (finiteFrameC2EinsteinHilbertAction_contDiffOn_two period hPeriod frame baseMetric couplings).sub
    (finiteFrameC2FrozenVolumeEinsteinHilbertAction_contDiffOn_two period hPeriod frame baseMetric
      couplings)

def finiteFrameC2FrozenVolumeEinsteinHilbertEuler
    (couplings : EinsteinHilbertCouplings) (variation : Model) : Model →L[Real] Real :=
  fderiv Real
    (finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings)
    variation

theorem finiteFrameC2FrozenVolumeEinsteinHilbertAction_hasFDerivAt_zero
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings)
      (finiteFrameC2FrozenVolumeEinsteinHilbertEuler period hPeriod frame baseMetric couplings 0)
      0 := by
  have hContDiffAt :=
    ((finiteFrameC2FrozenVolumeEinsteinHilbertAction_contDiffOn_two period hPeriod frame
      baseMetric couplings) 0
        (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)).contDiffAt
          ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).mem_nhds
            (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric))
  exact (hContDiffAt.differentiableAt (by norm_num)).hasFDerivAt

def finiteFrameC2EinsteinHilbertVolumeDefectEuler
    (couplings : EinsteinHilbertCouplings) (variation : Model) : Model →L[Real] Real :=
  fderiv Real
    (finiteFrameC2EinsteinHilbertVolumeDefectAction period hPeriod frame baseMetric couplings)
    variation

/-- The mobile-volume Euler is the frozen-volume Euler plus its exact volume defect. -/
theorem finiteFrameC2EinsteinHilbertEuler_eq_frozen_add_volumeDefect
    (couplings : EinsteinHilbertCouplings) (variation : Model)
    (hVariation : variation ∈ Domain) :
    finiteFrameC2EinsteinHilbertEuler period hPeriod frame baseMetric couplings variation =
      finiteFrameC2FrozenVolumeEinsteinHilbertEuler period hPeriod frame baseMetric couplings
          variation +
        finiteFrameC2EinsteinHilbertVolumeDefectEuler period hPeriod frame baseMetric couplings
          variation := by
  have hOpen := generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric
  have hMobile : DifferentiableAt Real
      (finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings) variation :=
    (((finiteFrameC2EinsteinHilbertAction_contDiffOn_two period hPeriod frame baseMetric couplings
      variation hVariation).contDiffAt (hOpen.mem_nhds hVariation)).differentiableAt
        (by norm_num))
  have hFrozen : DifferentiableAt Real
      (finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings)
      variation :=
    (((finiteFrameC2FrozenVolumeEinsteinHilbertAction_contDiffOn_two period hPeriod frame baseMetric
      couplings variation hVariation).contDiffAt (hOpen.mem_nhds hVariation)).differentiableAt
        (by norm_num))
  have hDerivative := fderiv_sub hMobile hFrozen
  unfold finiteFrameC2EinsteinHilbertEuler finiteFrameC2FrozenVolumeEinsteinHilbertEuler
    finiteFrameC2EinsteinHilbertVolumeDefectEuler
    finiteFrameC2EinsteinHilbertVolumeDefectAction
  have hFunctions :
      finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings -
          finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings =
        fun current =>
          finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings current -
            finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame baseMetric couplings
              current := by
    funext current
    rfl
  rw [(congrArg (fun action => fderiv Real action variation) hFunctions).symm.trans hDerivative]
  abel

end
end P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
end JanusFormal
