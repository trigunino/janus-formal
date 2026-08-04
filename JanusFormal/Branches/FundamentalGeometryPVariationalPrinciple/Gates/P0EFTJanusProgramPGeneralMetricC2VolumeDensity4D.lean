import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D

/-!
# Local C² volume density for general metric variations

The relative metric is the genuine open family `I + g⁻¹h`.  Its finite-frame
determinant is intrinsic because `g⁻¹h` lies in the projector corner and the
ambient complement is the identity.  Pulling the determinant back through the
positive scalar root chart gives the local volume ratio.  Multiplication by an
arbitrary smooth base volume yields the varied C² density.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Relative determinant of the genuine metric family `I + g⁻¹h`. -/
def generalMetricRelativeC2Determinant
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) : C2Scalar period hPeriod :=
  c2FiniteMatrixDeterminant period hPeriod frame.count
    (generalMetricRelativeC2ExtendedMatrix
      period hPeriod frame baseMetric variation)

theorem generalMetricRelativeC2Determinant_contDiff
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞
      (generalMetricRelativeC2Determinant
        period hPeriod frame baseMetric) :=
  (c2FiniteMatrixDeterminant_contDiff
    period hPeriod frame.count).fun_comp
      (generalMetricRelativeC2ExtendedMatrix_contDiff
        period hPeriod frame baseMetric)

theorem generalMetricRelativeC2Determinant_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    generalMetricRelativeC2Determinant period hPeriod frame baseMetric 0 =
      c2ScalarOne period hPeriod := by
  rw [generalMetricRelativeC2Determinant]
  change c2FiniteMatrixDeterminant period hPeriod frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count + 0) = _
  simpa using c2FiniteMatrixDeterminant_identity
    period hPeriod frame.count

/-- Open metric domain on which both the inverse metric and the selected
positive volume root exist. -/
def generalMetricRelativeC2VolumeDomain
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Set (GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ∩
    generalMetricRelativeC2Determinant period hPeriod frame baseMetric ⁻¹'
      c2ScalarLocalRootTarget period hPeriod

theorem generalMetricRelativeC2VolumeDomain_isOpen
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    IsOpen (generalMetricRelativeC2VolumeDomain
      period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen
    period hPeriod frame baseMetric).inter
      ((c2ScalarLocalRootTarget_isOpen period hPeriod).preimage
        (generalMetricRelativeC2Determinant_contDiff
          period hPeriod frame baseMetric).continuous)

theorem zero_mem_generalMetricRelativeC2VolumeDomain
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) ∈
      generalMetricRelativeC2VolumeDomain
        period hPeriod frame baseMetric := by
  exact ⟨zero_mem_generalMetricRelativeC2OpenDomain
      period hPeriod frame baseMetric,
    by
      change generalMetricRelativeC2Determinant
          period hPeriod frame baseMetric 0 ∈
        c2ScalarLocalRootTarget period hPeriod
      rw [generalMetricRelativeC2Determinant_zero]
      exact c2ScalarOne_mem_localRootTarget period hPeriod⟩

/-- Positive local volume ratio `sqrt(det(I + g⁻¹h))`. -/
def generalMetricRelativeC2VolumeRatio
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) : C2Scalar period hPeriod :=
  c2ScalarLocalRootBranch period hPeriod
    (generalMetricRelativeC2Determinant
      period hPeriod frame baseMetric variation)

theorem generalMetricRelativeC2VolumeRatio_contDiffOn_two
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (generalMetricRelativeC2VolumeRatio
        period hPeriod frame baseMetric)
      (generalMetricRelativeC2VolumeDomain
        period hPeriod frame baseMetric) := by
  have hDeterminant : ContDiffOn Real 2
      (generalMetricRelativeC2Determinant
        period hPeriod frame baseMetric)
      (generalMetricRelativeC2VolumeDomain
        period hPeriod frame baseMetric) :=
    ((generalMetricRelativeC2Determinant_contDiff
      period hPeriod frame baseMetric).of_le
        (show (2 : ℕ∞) ≤ ∞ by
          exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  exact (c2ScalarLocalRootBranch_contDiffOn period hPeriod).comp
    hDeterminant
    (fun _ hVariation => hVariation.2)

theorem generalMetricRelativeC2VolumeRatio_square
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain
      period hPeriod frame baseMetric) :
    c2ScalarSquare period hPeriod
        (generalMetricRelativeC2VolumeRatio
          period hPeriod frame baseMetric variation) =
      generalMetricRelativeC2Determinant
        period hPeriod frame baseMetric variation :=
  c2ScalarLocalRootBranch_square period hPeriod hVariation.2

theorem generalMetricRelativeC2VolumeRatio_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric 0 =
      c2ScalarOne period hPeriod := by
  rw [generalMetricRelativeC2VolumeRatio,
    generalMetricRelativeC2Determinant_zero,
    c2ScalarLocalRootBranch_at_one]

/-- C² volume density relative to any genuine smooth base volume. -/
def generalMetricC2VolumeDensity
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) : C2Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod baseVolume)
    (generalMetricRelativeC2VolumeRatio
      period hPeriod frame baseMetric variation)

theorem generalMetricC2VolumeDensity_contDiffOn_two
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real) :
    ContDiffOn Real 2
      (generalMetricC2VolumeDensity
        period hPeriod frame baseMetric baseVolume)
      (generalMetricRelativeC2VolumeDomain
        period hPeriod frame baseMetric) := by
  exact (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore
        period hPeriod baseVolume)).contDiff.contDiffOn.comp
    (generalMetricRelativeC2VolumeRatio_contDiffOn_two
      period hPeriod frame baseMetric)
    (fun _ _ => mem_univ _)

theorem generalMetricC2VolumeDensity_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real) :
    generalMetricC2VolumeDensity
        period hPeriod frame baseMetric baseVolume 0 =
      smoothToCanonicalPhysicalScalarC2JetCore
        period hPeriod baseVolume := by
  rw [generalMetricC2VolumeDensity,
    generalMetricRelativeC2VolumeRatio_zero,
    c2Scalar_mul_one]

/-- Summary gate: a genuine open neighborhood of the base metric carries the
selected exact C² volume density. -/
theorem general_metric_c2_volume_density_gate
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real) :
    IsOpen (generalMetricRelativeC2VolumeDomain
        period hPeriod frame baseMetric) ∧
      (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) ∈
        generalMetricRelativeC2VolumeDomain
          period hPeriod frame baseMetric ∧
      ContDiffOn Real 2
        (generalMetricC2VolumeDensity
          period hPeriod frame baseMetric baseVolume)
        (generalMetricRelativeC2VolumeDomain
          period hPeriod frame baseMetric) ∧
      generalMetricC2VolumeDensity
          period hPeriod frame baseMetric baseVolume 0 =
        smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod baseVolume ∧
      ∀ variation,
        variation ∈ generalMetricRelativeC2VolumeDomain
            period hPeriod frame baseMetric →
          c2ScalarSquare period hPeriod
              (generalMetricRelativeC2VolumeRatio
                period hPeriod frame baseMetric variation) =
            generalMetricRelativeC2Determinant
              period hPeriod frame baseMetric variation := by
  exact ⟨generalMetricRelativeC2VolumeDomain_isOpen
      period hPeriod frame baseMetric,
    zero_mem_generalMetricRelativeC2VolumeDomain
      period hPeriod frame baseMetric,
    generalMetricC2VolumeDensity_contDiffOn_two
      period hPeriod frame baseMetric baseVolume,
    generalMetricC2VolumeDensity_zero
      period hPeriod frame baseMetric baseVolume,
    fun variation hVariation =>
      generalMetricRelativeC2VolumeRatio_square
        period hPeriod frame baseMetric variation hVariation⟩

end

end P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
end JanusFormal
