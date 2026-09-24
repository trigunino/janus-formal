import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowFrame4D

/-! An inhabited open core for the existing complete bulk action at the intrinsic metric pair. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

variable (couplings : GlobalCandidateAActionCouplings)

abbrev IntrinsicBulkCore := FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
  period hPeriod (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod) couplings

local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod) couplings

def intrinsicBulkDomain : Set (IntrinsicBulkCore period hPeriod couplings) :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
    (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod)
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) couplings

def intrinsicBulkAction (interactionScale : Real) (coefficients : PotentialCoefficients) :
    IntrinsicBulkCore period hPeriod couplings → Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
    (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod)
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) couplings interactionScale coefficients

theorem intrinsicBulkMinusCenter_eq_zero :
    finiteFramePairedC2MinusCenter period hPeriod (intrinsicBulkGeometry period hPeriod)
      (canonicalTenFlowFrame period hPeriod) = 0 := by
  have hMetrics : (intrinsicBulkGeometry period hPeriod).minusMetric =
      (intrinsicBulkGeometry period hPeriod).plusMetric := rfl
  unfold finiteFramePairedC2MinusCenter
  rw [hMetrics, sub_self, map_zero]

theorem intrinsicBulkDomain_zero_mem :
    (0 : IntrinsicBulkCore period hPeriod couplings) ∈ intrinsicBulkDomain period hPeriod couplings := by
  apply zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain
    period hPeriod (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod)
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) couplings
  rw [intrinsicBulkMinusCenter_eq_zero]
  exact zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod
    (canonicalTenFlowFrame period hPeriod) (intrinsicBulkGeometry period hPeriod).plusMetric

theorem intrinsicBulkDomain_isOpen : IsOpen (intrinsicBulkDomain period hPeriod couplings) :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain_isOpen period hPeriod
    (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod)
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) couplings

theorem intrinsicBulkDomain_nonempty : (intrinsicBulkDomain period hPeriod couplings).Nonempty :=
  ⟨0, intrinsicBulkDomain_zero_mem period hPeriod couplings⟩

theorem intrinsicBulkAction_contDiffAt_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffAt Real 2 (intrinsicBulkAction period hPeriod couplings interactionScale coefficients) 0 := by
  exact ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_contDiffOn_two
    period hPeriod (intrinsicBulkGeometry period hPeriod) (canonicalTenFlowFrame period hPeriod)
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) couplings interactionScale coefficients)
      0 (intrinsicBulkDomain_zero_mem period hPeriod couplings)).contDiffAt
        ((intrinsicBulkDomain_isOpen period hPeriod couplings).mem_nhds
          (intrinsicBulkDomain_zero_mem period hPeriod couplings))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
