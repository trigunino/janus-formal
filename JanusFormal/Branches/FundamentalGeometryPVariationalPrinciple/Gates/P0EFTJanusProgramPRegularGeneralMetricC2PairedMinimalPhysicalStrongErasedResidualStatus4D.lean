import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D

/-!
# Honest residual status for the erased normal and ghost sectors

The current minimal physical target forgets the normal and diffeomorphism-
ghost coordinates.  Their Euler covectors therefore vanish kinematically.
This gate gives those sectors a singleton residual carrier that records that
architectural status; it deliberately does not advertise a derived dynamical
field equation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedResidualStatus4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Singleton marker: the component is absent from the current target rather
than constrained by an independently derived Euler equation. -/
inductive KinematicallyErasedEulerResidual where
  | erased

/-- A zero covector represented by the explicit singleton erasure status. -/
def kinematicallyErasedPDEResidualRepresentation
    {Test : Type*} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) (hCovector : covector = 0) :
    SeparatingPDEResidualRepresentation covector where
  Residual := KinematicallyErasedEulerResidual
  zeroResidual := .erased
  residual := .erased
  pairing := fun _ _ => 0
  represents := by
    intro test
    rw [hCovector]
    rfl
  separates := by simp

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

def regularGeneralMetricC2PairedMinimalPhysicalStrongNormalErasedResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongNormalEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact kinematicallyErasedPDEResidualRepresentation _
    (regular_general_metric_c2_paired_minimal_physical_strong_erased_sector_euler_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
          hPoint).1

def regularGeneralMetricC2PairedMinimalPhysicalStrongGhostErasedResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact kinematicallyErasedPDEResidualRepresentation _
    (regular_general_metric_c2_paired_minimal_physical_strong_erased_sector_euler_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
          hPoint).2

/-- Latest physical PDE package with normal and ghost status made explicit. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongErasedStatusPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase point hPoint hPlus hMinus with
    normal :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongNormalErasedResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint
    diffeomorphismGhost :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGhostErasedResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint }

def RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedStatusSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedStatusPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase point hPoint hPlus hMinus)

/-- Gate marker: the full Euler equivalence is preserved, while the two
erased sectors are now explicitly classified as kinematic singleton statuses.
-/
theorem regular_general_metric_c2_paired_minimal_physical_strong_erased_residual_status_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedStatusSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedStatusPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase point hPoint hPlus hMinus)

end
end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedResidualStatus4D
end JanusFormal
