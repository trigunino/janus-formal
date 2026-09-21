import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12D9NonnegativePairing4D

/-! The actual paired Abelian BRST form cannot be realized by the installed D9. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianBRSTActualD9NoGo4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D
open P0EFTJanusProgramPT12D9NonnegativePairing4D

attribute [local instance] complexDiagonalHilbertRealInnerProductSpace

/-- The installed nonnegative D9 target cannot realize the actual paired
Abelian BRST Hessian. Even a nonlinear, noninjective map cannot preserve all
self-pairings, so no linear common-core pairing realization exists. -/
theorem no_abelianBRST_actual_to_D9_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    ¬ ∃ realize : GlobalPairedAbelianBRSTState period hPeriod →
        (complexDiagonalRealOperator (iota × Fin 8)
          (d9GaugeGhostUnboundedWeight covector)).domain,
      ∀ core : GlobalPairedAbelianBRSTState period hPeriod,
        inner Real
          (complexDiagonalRealOperator (iota × Fin 8)
            (d9GaugeGhostUnboundedWeight covector) (realize core))
          (realize core : D9GaugeGhostUnboundedHilbert iota) =
        globalPairedAbelianOffShellHessian period hPeriod metric
          (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric core)
          (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric core) := by
  rintro ⟨realize, hPairing⟩
  obtain ⟨core, hNegative⟩ := exists_abelianBRST_negative_direction
    period hPeriod metric
  have hNonnegative := d9Real_pairing_nonneg covector (realize core)
  rw [hPairing core] at hNonnegative
  exact (not_le_of_gt hNegative) hNonnegative

end
end P0EFTJanusProgramPT12AbelianBRSTActualD9NoGo4D
end JanusFormal
