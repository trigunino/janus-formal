import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Densely defined genuine Hessian operator on the original L² smooth state image. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianL2OperatorCore4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

open P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D
open P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D
open P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
open P0EFTJanusProgramPT12DeDonderL2Closed4D

open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
open P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
open P0EFTJanusProgramPT12SignedBRSTGram4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace

open P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
open P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D

open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

theorem hessianSmoothDomain_add (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFeatureSmoothDomain period hPeriod metric (first + second) =
      hessianFeatureSmoothDomain period hPeriod metric first + hessianFeatureSmoothDomain period hPeriod metric second :=
  Subtype.ext ((diffeomorphismL2Smooth period hPeriod (metric .plus)).map_add first second)

theorem hessianSmoothDomain_smul (scalar : Real) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFeatureSmoothDomain period hPeriod metric (scalar • field) =
      scalar • hessianFeatureSmoothDomain period hPeriod metric field :=
  Subtype.ext ((diffeomorphismL2Smooth period hPeriod (metric .plus)).map_smul scalar field)

def hessianSmoothRieszLinearMap : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) where
  toFun := hessianSmoothRiesz period hPeriod reference metric couplings
  map_add' first second := by
    apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).eq_of_inner_left (𝕜 := Real)
    intro test
    have h (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :=
      hessianSmoothRiesz_pairing period hPeriod reference metric couplings field (hessianFeatureSmoothDomain period hPeriod metric test)
    change inner Real (hessianSmoothRiesz period hPeriod reference metric couplings (first + second))
      (hessianFeatureSmoothDomain period hPeriod metric test).val = _
    rw [h, inner_add_left]
    change _ = inner Real (hessianSmoothRiesz period hPeriod reference metric couplings first)
      (hessianFeatureSmoothDomain period hPeriod metric test).val +
      inner Real (hessianSmoothRiesz period hPeriod reference metric couplings second)
        (hessianFeatureSmoothDomain period hPeriod metric test).val
    rw [h, h, hessianSmoothDomain_add]
    simp only [hessianL2Form, hessianSectorForm_add_left]
    ring
  map_smul' scalar field := by
    apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).eq_of_inner_left (𝕜 := Real)
    intro test
    have h (input : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :=
      hessianSmoothRiesz_pairing period hPeriod reference metric couplings input (hessianFeatureSmoothDomain period hPeriod metric test)
    change inner Real (hessianSmoothRiesz period hPeriod reference metric couplings (scalar • field))
      (hessianFeatureSmoothDomain period hPeriod metric test).val = _
    rw [h]
    simp only [RingHom.id_apply]
    rw [real_inner_smul_left (hessianSmoothRiesz period hPeriod reference metric couplings field)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) test) scalar]
    change _ = scalar * inner Real (hessianSmoothRiesz period hPeriod reference metric couplings field)
      (hessianFeatureSmoothDomain period hPeriod metric test).val
    rw [h, hessianSmoothDomain_smul]
    simp only [hessianL2Form, hessianSectorForm_smul_left]
    ring

private def hessianOperatorSmoothEquivDomain : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ≃ₗ[Real]
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  LinearEquiv.ofInjective (diffeomorphismL2Smooth period hPeriod (metric .plus))
    (diffeomorphismL2Smooth_injective period hPeriod (metric .plus))

def hessianL2OperatorCore : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) where
  domain := (diffeomorphismL2Smooth period hPeriod (metric .plus)).range
  toFun := (hessianSmoothRieszLinearMap period hPeriod reference metric couplings).comp
    (hessianOperatorSmoothEquivDomain period hPeriod metric).symm.toLinearMap

theorem hessianL2OperatorCore_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianL2OperatorCore period hPeriod reference metric couplings
      ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field, ⟨field, rfl⟩⟩ =
      hessianSmoothRiesz period hPeriod reference metric couplings field := by
  change hessianSmoothRieszLinearMap period hPeriod reference metric couplings
    ((hessianOperatorSmoothEquivDomain period hPeriod metric).symm
      ((hessianOperatorSmoothEquivDomain period hPeriod metric) field)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem hessianL2OperatorCore_denseDomain : Dense
    ((hessianL2OperatorCore period hPeriod reference metric couplings).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)

theorem hessianSmoothRiesz_symmetric (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianSmoothRiesz period hPeriod reference metric couplings first)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) =
    inner Real (diffeomorphismL2Smooth period hPeriod (metric .plus) first)
      (hessianSmoothRiesz period hPeriod reference metric couplings second) :=
  (hessianSmoothRiesz_pairing period hPeriod reference metric couplings first
    (hessianFeatureSmoothDomain period hPeriod metric second)).trans
      ((hessianL2Form_comm period hPeriod reference metric couplings _ _).trans
        ((hessianSmoothRiesz_pairing period hPeriod reference metric couplings second
          (hessianFeatureSmoothDomain period hPeriod metric first)).symm.trans (real_inner_comm _ _)))

theorem hessianL2OperatorCore_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus))
      (hessianL2OperatorCore period hPeriod reference metric couplings)
      (hessianL2OperatorCore period hPeriod reference metric couplings) := by
  rintro ⟨first, hFirst⟩ ⟨second, hSecond⟩
  obtain ⟨x, rfl⟩ := hFirst
  obtain ⟨y, rfl⟩ := hSecond
  rw [hessianL2OperatorCore_smooth, hessianL2OperatorCore_smooth]
  exact hessianSmoothRiesz_symmetric period hPeriod reference metric couplings x y

end
end JanusFormal.P0EFTJanusProgramPT12HessianL2OperatorCore4D
