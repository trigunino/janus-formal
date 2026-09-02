import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4DCalculus

/-!
# Closure of the nonlinear full-BRST relational chart

This continuation records the Abelian zero-nonminimal reduction and its
canonical full-core representative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 8000000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldClosure :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩


variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceClosure :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldClosure :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceClosure :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceClosure :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteClosure :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FullBRSTChart

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private theorem zeroGlobalAbelianNakanishiLautrupField_field :
    (zeroGlobalAbelianNakanishiLautrupField period hPeriod).field = 0 :=
  rfl

private theorem zeroGlobalAbelianAntighostField_field :
    (zeroGlobalAbelianAntighostField period hPeriod).field = 0 :=
  rfl

private theorem globalGaugeLiePairingAt_zero_left
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod 0 field point = 0 := by
  simpa only [zero_smul, zero_mul] using
    (globalGaugeLiePairingAt_smul_first period hPeriod 0
      (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) field point)

/-- The Abelian gauge-fixing action vanishes when its `c/cbar/B` fields are
zero, without constraining the physical potential. -/
theorem globalPairedAbelianGaugeFermionBRSTAction_zero_nonminimal
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
        { potential := potential
          nonminimal := fun _ =>
            zeroGlobalAbelianNonminimalFields period hPeriod }
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
  unfold globalPairedAbelianGaugeFermionBRSTAction
    globalPairedAbelianGaugeFermionBRSTDensity
    zeroGlobalAbelianNonminimalFields
  simp only [zeroGlobalAbelianNakanishiLautrupField_field,
    zeroGlobalAbelianAntighostField_field,
    globalGaugeLiePairingAt_zero_left, mul_zero, zero_sub, neg_zero, add_zero,
    Finset.sum_const_zero, integral_zero]

/-- Canonical core slice with both nonminimal BRST sectors fixed at zero. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore
    (physical : GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period
      hPeriod configuration)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration :=
  (physical,
    (zeroGlobalDiffeomorphismNonminimalFields period hPeriod,
      { potential := potential
        nonminimal := fun _ =>
          zeroGlobalAbelianNonminimalFields period hPeriod }))

end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
