import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D

/-!
# Exact frontier of the global BRST/BV problem

The physical abelian gauge differential is nilpotent, the genuinely odd
exterior-valued diffeomorphism ghost satisfies its cubic Jacobi closure, and
the existing general-metric BV doublet is nilpotent and preserves the current
Program-P boundary domain.  The exact `U(1)²` action orbit is stationary.

This is not `BRST-GLOBAL-01`: the nonlinear exterior ghost has not yet been
extended to one derivation on every field, antifield and boundary component
of the assembled action.  The ordinary commuting-ghost construction is
proved trivial, so that missing exterior extension cannot be bypassed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBRSTFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalNoether4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Every currently constructed BRST layer, with its scope exposed. -/
structure ProgramPGlobalBRSTFrontierCertificate4D where
  abelianSquareZero : ∀ state : AbelianBRSTState period hPeriod,
    brstDifferential period hPeriod
        (brstDifferential period hPeriod state) =
      zeroBRSTState period hPeriod
  exteriorGhostJacobi : ∀ i j k first second third,
    cubicGhostBRSTJacobiObstruction period hPeriod i j k
        first second third = 0
  metricBVSquareZero : ∀ phase : SmoothGeneralMetricBVField period hPeriod,
    smoothGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVZero period hPeriod
  metricBVBoundaryStable :
    ∀ (domain : ProgramPCommonGeometricDomain4D period hPeriod)
      (variation : IndependentFieldVariation period hPeriod)
      (phase : SmoothGeneralMetricBVField period hPeriod),
      completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase) ∈
          programPBoundaryTangentDomain4D period hPeriod domain ↔
        completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
          programPBoundaryTangentDomain4D period hPeriod domain
  ordinaryGhostNoGo :
    (∀ ghost : SmoothDiffeomorphismGhost period hPeriod,
      ordinaryQuadraticGhostBRST period hPeriod ghost = 0) ∧
      ¬ ∃ ghost,
        ordinaryQuadraticGhostBRST period hPeriod ghost ≠ 0

def programPGlobalBRSTFrontierCertificate4D :
    ProgramPGlobalBRSTFrontierCertificate4D period hPeriod where
  abelianSquareZero := brstDifferential_square_zero period hPeriod
  exteriorGhostJacobi := by
    intro i j k first second third
    exact
      (exterior_diffeomorphism_ghost_brst4D_closure
        period hPeriod).2.2.2 i j k first second third
  metricBVSquareZero :=
    smoothGeneralMetricBVBRST_square_zero period hPeriod
  metricBVBoundaryStable :=
    completeVariationWithGeneralMetricBV_BRST_mem_boundaryDomain_iff
      period hPeriod
  ordinaryGhostNoGo :=
    ordinary_ghost_nonlinear_brst_noGo period hPeriod

/-- The exact assembled action is stationary along every paired smooth
abelian BRST ghost orbit. -/
theorem global_physical_u1_brst_action_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (ghosts : PhysicalPairedGaugeGhost period hPeriod) :
    HasDerivAt
      (globalCandidateAPhysicalGaugeOrbit
        period hPeriod data measure ghosts) 0 0 :=
  globalCandidateAPhysicalGaugeOrbit_hasDerivAt_zero
    period hPeriod data measure ghosts

theorem global_brst_frontier_gate :
    Nonempty (ProgramPGlobalBRSTFrontierCertificate4D period hPeriod) :=
  ⟨programPGlobalBRSTFrontierCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPGlobalBRSTFrontier4D
end JanusFormal
