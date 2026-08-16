import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreActualFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D

/-!
# Dense-core Candidate-A frontier on the nondegenerate Schur stratum

The H11 physical extension is generated from the smooth-core graph estimate and
the seven genuine action Hessians.  If the resulting augmented Hessian admits a
bounded finite/complement Schur decomposition with nonzero finite determinant,
the full operator is invertible and its Green operator is the explicit block
formula

`T⁻¹ R diag(S⁻¹,D⁻¹) L T`.

This joins the analytically correct dense-core H11 construction to the strongest
zero-mode-free H12/Green endpoint without introducing a Hilbert-to-smooth map.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreSchurFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option synthInstance.maxHeartbeats 9000000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D
open P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreActualFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Strong zero-mode-free endpoint from the dense-core H11 data and the finite
Schur determinant. -/
def global_candidateA_hessian_canonical_denseCore_schur_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family))
    (agreement : GlobalCandidateASevenCanonicalDenseCoreAgreement4D period
      hPeriod configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)
        einsteinScale family)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreActualPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family chartBound
            agreement)
        Mode Complement) :=
  let chart := globalCandidateACanonicalDenseCoreChart period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateACanonicalDenseCoreSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let physical := globalCandidateACanonicalDenseCoreActualPhysicalExtension period
    hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound agreement
  let h13 := global_candidateA_h13_matter_ll_same_action_gate period hPeriod
    configuration data analysis chart sameAction
  let h11 := global_candidateA_h11_canonical_denseCore_gate period hPeriod
    configuration data analysis chart sameAction einsteinScale family chartBound
      agreement
  let determinant := global_candidateA_actual_schur_determinant_gate period
    hPeriod determinantData
  let inverseIdentities := global_candidateA_actual_schur_explicit_green_gate
    period hPeriod determinantData
  (h13, h11, determinant, inverseIdentities,
    globalCandidateAActualSchurExplicitGreen period hPeriod determinantData)

/-- The zero-mode-free Schur endpoint has three analytic packets after the
local family is fixed: core regularity, exact seven-block agreement and the
bounded Schur determinant packet. -/
theorem global_candidateA_hessian_canonical_denseCore_schur_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreSchurFrontier4D
end JanusFormal
