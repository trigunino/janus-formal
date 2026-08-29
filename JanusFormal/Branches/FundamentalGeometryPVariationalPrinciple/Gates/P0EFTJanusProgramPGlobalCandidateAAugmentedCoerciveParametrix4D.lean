import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D

/-!
# Canonical Candidate-A parametrix from coercivity and shifted surjectivity

The augmented Candidate-A generalized inverse is no longer an independent
packet.  It is the inverse of `H + P`, where `P` is the finite defect projector.
The identities proved by the generic coercive-shift layer identify both H12
defects with `P` itself.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D

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

private theorem finiteDimensional_range_of_eq_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {operator : E →L[Real] E}
    (shift : FiniteDefectCoerciveShiftData operator)
    (defect : E →L[Real] E)
    (hDefect : defect = shift.projection) :
    FiniteDimensional Real defect.range := by
  subst defect
  exact shift.projection_range_finite

/-- The canonical bounded Candidate-A parametrix. -/
noncomputable def globalCandidateAAugmentedCoerciveParametrix
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (hSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :=
  @finiteDefectCanonicalParametrix
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical) shift hSurjective

/-- The canonical left H12 defect equals the finite projector. -/
theorem globalCandidateAAugmentedKernelDefect_eq_projection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (hSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :
    globalCandidateAAugmentedKernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective) =
      @FiniteDefectCoerciveShiftData.projection
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift := by
  letI := augmentedFredholmNormedAddCommGroup period hPeriod configuration data
    analysis
  letI := augmentedFredholmNormedSpace period hPeriod configuration data analysis
  letI := augmentedFredholmModule period hPeriod configuration data analysis
  apply @ContinuousLinearMap.ext Real Real inferInstance inferInstance
    (RingHom.id Real)
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance
    (augmentedFredholmModule period hPeriod configuration data analysis)
    (augmentedFredholmModule period hPeriod configuration data analysis) _ _
  intro vector
  change vector -
      (@finiteDefectCanonicalParametrix
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift hSurjective)
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical vector) =
    (@FiniteDefectCoerciveShiftData.projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift) vector
  have hVector :=
    @finiteDefectCanonicalParametrix_operator_apply
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift hSurjective
      vector
  exact (congrArg (fun value => vector - value) hVector).trans
    (sub_sub_cancel vector _)

/-- The canonical right H12 defect equals the same finite projector. -/
theorem globalCandidateAAugmentedCokernelDefect_eq_projection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (hSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :
    globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective) =
      @FiniteDefectCoerciveShiftData.projection
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift := by
  letI := augmentedFredholmNormedAddCommGroup period hPeriod configuration data
    analysis
  letI := augmentedFredholmNormedSpace period hPeriod configuration data analysis
  letI := augmentedFredholmModule period hPeriod configuration data analysis
  apply @ContinuousLinearMap.ext Real Real inferInstance inferInstance
    (RingHom.id Real)
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance
    (augmentedFredholmModule period hPeriod configuration data analysis)
    (augmentedFredholmModule period hPeriod configuration data analysis) _ _
  intro vector
  change vector -
      globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical
          ((@finiteDefectCanonicalParametrix
            (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
              configuration data analysis)
            (augmentedFredholmNormedAddCommGroup period hPeriod configuration
              data analysis)
            (augmentedFredholmNormedSpace period hPeriod configuration data
              analysis)
            (augmentedFredholmCompleteSpace period hPeriod configuration data
              analysis)
            (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
              configuration data analysis chart sameAction physical) shift
                hSurjective) vector) =
    (@FiniteDefectCoerciveShiftData.projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift) vector
  have hVector :=
    @operator_finiteDefectCanonicalParametrix_apply
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift hSurjective
      vector
  exact (congrArg (fun value => vector - value) hVector).trans
    (sub_sub_cancel vector _)

/-- Construct the pre-existing generalized-inverse H12 packet from the
coercive shift and its surjectivity. -/
noncomputable def globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (hSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift))
    (hLLStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :
    GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period hPeriod
      configuration data analysis chart sameAction physical := by
  letI := augmentedFredholmNormedAddCommGroup period hPeriod configuration data
    analysis
  letI := augmentedFredholmNormedSpace period hPeriod configuration data analysis
  letI := augmentedFredholmModule period hPeriod configuration data analysis
  letI := augmentedFredholmCompleteSpace period hPeriod configuration data analysis
  refine {
  parametrix := globalCandidateAAugmentedCoerciveParametrix period hPeriod
    configuration data analysis chart sameAction physical shift hSurjective
  generalized_inverse :=
    @operator_parametrix_operator
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift hSurjective
  kernelDefect_range_finite := by
    exact @finiteDimensional_range_of_eq_projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift
      (globalCandidateAAugmentedKernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective))
      (globalCandidateAAugmentedKernelDefect_eq_projection period hPeriod
        configuration data analysis chart sameAction physical shift hSurjective)
  cokernelDefect_range_finite := by
    exact @finiteDimensional_range_of_eq_projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift
      (globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective))
      (globalCandidateAAugmentedCokernelDefect_eq_projection period hPeriod
        configuration data analysis chart sameAction physical shift hSurjective)
  ll_stationary := hLLStationary
  }

/-- Full H12 gate through the existing generalized-inverse adapter. -/
def global_candidateA_h12_fredholm_gate_of_coerciveShift
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (hSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift))
    (hLLStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
    period hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
        period hPeriod configuration data analysis chart sameAction physical
          shift hSurjective hLLStationary)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D
end JanusFormal
