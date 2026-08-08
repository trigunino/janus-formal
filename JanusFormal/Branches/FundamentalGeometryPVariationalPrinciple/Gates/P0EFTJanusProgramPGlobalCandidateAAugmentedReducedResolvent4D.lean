import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D

/-!
# Real reduced resolvent of the augmented Candidate-A Hessian

The concrete H12 orthogonal-coercive packet supplies an exact zero-mode
projection and a positive lower bound on its complement.  The augmented
Candidate-A Riesz representative is already self-adjoint.  Hence every real
spectral parameter `lambda` with

`|lambda| < coercivityConstant`

lies in a certified resolvent interval for the true reduced Hessian.  The
resulting inverse has norm at most

`(coercivityConstant - |lambda|)⁻¹`.

At `lambda = 0` this construction is exactly the previously installed reduced
Green operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 3000000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedOperator4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedResolvent4D

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

private abbrev CandidateHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateResolventNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateResolventInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateResolventNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateResolventModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateResolventCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The actual reduced Candidate-A shift `H_red - lambda I`. -/
def globalCandidateAAugmentedReducedShiftedOperator
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (spectralParameter : Real) :=
  finiteDefectReducedShiftedOperator
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift spectralParameter

/-- Real Candidate-A resolvent on the exact zero-mode complement. -/
noncomputable def globalCandidateAAugmentedReducedRealResolvent
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| <
      shift.coerciveShift.coercivityConstant) :=
  finiteDefectReducedRealResolvent
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift spectralParameter hSpectral

/-- Exact inverse and norm bound for one real spectral parameter. -/
structure GlobalCandidateAAugmentedReducedResolventCertificate4D
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| <
      shift.coerciveShift.coercivityConstant) : Prop where
  leftInverse : Function.LeftInverse
    (globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
      data analysis chart sameAction physical shift spectralParameter hSpectral)
    (globalCandidateAAugmentedReducedShiftedOperator period hPeriod configuration
      data analysis chart sameAction physical shift spectralParameter)
  rightInverse : Function.RightInverse
    (globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
      data analysis chart sameAction physical shift spectralParameter hSpectral)
    (globalCandidateAAugmentedReducedShiftedOperator period hPeriod configuration
      data analysis chart sameAction physical shift spectralParameter)
  opNorm_le :
    ‖globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
      data analysis chart sameAction physical shift spectralParameter hSpectral‖ ≤
      (shift.coerciveShift.coercivityConstant - |spectralParameter|)⁻¹

/-- Construction of the Candidate-A real-resolvent certificate. -/
def globalCandidateAAugmentedReducedResolventCertificate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| <
      shift.coerciveShift.coercivityConstant) :
    GlobalCandidateAAugmentedReducedResolventCertificate4D period hPeriod
      configuration data analysis chart sameAction physical shift
        spectralParameter hSpectral := by
  have hGate := finite_defect_reduced_real_resolvent_gate
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift spectralParameter hSpectral
  exact
    { leftInverse := hGate.1
      rightInverse := hGate.2.1
      opNorm_le := hGate.2.2 }

/-- At zero spectral parameter the resolvent is the installed reduced Green
operator. -/
theorem globalCandidateAAugmentedReducedRealResolvent_zero
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
        data analysis chart sameAction physical shift 0
        (by simpa using shift.coerciveShift.coercivityConstant_pos) =
      globalCandidateAAugmentedReducedInverse period hPeriod configuration data
        analysis chart sameAction physical shift := by
  exact finiteDefectReducedRealResolvent_zero
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift
    (globalCandidateAAugmentedOrthogonalCoerciveShift_surjective period hPeriod
      configuration data analysis chart sameAction physical shift)
    (by simpa using shift.coerciveShift.coercivityConstant_pos)

/-- Public Candidate-A reduced-resolvent gate. -/
theorem global_candidateA_augmented_reduced_resolvent_gate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| <
      shift.coerciveShift.coercivityConstant) :
    GlobalCandidateAAugmentedReducedResolventCertificate4D period hPeriod
      configuration data analysis chart sameAction physical shift
        spectralParameter hSpectral :=
  globalCandidateAAugmentedReducedResolventCertificate period hPeriod
    configuration data analysis chart sameAction physical shift spectralParameter
      hSpectral

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D
end JanusFormal
