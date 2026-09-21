import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D

/-!
The nondegenerate physical Friedrichs fibres have an explicit bounded
Green operator.  Its difference from the stabilized reference inverse is
compact, and its logarithmic derivative candidate is compact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 10000
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

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

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- The inverse of the bounded identity-plus-compact factor.  Away from the
unit locus `Ring.inverse` is zero; all inverse statements below explicitly
assume physical nondegeneracy. -/
def programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  Ring.inverse
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter)

theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_left
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).comp
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) =
      ContinuousLinearMap.id Real _ := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  have hUnit : IsUnit factor :=
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).mp hParameter
  change Ring.inverse factor * factor = 1
  exact Ring.inverse_mul_cancel factor hUnit

theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_right
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).comp
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) =
      ContinuousLinearMap.id Real _ := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  have hUnit : IsUnit factor :=
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).mp hParameter
  change factor * Ring.inverse factor = 1
  exact Ring.mul_inverse_cancel factor hUnit

/-- Domain-valued inverse of a nondegenerate physical fibre. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →ₗ[Real]
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector couplings.matterMassSquared analysis
          parameter).domain :=
  (programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis
      parameter).comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).toLinearMap

/-- Ambient Green operator of a physical fibre. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis
      parameter).comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter)

@[simp]
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse_coe
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (source : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    ((programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter source :
      (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
        couplings.matterMassSquared analysis parameter).domain) :
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) =
      programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter source := by
  exact programPT12GaugeFixedLLFriedrichsD11StabilizedInverse_coe
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter source)

/-- The domain-valued physical inverse is a genuine two-sided inverse on every
nondegenerate fibre. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse_twoSided
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    Function.LeftInverse
        (programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter)
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun ∧
      Function.RightInverse
        (programPT12GaugeFixedLLFriedrichsFullPhysicalDomainInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter)
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  let factorInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let stabilized := programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
    period hPeriod covector couplings.matterMassSquared analysis parameter
  let stabilizedInverse :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  have hFactorLeft : ∀ state, factorInverse (factor state) = state := by
    intro state
    have hMap := congrArg (fun operator => operator state)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_left
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter hParameter)
    exact hMap
  have hFactorRight : ∀ state, factor (factorInverse state) = state := by
    intro state
    have hMap := congrArg (fun operator => operator state)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_right
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter hParameter)
    exact hMap
  have hStabilized :=
    programPT12GaugeFixedLLFriedrichsD11Stabilization_twoSidedInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  constructor
  · intro state
    change stabilizedInverse (factorInverse
      ((programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter).toFun state)) = state
    rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_factorization_apply
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter]
    change stabilizedInverse (factorInverse (factor (stabilized.toFun state))) =
      state
    rw [hFactorLeft]
    exact hStabilized.1 state
  · intro source
    change (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).toFun
      (stabilizedInverse (factorInverse source)) = source
    rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_factorization_apply
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter]
    change factor (stabilized.toFun
      (stabilizedInverse (factorInverse source))) = source
    rw [hStabilized.2 (factorInverse source), hFactorRight]

/-- The stabilized reference inverse is norm-continuous. -/
theorem programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_continuous
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    Continuous (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter) := by
  change Continuous
    ((fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter) +
     (fun _ : Real =>
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis))
  exact
    (programPT12GaugeFixedLLFriedrichsD11Green_differentiable
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis).continuous.add
      continuous_const

/-- The bounded factor inverse varies continuously at every nondegenerate
parameter. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_continuousAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    ContinuousAt (fun value =>
      programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity value) parameter := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  have hUnit : IsUnit factor :=
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).mp hParameter
  have hInverse : ContinuousAt Ring.inverse factor := by
    simpa only [hUnit.unit_spec] using
      (NormedRing.inverse_continuousAt hUnit.unit)
  exact hInverse.comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_continuous
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity).continuousAt

/-- The physical Green operator varies continuously at every nondegenerate
parameter. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse_continuousAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    ContinuousAt (fun value =>
      programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity value) parameter :=
  (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_continuous
    period hPeriod configuration analysis d9Ellipticity).continuousAt.clm_comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_continuousAt
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter hParameter)

/-- The bounded factor differs compactly from the identity. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_sub_id_compact
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter -
        ContinuousLinearMap.id Real
          (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) := by
  have hCompact :=
    ((programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod).sub
      (programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis)).comp_clm
      (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter)
  have hIdentity :
      programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter -
        ContinuousLinearMap.id Real
          (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis) =
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              (iota := iota) period hPeriod -
        programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis).comp
        (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter) := by
    ext state
    simp [programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor,
      linearPMap_compactPerturbation_boundedFactor]
  rw [hIdentity]
  exact hCompact

/-- On the nondegenerate locus, the bounded factor inverse also differs
compactly from the identity. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_sub_id_compact
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter -
        ContinuousLinearMap.id Real
          (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  let factorInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let identity := ContinuousLinearMap.id Real
    (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis)
  have hCompact : IsCompactOperator (factor - identity) :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_sub_id_compact
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  have hCancel : ∀ state, factorInverse (factor state) = state := by
    intro state
    have hMap := congrArg (fun operator => operator state)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_left
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter hParameter)
    exact hMap
  have hIdentity :
      factorInverse - identity = -(factorInverse.comp (factor - identity)) := by
    ext state
    change factorInverse state - state =
      -(factorInverse (factor state - state))
    rw [map_sub, hCancel]
    abel
  rw [hIdentity]
  exact (hCompact.clm_comp factorInverse).neg

/-- The physical Green operator is a compact correction of the stabilized
reference inverse. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse_sub_stabilized_compact
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter -
        programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter) := by
  let stabilizedInverse :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let factorInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let identity := ContinuousLinearMap.id Real
    (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis)
  have hCompact : IsCompactOperator (factorInverse - identity) :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_sub_id_compact
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter hParameter
  have hIdentity :
      programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter - stabilizedInverse =
        stabilizedInverse.comp (factorInverse - identity) := by
    ext state
    change stabilizedInverse (factorInverse state) - stabilizedInverse state =
      stabilizedInverse (factorInverse state - state)
    rw [map_sub]
  rw [hIdentity]
  exact hCompact.clm_comp stabilizedInverse

/-- Bismut--Freed logarithmic derivative candidate of the physical Green
family. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter).comp
    (programPT12GaugeFixedLLFriedrichsD11VariationOperator
      (iota := iota) period hPeriod analysis parameter)

/-- The physical logarithmic derivative candidate is compact on every
nondegenerate fibre. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative_compact
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) := by
  let variation := programPT12GaugeFixedLLFriedrichsD11VariationOperator
    (iota := iota) period hPeriod analysis parameter
  let green := programPT12GaugeFixedLLFriedrichsD11GreenOperator
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let kernelProjection :=
    programPT12GaugeFixedLLFriedrichsD11KernelProjection period hPeriod covector
      couplings.matterMassSquared analysis
  let stabilizedInverse :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let physicalInverse :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  have hGreenVariation : IsCompactOperator (green.comp variation) := by
    exact programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative_compact
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  have hKernelVariation :
      IsCompactOperator (kernelProjection.comp variation) :=
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis).comp_clm
      variation
  have hStabilizedVariation :
      IsCompactOperator (stabilizedInverse.comp variation) := by
    have hSum := hGreenVariation.add hKernelVariation
    have hIdentity :
        stabilizedInverse.comp variation =
          green.comp variation + kernelProjection.comp variation := by
      ext state
      simp [stabilizedInverse,
        programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse,
        green, kernelProjection]
    rw [hIdentity]
    exact hSum
  have hRelative : IsCompactOperator (physicalInverse - stabilizedInverse) :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse_sub_stabilized_compact
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter hParameter
  have hRelativeVariation :
      IsCompactOperator ((physicalInverse - stabilizedInverse).comp variation) :=
    hRelative.comp_clm variation
  have hIdentity :
      physicalInverse.comp variation =
        stabilizedInverse.comp variation +
          (physicalInverse - stabilizedInverse).comp variation := by
    ext state
    simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
    abel
  change IsCompactOperator (physicalInverse.comp variation)
  rw [hIdentity]
  exact hStabilizedVariation.add hRelativeVariation

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D
end JanusFormal
