import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamily4D

/-!
The invertible physical Friedrichs fibres form an open parameter locus, and
invertibility therefore persists locally around every nondegenerate fibre.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D

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

/-- The bounded identity-plus-compact factor controlling one physical fibre. -/
def programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  linearPMap_compactPerturbation_boundedFactor
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis
        parameter)

/-- The controlling bounded factor varies continuously in operator norm. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_continuous
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    Continuous
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity) := by
  have hGreen : Continuous (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter) :=
    (programPT12GaugeFixedLLFriedrichsD11Green_differentiable
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis).continuous
  have hInverse : Continuous (fun parameter =>
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
    exact hGreen.add continuous_const
  have hComp : Continuous (fun parameter =>
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              (iota := iota) period hPeriod -
        programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis).comp
        (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter)) :=
    (continuous_const : Continuous (fun _ : Real =>
      programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              (iota := iota) period hPeriod -
        programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis)).clm_comp
      hInverse
  change Continuous
    ((fun _ : Real =>
        ContinuousLinearMap.id Real
          (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) +
      (fun parameter =>
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
            (configuration := configuration) (data := data)
              (analysis := analysis) (chart := chart)
                (sameAction := sameAction) (physical := physical)
                  (iota := iota) period hPeriod -
          programPT12GaugeFixedLLFriedrichsD11KernelProjection
            period hPeriod covector couplings.matterMassSquared analysis).comp
          (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              parameter)))
  exact continuous_const.add hComp

/-- A physical fibre is bijective exactly when its bounded factor is. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_factor
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    Function.Bijective
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun ↔
      Function.Bijective
        (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter) := by
  let reference := programPT12GaugeFixedLLFriedrichsD11Operator
    period hPeriod covector couplings.matterMassSquared analysis parameter
  let stabilized := programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
    period hPeriod covector couplings.matterMassSquared analysis parameter
  let full := programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := chart) (sameAction := sameAction) (physical := physical)
        period hPeriod covector parameter
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  have hStabilized : Function.Bijective stabilized.toFun := by
    have hInverse :=
      programPT12GaugeFixedLLFriedrichsD11Stabilization_twoSidedInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter
    exact ⟨hInverse.1.injective, hInverse.2.surjective⟩
  have hFactorization : ∀ state : reference.domain,
      full.toFun state = factor (stabilized.toFun state) := by
    intro state
    exact programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_factorization_apply
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter state
  change Function.Bijective
      (fun state : reference.domain => full.toFun state) ↔
    Function.Bijective factor
  have hFunctionEq :
      (fun state : reference.domain => full.toFun state) =
        (factor : _ → _) ∘ (fun state : reference.domain => stabilized.toFun state) := by
    funext state
    exact hFactorization state
  rw [hFunctionEq]
  exact Function.Bijective.of_comp_iff (factor : _ → _) hStabilized

/-- Equivalently, physical nondegeneracy is invertibility in the Banach
algebra of bounded endomorphisms. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    Function.Bijective
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun ↔
      IsUnit
        (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_factor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter

/-- Parameters at which the full physical fibre is nondegenerate. -/
def programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) : Set Real :=
  {parameter | Function.Bijective
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).toFun}

/-- The physical nondegenerate locus is open. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet_isOpen
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    IsOpen (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
      period hPeriod configuration data analysis chart sameAction physical
        covector) := by
  have hSet :
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
          period hPeriod configuration data analysis chart sameAction physical
            covector =
        {parameter | IsUnit
          (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter)} := by
    ext parameter
    exact programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  rw [hSet]
  exact Units.isOpen.preimage
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_continuous
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)

/-- No zero mode can appear sufficiently near a nondegenerate physical fibre. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_eventually_bijective
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : Function.Bijective
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter).toFun) :
    ∀ᶠ nearby in nhds parameter, Function.Bijective
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector nearby).toFun := by
  have hMem : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector := hParameter
  show programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
      period hPeriod configuration data analysis chart sameAction physical
        covector ∈ nhds parameter
  exact (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet_isOpen
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity).mem_nhds hMem

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
end JanusFormal
