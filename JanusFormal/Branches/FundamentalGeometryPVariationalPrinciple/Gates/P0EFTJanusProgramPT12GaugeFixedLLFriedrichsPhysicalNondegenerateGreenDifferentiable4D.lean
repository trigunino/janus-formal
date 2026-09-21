import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D

/-! Operator-norm differentiability of the nondegenerate physical Green family. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D

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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D
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

local instance physicalEndomorphismIsScalarTower
    {iota : Type*} [DecidableEq iota] :
    IsScalarTower Real
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis)
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis) where
  smul_assoc scalar first second := by
    ext state
    rfl

local instance physicalEndomorphismSMulCommClass
    {iota : Type*} [DecidableEq iota] :
    SMulCommClass Real
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis)
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis) where
  smul_comm scalar first second := by
    ext state
    change scalar • first (second state) = first (scalar • second state)
    exact (first.map_smul scalar (second state)).symm

/-- The stabilized reference inverse has the same derivative as the Green family. -/
theorem programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_hasDerivAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    HasDerivAt
      (fun value =>
        programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis value)
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter) parameter := by
  change HasDerivAt
    (fun value =>
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis value +
        programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
      period hPeriod analysis parameter) parameter
  exact
    (programPT12GaugeFixedLLFriedrichsD11Green_hasDerivAt
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter).add_const
      (programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis)

/-- Derivative of the physical identity-plus-compact factor. -/
def programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorDerivative
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (_d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod -
    programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis).comp
    (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
      period hPeriod analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_hasDerivAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    HasDerivAt
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) parameter := by
  let difference :=
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod -
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis
  have hStabilized :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_hasDerivAt
      (couplings := couplings) period hPeriod configuration analysis
        d9Ellipticity parameter
  have hComp : HasDerivAt
      (fun value => difference.comp
        (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            value))
      (difference.comp
        (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
          period hPeriod analysis parameter)) parameter := by
    simpa using (hasDerivAt_const parameter difference).clm_comp hStabilized
  change HasDerivAt
    (fun value =>
      ContinuousLinearMap.id Real
          (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis) +
        difference.comp
          (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              value))
    (difference.comp
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        period hPeriod analysis parameter)) parameter
  exact hComp.const_add _

/-- Banach-algebra derivative of the inverse bounded factor. -/
def programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (-ContinuousLinearMap.mulLeftRight Real
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter))
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorDerivative
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter)

theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative_eq
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter =
      -((programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter).comp
        ((programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorDerivative
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter).comp
          (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter))) := by
  ext state
  simp [programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative,
    ContinuousLinearMap.mulLeftRight_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply]

theorem programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_hasDerivAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical covector) :
    HasDerivAt
      (fun value =>
        programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity value)
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) parameter := by
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  have hUnit : IsUnit factor :=
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_bijective_iff_isUnit
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter).mp hParameter
  have hInverse := hasFDerivAt_ringInverse (𝕜 := Real) hUnit.unit
  have hChain := hInverse.comp_hasDerivAt parameter
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor_hasDerivAt
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter)
  simpa [Function.comp_def, factor,
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse,
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative,
    hUnit.unit_spec, ← Ring.inverse_unit hUnit.unit] using! hChain

/-- Operator-norm derivative of the physical Green family. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverseDerivative
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
      period hPeriod analysis parameter).comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter) +
  (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis
        parameter).comp
    (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter)

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse_hasDerivAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical covector) :
    HasDerivAt
      (fun value =>
        programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity value)
      (programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverseDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter) parameter := by
  simpa [programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse,
    programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverseDerivative] using
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_hasDerivAt
      (couplings := couplings) period hPeriod configuration analysis
        d9Ellipticity parameter).clm_comp
      (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_hasDerivAt
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter hParameter)

theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_comp_variation
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis).comp
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter) = 0 := by
  ext state
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D.CanonicalLLL2
      period hPeriod analysis)).injective
  apply Prod.ext <;>
    simp [programPT12GaugeFixedLLFriedrichsD11KernelProjection,
      programPT12GaugeFixedLLFriedrichsD11RangeProjection,
      programPT12GaugeFixedLLFriedrichsD11VariationOperator,
      withLpTwoProdMap_apply, ContinuousLinearMap.comp_apply]

theorem programPT12GaugeFixedLLFriedrichsD11Variation_comp_kernelProjection
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter).comp
      (programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis) = 0 := by
  ext state
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D.CanonicalLLL2
      period hPeriod analysis)).injective
  apply Prod.ext <;>
    simp [programPT12GaugeFixedLLFriedrichsD11KernelProjection,
      programPT12GaugeFixedLLFriedrichsD11RangeProjection,
      programPT12GaugeFixedLLFriedrichsD11VariationOperator,
      withLpTwoProdMap_apply, ContinuousLinearMap.comp_apply]

theorem programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverseDerivative_eq
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter =
      -((programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter).comp
        ((programPT12GaugeFixedLLFriedrichsD11VariationOperator
            (iota := iota) period hPeriod analysis parameter).comp
          (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              parameter))) := by
  rw [programPT12GaugeFixedLLFriedrichsD11GreenDerivative_eq_neg_comp
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter]
  let green := programPT12GaugeFixedLLFriedrichsD11GreenOperator
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let kernel := programPT12GaugeFixedLLFriedrichsD11KernelProjection
    period hPeriod covector couplings.matterMassSquared analysis
  let variation := programPT12GaugeFixedLLFriedrichsD11VariationOperator
    (iota := iota) period hPeriod analysis parameter
  have hKernelVariation : kernel.comp variation = 0 :=
    programPT12GaugeFixedLLFriedrichsD11KernelProjection_comp_variation
      (couplings := couplings) period hPeriod configuration analysis
        covector parameter
  have hVariationKernel : variation.comp kernel = 0 :=
    programPT12GaugeFixedLLFriedrichsD11Variation_comp_kernelProjection
      (couplings := couplings) period hPeriod configuration analysis
        covector parameter
  have hKernelVariationApply : ∀ state, kernel (variation state) = 0 := by
    intro state
    exact congrArg (fun operator => operator state) hKernelVariation
  have hVariationKernelApply : ∀ state, variation (kernel state) = 0 := by
    intro state
    exact congrArg (fun operator => operator state) hVariationKernel
  change -(green.comp (variation.comp green)) =
    -((green + kernel).comp (variation.comp (green + kernel)))
  ext state
  simp only [neg_apply, ContinuousLinearMap.comp_apply, add_apply, map_add]
  rw [hVariationKernelApply]
  simp only [add_zero, map_zero]
  rw [hKernelVariationApply]
  simp

/-- Exact inverse derivative identity for the nondegenerate physical Green. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverseDerivative_eq
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical covector) :
    programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverseDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter =
      -((programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter).comp
        ((programPT12GaugeFixedLLFriedrichsD11VariationOperator
            (iota := iota) period hPeriod analysis parameter).comp
          (programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter))) := by
  let stabilized :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let variation := programPT12GaugeFixedLLFriedrichsD11VariationOperator
    (iota := iota) period hPeriod analysis parameter
  let stabilizedDerivative :=
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative
      (iota := iota) period hPeriod analysis parameter
  let difference :=
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod -
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  let factorDerivative :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorDerivative
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let factorInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let factorInverseDerivative :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let physicalInverse :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalAmbientInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  have hStabilizedDerivative :
      stabilizedDerivative = -(stabilized * variation * stabilized) := by
    exact programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverseDerivative_eq
      (couplings := couplings) period hPeriod configuration analysis
        d9Ellipticity parameter
  have hFactor : factor = 1 + difference * stabilized := by
    rfl
  have hFactorDerivative : factorDerivative = difference * stabilizedDerivative := by
    rfl
  have hFactorInverseDerivative :
      factorInverseDerivative = -(factorInverse * factorDerivative * factorInverse) := by
    exact programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverseDerivative_eq
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  have hPhysicalInverse : physicalInverse = stabilized * factorInverse := by
    rfl
  have hCancel : factorInverse * factor = 1 := by
    exact programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_left
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter hParameter
  have hCorrection :
      factorInverse * difference * stabilized = 1 - factorInverse := by
    have hExpanded :
        factorInverse + factorInverse * difference * stabilized = 1 := by
      calc
        factorInverse + factorInverse * difference * stabilized =
            factorInverse * (1 + difference * stabilized) := by
          rw [mul_add, mul_one, mul_assoc]
        _ = factorInverse * factor := by rw [← hFactor]
        _ = 1 := hCancel
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hExpanded
  change stabilizedDerivative * factorInverse +
      stabilized * factorInverseDerivative =
    -(physicalInverse * variation * physicalInverse)
  rw [hFactorInverseDerivative, hFactorDerivative,
    hStabilizedDerivative, hPhysicalInverse]
  ext state
  have hCorrectionApply := congrArg (fun operator => operator
    (variation (stabilized (factorInverse state)))) hCorrection
  change factorInverse
      (difference (stabilized
        (variation (stabilized (factorInverse state))))) =
    variation (stabilized (factorInverse state)) -
      factorInverse (variation (stabilized (factorInverse state)))
        at hCorrectionApply
  simp only [mul_apply_eq_comp, add_apply, neg_apply, map_neg]
  rw [hCorrectionApply, map_sub]
  abel

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D
end JanusFormal
