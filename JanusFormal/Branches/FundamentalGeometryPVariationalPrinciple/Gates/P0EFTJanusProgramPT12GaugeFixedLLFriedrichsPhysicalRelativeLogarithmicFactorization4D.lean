import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D

/-!
# T12 relative physical logarithmic factorization

On the physical nondegenerate locus, the difference between the physical and
reference logarithmic derivatives is an exact two-sided stabilized-inverse
sandwich.  This is only an operator identity; no nuclearity is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicFactorization4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
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

/-- The bounded middle factor in the relative logarithmic sandwich. -/
def programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter).comp
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod -
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis)

/-- Difference between the physical and reference D11 logarithmic
derivatives. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalRelativeLogarithmicDerivative
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter -
    programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis
        parameter

/-- Positive stabilized-inverse sandwich underlying the relative logarithmic
derivative. -/
def programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicSandwich
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
    ((programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter).comp
      ((programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter).comp
        (programPT12GaugeFixedLLFriedrichsD11VariationOperator
          (iota := iota) period hPeriod analysis parameter)))

/-- Exact relative logarithmic derivative as a stabilized-inverse sandwich. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmic_factorization
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (hParameter : parameter ∈
      programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    programPT12GaugeFixedLLFriedrichsFullPhysicalRelativeLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter =
      -programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicSandwich
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter := by
  let stabilized :=
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let factor := programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactor
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity parameter
  let factorInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  let correction :=
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod -
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector couplings.matterMassSquared analysis
  let variation := programPT12GaugeFixedLLFriedrichsD11VariationOperator
    (iota := iota) period hPeriod analysis parameter
  let referenceGreen := programPT12GaugeFixedLLFriedrichsD11GreenOperator
    period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  let kernelProjection :=
    programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis
  have hFactorApply : ∀ state, factor state =
      state + correction (stabilized state) := by
    intro state
    rfl
  have hInverse :=
    programPT12GaugeFixedLLFriedrichsPhysicalBoundedFactorInverse_left
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter hParameter
  have hKernelVariation :=
    programPT12GaugeFixedLLFriedrichsD11KernelProjection_comp_variation
      (couplings := couplings) period hPeriod configuration analysis covector
        parameter
  ext state
  have hCancel :
      factorInverse (variation state) +
          factorInverse (correction (stabilized (variation state))) =
        variation state := by
    have hApply := congrArg
      (fun operator => operator (variation state)) hInverse
    rw [ContinuousLinearMap.comp_apply, hFactorApply,
      map_add] at hApply
    simpa [factorInverse, factor] using hApply
  have hRelative :
      factorInverse (variation state) - variation state =
        -factorInverse (correction (stabilized (variation state))) := by
    calc
      factorInverse (variation state) - variation state =
          factorInverse (variation state) -
            (factorInverse (variation state) +
              factorInverse (correction (stabilized (variation state)))) := by
                rw [hCancel]
      _ = -factorInverse (correction (stabilized (variation state))) := by
        abel
  have hKernelApply : kernelProjection (variation state) = 0 := by
    have hApply := congrArg (fun operator => operator state) hKernelVariation
    simpa [kernelProjection, variation] using hApply
  have hStabilizedVariation :
      stabilized (variation state) = referenceGreen (variation state) := by
    simp [stabilized,
      programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse,
      referenceGreen, kernelProjection, hKernelApply]
  change
    stabilized (factorInverse (variation state)) -
        referenceGreen (variation state) =
      -(stabilized
        (factorInverse (correction (stabilized (variation state)))))
  calc
    stabilized (factorInverse (variation state)) -
          referenceGreen (variation state) =
        stabilized (factorInverse (variation state)) -
          stabilized (variation state) := by rw [hStabilizedVariation]
    _ = stabilized
        (factorInverse (variation state) - variation state) := by
          rw [map_sub]
    _ = stabilized
        (-factorInverse (correction (stabilized (variation state)))) := by
          rw [hRelative]
    _ = -(stabilized
        (factorInverse (correction (stabilized (variation state))))) := by
          rw [map_neg]

end Physical

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicFactorization4D
end JanusFormal
