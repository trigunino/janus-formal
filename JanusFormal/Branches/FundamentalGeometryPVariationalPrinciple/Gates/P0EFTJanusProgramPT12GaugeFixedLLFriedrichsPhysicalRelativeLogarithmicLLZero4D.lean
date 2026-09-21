import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11DiagonalNuclearInput4D

/-! Vanishing of the physical relative logarithmic LL column. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicLLZero4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsAmbientHilbertBasis4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11DiagonalNuclearInput4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicFactorization4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The D11 defect projection has no LL component. -/
@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_on_ll_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (mode : LLMode) :
    programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis
        (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          (iota := iota) period hPeriod analysis llSpectral (.inr mode)) = 0 := by
  rw [programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis_ll,
    programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply,
    programPT12GaugeFixedLLFriedrichsD11RangeProjection,
    withLpTwoProdMap_apply]
  simp

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

/-- If the physical perturbation kills one LL basis vector, so does the
relative logarithmic middle factor. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle_on_ll_basis_of_physical_zero
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (mode : LLMode)
    (hPhysical :
      programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod
          (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
            (iota := iota) period hPeriod analysis llSpectral (.inr mode)) = 0) :
    programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter
        (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          (iota := iota) period hPeriod analysis llSpectral (.inr mode)) = 0 := by
  rw [programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle,
    ContinuousLinearMap.comp_apply, sub_apply,
    hPhysical,
    programPT12GaugeFixedLLFriedrichsD11KernelProjection_on_ll_basis]
  simp

/-- Pointwise vanishing of the physical LL column supplies the exact weighted
nuclear input with no additional summability hypothesis. -/
def physicalRelativeLogarithmicLLDiagonalInputOfPhysicalZero
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (hPhysical : ∀ mode : LLMode,
      programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod
          (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
            (iota := iota) period hPeriod analysis llSpectral (.inr mode)) = 0) :
    PhysicalRelativeLogarithmicLLDiagonalInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity LLMode :=
  PhysicalRelativeLogarithmicLLDiagonalInput4D.ofLLImageSquareSummable
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity llSpectral (by
        intro parameter
        apply (summable_zero : Summable (fun _ : LLMode => (0 : Real))).congr
        intro mode
        rw [programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle_on_ll_basis_of_physical_zero
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter.1 llSpectral mode (hPhysical mode)]
        simp)

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicLLZero4D
end JanusFormal
