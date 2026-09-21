import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartBismutFreed4D

/-!
# Physical relative finite-part variation and canonical Schwarz reduction

A direct derivative theorem for the physical relative finite part identifies
its named derivative by uniqueness.  Canonical Mellin Schwarz reflection makes
the regularized zeta derivative real.  These two derived facts construct the
existing physical relative finite-part Bismut--Freed input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartVariationSchwarz4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
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
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartBismutFreed4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicNuclear4D

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

/-- Analytically natural inputs replacing the named finite-part derivative
identity and the scalar zeta-reality field. -/
structure PhysicalRelativeFinitePartVariationSchwarzInput4D
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  relativeNuclear : PhysicalRelativeLogarithmicNuclearInput4D
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity
  zetaFamily : RelativeHeatMellinZetaFamilyData
  finitePartTrace_hasDerivAt : ∀ parameter :
      PhysicalRelativeNondegenerateParameter period hPeriod configuration data
        analysis chart sameAction physical covector,
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          (zetaFamily.finitePartFamily.finitePart current))
      (relativeNuclear.trace period hPeriod configuration data analysis chart
        sameAction physical parameter)
      parameter.1
  canonicalSchwarz : ∀ parameter : Real,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (zetaFamily.continuation parameter)

namespace PhysicalRelativeFinitePartVariationSchwarzInput4D

/-- Uniqueness of the derivative identifies the named finite-part derivative
with the intrinsic physical relative trace. -/
theorem finitePartLogDerivative_eq_trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartVariationSchwarzInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    input.zetaFamily.finitePartFamily.logDerivative parameter.1 =
      input.relativeNuclear.trace period hPeriod configuration data analysis
        chart sameAction physical parameter :=
  (input.zetaFamily.finitePartFamily.hasDerivAt_logDeterminant parameter.1).unique
    (input.finitePartTrace_hasDerivAt parameter)

/-- Canonical Schwarz reflection forces reality of every regularized zeta
derivative in the family. -/
theorem zetaPrimeAtZero_real
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartVariationSchwarzInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : Real) :
    (input.zetaFamily.zetaPrimeAtZero parameter).im = 0 := by
  simpa [RelativeHeatMellinZetaFamilyData.zetaPrimeAtZero] using
    (input.canonicalSchwarz parameter).derivativeAtZero_im_eq_zero

/-- Construct the finite-part physical relative Bismut--Freed input from the
direct variation and canonical Schwarz packets. -/
def toFinitePartBismutFreedInput
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartVariationSchwarzInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    PhysicalRelativeFinitePartBismutFreedInput4D period hPeriod configuration
      data analysis chart sameAction physical d9Ellipticity where
  relativeNuclear := input.relativeNuclear
  zetaFamily := input.zetaFamily
  finitePartLogDerivative_eq_trace :=
    input.finitePartLogDerivative_eq_trace period hPeriod configuration data
      analysis chart sameAction physical
  zetaPrimeAtZero_real := input.zetaPrimeAtZero_real period hPeriod
    configuration data analysis chart sameAction physical

/-- Public direct-variation and canonical-Schwarz reduction checkpoint. -/
theorem finitePartVariationSchwarzInput_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartVariationSchwarzInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    Nonempty
      (PhysicalRelativeFinitePartBismutFreedInput4D period hPeriod
        configuration data analysis chart sameAction physical d9Ellipticity) :=
  ⟨input.toFinitePartBismutFreedInput period hPeriod configuration data
    analysis chart sameAction physical⟩

end PhysicalRelativeFinitePartVariationSchwarzInput4D
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartVariationSchwarz4D
end JanusFormal
