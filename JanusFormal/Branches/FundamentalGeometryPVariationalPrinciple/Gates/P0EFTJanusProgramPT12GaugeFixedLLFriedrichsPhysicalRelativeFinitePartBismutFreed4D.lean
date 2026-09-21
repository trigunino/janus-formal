import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeBismutFreedBridge4D

/-!
# Physical relative Bismut--Freed bridge from finite-part data

The physical relative coefficient comparison follows from the real
finite-part logarithmic derivative and reality of the regularized zeta
derivative.  The existing relative Bismut--Freed bridge then supplies the
determinant and metric conclusions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartBismutFreed4D

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
open P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeBismutFreedBridge4D
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

/-- Real finite-part data sufficient to recover the complex physical relative
Bismut--Freed coefficient on the nondegenerate locus. -/
structure PhysicalRelativeFinitePartBismutFreedInput4D
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  relativeNuclear : PhysicalRelativeLogarithmicNuclearInput4D
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity
  zetaFamily : RelativeHeatMellinZetaFamilyData
  finitePartLogDerivative_eq_trace : ∀ parameter :
      PhysicalRelativeNondegenerateParameter period hPeriod configuration data
        analysis chart sameAction physical covector,
    zetaFamily.finitePartFamily.logDerivative parameter.1 =
      relativeNuclear.trace period hPeriod configuration data analysis chart
        sameAction physical parameter
  zetaPrimeAtZero_real : ∀ parameter : Real,
    (zetaFamily.zetaPrimeAtZero parameter).im = 0

namespace PhysicalRelativeFinitePartBismutFreedInput4D

/-- Generic real finite-part coefficient data for the same zeta family. -/
def toReferenceZetaTraceCoefficientData
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartBismutFreedInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    ReferenceZetaTraceCoefficientData input.zetaFamily where
  logarithmicTrace := input.zetaFamily.finitePartFamily.logDerivative
  finitePartLogDerivative_eq_trace := fun _ => rfl
  zetaPrimeAtZero_real := input.zetaPrimeAtZero_real

/-- The finite-part trace identity and zeta reality force the full complex
physical relative coefficient agreement. -/
theorem coefficient_agreement
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartBismutFreedInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    relativeZetaConnectionCoefficient input.zetaFamily.toZetaFamily
        parameter.1 =
      input.relativeNuclear.bismutFreedCoefficient period hPeriod configuration
        data analysis chart sameAction physical parameter := by
  rw [input.toReferenceZetaTraceCoefficientData.connectionCoefficient_eq_neg_trace]
  simp only [toReferenceZetaTraceCoefficientData,
    PhysicalRelativeLogarithmicNuclearInput4D.bismutFreedCoefficient]
  rw [input.finitePartLogDerivative_eq_trace parameter]
  simp

/-- Construct the existing physical relative Bismut--Freed bridge without an
independent complex coefficient hypothesis. -/
def toPhysicalRelativeBismutFreedBridgeData
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartBismutFreedInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    PhysicalRelativeBismutFreedBridgeData period hPeriod configuration data
      analysis chart sameAction physical d9Ellipticity where
  relativeNuclear := input.relativeNuclear
  zetaFamily := input.zetaFamily
  coefficient_agreement := input.coefficient_agreement period hPeriod
    configuration data analysis chart sameAction physical

/-- Public finite-part-to-relative-Bismut--Freed construction checkpoint. -/
theorem finitePartBismutFreedInput_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalRelativeFinitePartBismutFreedInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    Nonempty
      (PhysicalRelativeBismutFreedBridgeData period hPeriod configuration data
        analysis chart sameAction physical d9Ellipticity) :=
  ⟨input.toPhysicalRelativeBismutFreedBridgeData period hPeriod configuration
    data analysis chart sameAction physical⟩

end PhysicalRelativeFinitePartBismutFreedInput4D
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeFinitePartBismutFreed4D
end JanusFormal
