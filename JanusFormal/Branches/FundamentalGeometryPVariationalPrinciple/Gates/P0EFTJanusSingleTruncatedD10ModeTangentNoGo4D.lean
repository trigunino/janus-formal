import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationD9FieldAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentFieldVariationLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonLLActionVariation4D

/-!
# Typed no-go for a single truncated D10 mode tangent

The lowest positive truncated D10 label is completely explicit.  The current
Program-P field package, however, contains no geometric eigensection map from
that spectral label.  This gate exhibits the obstruction at that single mode:
the zero tangent and a concrete nonzero constant LL tangent are distinct true
`ProgramPCompleteVariation4D` values, while the current D9 projection sees
them identically.  Thus the spectral label and existing D9 data do not select
a unique mode tangent without additional physical realization data.

No claim is made that the displayed LL tangent is a D10 eigensection.
-/

namespace JanusFormal
namespace P0EFTJanusSingleTruncatedD10ModeTangentNoGo4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusCompleteVariationD9FieldAssembly4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Lowest sphere level, first positive circle frequency and positive-quarter
root, including the first genuine sphere-degeneracy label. -/
def lowestPositiveTruncatedD10Mode
    (data : ProductThroatSpectralData) : TruncatedD10Mode data 1 1 :=
  ⟨⟨0, by omega⟩,
    (⟨0, sphere_multiplicity_positive data 0⟩,
      ((⟨0, by omega⟩, false), .positiveQuarter))⟩

/-- The calculable separated spectral label represented by that truncation. -/
def lowestPositiveProductDiracMode : ProductDiracMode where
  sphereLevel := 0
  circleMode := 1
  rootChoice := .positiveQuarter

@[simp]
theorem lowestPositiveTruncatedD10Mode_label
    (data : ProductThroatSpectralData) :
    truncatedD10Mode (lowestPositiveTruncatedD10Mode data) =
      lowestPositiveProductDiracMode :=
  rfl

/-- The corresponding multiplicity-aware Program-P D10 label. -/
def lowestPositiveProgramPD10Mode
    (data : ProductThroatSpectralData) : ProgramPD10Mode4D data :=
  truncatedProgramPD10Mode4D (lowestPositiveTruncatedD10Mode data)

@[simp]
theorem lowestPositiveProgramPD10Mode_separatedMode
    (data : ProductThroatSpectralData) :
    (lowestPositiveProgramPD10Mode data).separatedMode =
      lowestPositiveProductDiracMode :=
  rfl

/-- A concrete nonzero constant LL direction already belonging to the true
independent-field tangent type. -/
def unitLLDirection : SmoothThroatField period hPeriod LLFieldFiber :=
  constantSmoothThroatField period hPeriod LLFieldFiber
    (EuclideanSpace.single 0 1)

/-- Canonical zero complete tangent. -/
def zeroCompleteVariation : ProgramPCompleteVariation4D period hPeriod :=
  independentCompleteVariation period hPeriod 0

/-- A genuine complete tangent carrying only the constant LL direction. -/
def unitLLCompleteVariation : ProgramPCompleteVariation4D period hPeriod :=
  independentCompleteVariation period hPeriod
    (llFluxIndependentVariation period hPeriod
      (unitLLDirection period hPeriod))

@[simp]
theorem unitLLCompleteVariation_llField_at
    (point : EffectiveThroat period hPeriod) :
    (unitLLCompleteVariation period hPeriod).independent.llField point 0 = 1 := by
  simp [unitLLCompleteVariation, unitLLDirection,
    llFluxIndependentVariation, constantSmoothThroatField]

/-- The present D9 projection is blind to the LL-only distinction. -/
theorem unitLLCompleteVariation_D9_eq_zero
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    completeVariationD9Field period hPeriod (Equiv.refl MatterFiber)
        (unitLLCompleteVariation period hPeriod) sector column point =
      completeVariationD9Field period hPeriod (Equiv.refl MatterFiber)
        (zeroCompleteVariation period hPeriod) sector column point :=
  rfl

/-- Candidate tangents over a fixed D10 label.  The label itself supplies no
map into geometric Program-P fields. -/
abbrev D10ModeTangentFiber
    {data : ProductThroatSpectralData}
    (_mode : ProgramPD10Mode4D data) :=
  ProgramPCompleteVariation4D period hPeriod

/-- Even over the single explicit lowest label, the current concrete field
and D9 data do not determine a unique tangent. -/
theorem lowestPositiveD10Mode_tangentFiber_not_subsingleton
    (data : ProductThroatSpectralData)
    (point : EffectiveThroat period hPeriod) :
    ¬ Subsingleton
      (D10ModeTangentFiber period hPeriod
        (lowestPositiveProgramPD10Mode data)) := by
  intro hSubsingleton
  have hEqual := hSubsingleton.allEq
    (zeroCompleteVariation period hPeriod)
    (unitLLCompleteVariation period hPeriod)
  have hValue := congrArg
    (fun variation : ProgramPCompleteVariation4D period hPeriod =>
      variation.independent.llField point 0) hEqual
  change (0 : Real) = 1 at hValue
  norm_num at hValue

end

end P0EFTJanusSingleTruncatedD10ModeTangentNoGo4D
end JanusFormal
