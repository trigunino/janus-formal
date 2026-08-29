import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D

/-!
# Local coordinates of the global primitive SpinC complex action

The global imaginary endomorphism and the intrinsic complex scalar action are
constructed without choosing a trivialization.  In every installed primitive
SpinC chart they nevertheless reduce to the expected fiber formulas.

This is the missing bridge needed to analyze complex first-sphere packets by
pointwise geometric witnesses: local evaluation commutes with `J`, and an
arbitrary complex coefficient becomes the real/imaginary fiber combination
of the evaluated section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexLocalCoordinate4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Local coordinates commute exactly with the globally descended imaginary
endomorphism. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_imaginary
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCImaginarySection
          period hPeriod .positiveQuarter state) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state) := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod .positiveQuarter state
  let imaginaryFamily :=
    d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod .positiveQuarter family
  have hRecover :
      family.toSmoothSection period hPeriod .positiveQuarter = state :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
      period hPeriod .positiveQuarter state
  have hStateLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state =
        family.localValue index base := by
    rw [← hRecover,
      primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod index base hBase]
    exact primitiveSpinCBundleSection_localTriv
      period hPeriod .positiveQuarter family index base hBase
  calc
    primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base
          (d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter state) =
        imaginaryFamily.localValue index base := by
      rw [show
          d9PrimitiveSpinCImaginarySection
              period hPeriod .positiveQuarter state =
            imaginaryFamily.toSmoothSection
              period hPeriod .positiveQuarter by rfl,
        primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
          period hPeriod index base hBase]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter imaginaryFamily index base hBase
    _ =
        d9PrimitiveSpinCImaginaryAction
          (family.localValue index base) :=
      rfl
    _ =
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index base state) := by
      rw [hStateLocal]

/-- Local coordinates of the intrinsic global complex scalar action. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_complexScalar
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (scalar : Complex)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state) =
      scalar.re •
          primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index base state +
        scalar.im •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod index base state) := by
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (scalar.re • state +
          scalar.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod .positiveQuarter state) = _
  rw [map_add, map_smul, map_smul,
    primitiveSpinCGeometricSectionLocalCoordinate_imaginary
      period hPeriod index base hBase state]

/-- Local coordinates of one complex eigenspinor coefficient. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_complexLine
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (coefficient : Complex) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter state coefficient) =
      coefficient.re •
          primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index base state +
        coefficient.im •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod index base state) := by
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (coefficient.re • state +
          coefficient.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod .positiveQuarter state) = _
  rw [map_add, map_smul, map_smul,
    primitiveSpinCGeometricSectionLocalCoordinate_imaginary
      period hPeriod index base hBase state]

/-- The local-coordinate map itself intertwines the global imaginary
endomorphism with its fiber counterpart. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_intertwines_imaginary
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base).comp
        (d9PrimitiveSpinCImaginarySectionLinearMap
          period hPeriod .positiveQuarter) =
      d9PrimitiveSpinCImaginaryAction.toLinearMap.comp
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base) := by
  apply LinearMap.ext
  intro state
  exact primitiveSpinCGeometricSectionLocalCoordinate_imaginary
    period hPeriod index base hBase state

/-- Consolidated local complex-coordinate bridge. -/
theorem primitiveSpinCGlobalComplexLocalCoordinate_closed
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (∀ state,
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base
          (d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter state) =
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index base state)) ∧
      (∀ scalar state,
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod index base
            (d9PrimitiveSpinCComplexScalarSection
              period hPeriod .positiveQuarter scalar state) =
          scalar.re •
              primitiveSpinCGeometricSectionLocalCoordinate
                period hPeriod index base state +
            scalar.im •
              d9PrimitiveSpinCImaginaryAction
                (primitiveSpinCGeometricSectionLocalCoordinate
                  period hPeriod index base state)) :=
  ⟨primitiveSpinCGeometricSectionLocalCoordinate_imaginary
      period hPeriod index base hBase,
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar
      period hPeriod index base hBase⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexLocalCoordinate4D
end JanusFormal
