import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexLinearity4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Complex linearity of the faithful low-energy SpinC coordinates

The zero Hopf coefficient and the complete signed first-sphere packet are now
assembled into seven faithful complex coordinates.  This gate proves that the
ambient synthesis respects the intrinsic global complex scalar action and that
the explicit low-energy Dirac diagonal is complex linear.

Thus the actual low-energy geometric range is stable under all constant
complex scalars, and the genuine differential Dirac operator commutes with
that action on the range.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexLinearity4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexLinearity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

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

/-- One Hopf zero-mode coefficient respects multiplication by any constant
complex scalar through the global SpinC scalar action. -/
theorem primitiveSpinCHopfZeroModeCoefficientLinearMap_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar coefficient : Complex) :
    primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, mode) (scalar * coefficient) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficient) := by
  apply ContMDiffSection.ext
  intro base
  rw [primitiveSpinCHopfZeroModeCoefficientLinearMap_eq_complexSection,
    primitiveSpinCHopfZeroModeCoefficientLinearMap_eq_complexSection,
    d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexAction_eq_re_add_im]
  unfold primitiveSpinCHopfZeroModeComplexSection
  change
    d9PrimitiveSpinCComplexActionCLM (scalar * coefficient)
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod .positiveQuarter).indexAt base) base) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCComplexActionCLM coefficient
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
            ((d9PrimitiveSpinCVectorBundleCore
              period hPeriod .positiveQuarter).indexAt base) base))
  exact d9PrimitiveSpinCComplexAction_mul scalar coefficient _

/-- The full seven-coordinate low-energy synthesis respects the intrinsic
global complex scalar action. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode (scalar • coefficients) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply]
  change
    primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) (scalar * coefficients.1) +
        primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode (scalar • coefficients.2) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficients.1 +
          primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2)
  rw [primitiveSpinCHopfZeroModeCoefficientLinearMap_complex_smul,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_complex_smul]
  exact
    (map_add
      (d9PrimitiveSpinCComplexScalarSectionLinearMap
        period hPeriod .positiveQuarter scalar)
      (primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, mode) coefficients.1)
      (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode coefficients.2)).symm

/-- The explicit seven-coordinate Dirac diagonal commutes with arbitrary
complex scalar multiplication. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
        period sector mode (scalar • coefficients) =
      scalar •
        primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients := by
  apply Prod.ext
  · change
      ((-normalRootLeviCivitaCorrectedFrequency
          period sector mode : Real) : Complex) *
          (scalar * coefficients.1) =
        scalar *
          (((-normalRootLeviCivitaCorrectedFrequency
            period sector mode : Real) : Complex) * coefficients.1)
    ring
  · exact
      primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_complex_smul
        period sector mode scalar coefficients.2

/-- The actual faithful low-energy geometric range is invariant under every
constant complex scalar action. -/
theorem primitiveSpinCHopfLowEnergyComplexSpan_complexScalar_mem
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (state : PrimitiveSpinCHopfLowEnergyComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar state.1 ∈
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode := by
  rcases (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
    period hPeriod sector mode).surjective state with ⟨coefficients, rfl⟩
  refine ⟨
    primitiveSpinCHopfLowEnergyComplexCoefficientBlockEquiv
      period hPeriod sector mode (scalar • coefficients), ?_⟩
  change
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode (scalar • coefficients) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients)
  exact
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_complex_smul
      period hPeriod sector mode scalar coefficients)

/-- On the actual low-energy geometric range, the genuine differential Dirac
operator commutes with every constant complex scalar action. -/
theorem primitiveSpinCHopfLowEnergyComplexSpan_dirac_complexScalar
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (state : PrimitiveSpinCHopfLowEnergyComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state.1) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state.1) :=
  d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    period hPeriod scalar state.1

/-- Consolidated complex-linearity theorem for the faithful seven-coordinate
low-energy block. -/
theorem primitiveSpinCHopfLowEnergyComplexLinearity_closed
    (sector : NormalRootChoice) (mode : Int) :
    (∀ (scalar : Complex)
        (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients),
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode (scalar • coefficients) =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode coefficients)) ∧
      (∀ (scalar : Complex)
          (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients),
        primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode (scalar • coefficients) =
          scalar •
            primitiveSpinCHopfLowEnergyComplexCoefficientOperator
              period sector mode coefficients) ∧
      (∀ (scalar : Complex)
          (state : PrimitiveSpinCHopfLowEnergyComplexSpan
            period hPeriod sector mode),
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state.1 ∈
          PrimitiveSpinCHopfLowEnergyComplexSpan
            period hPeriod sector mode) :=
  ⟨primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_complex_smul
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator_complex_smul
      period sector mode,
    primitiveSpinCHopfLowEnergyComplexSpan_complexScalar_mem
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexLinearity4D
end JanusFormal
