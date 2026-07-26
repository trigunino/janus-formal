import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite dimension of the faithful low-energy SpinC block

The geometric zero-plus-first-level block has one complex Hopf coefficient and
six complex signed first-sphere coefficients.  The exact synthesis equivalence
therefore identifies its actual smooth-section range with a fourteen-
real-dimensional vector space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexFinrank4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The faithful coefficient space contains seven complex, hence fourteen real,
coordinates. -/
theorem primitiveSpinCLowEnergyGeometricComplexCoefficients_finrank :
    Module.finrank Real PrimitiveSpinCLowEnergyGeometricComplexCoefficients =
      14 := by
  simp [PrimitiveSpinCLowEnergyGeometricComplexCoefficients,
    PrimitiveSpinCFirstSphereSignedComplexCoefficients,
    PrimitiveSpinCFirstSphereComplexCoefficients,
    Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex]

/-- The actual geometric low-energy smooth-section range has real dimension
exactly fourteen. -/
theorem primitiveSpinCHopfLowEnergyComplexSpan_finrank
    (sector : NormalRootChoice) (mode : Int) :
    Module.finrank Real
        (PrimitiveSpinCHopfLowEnergyComplexSpan
          period hPeriod sector mode) = 14 := by
  calc
    Module.finrank Real
        (PrimitiveSpinCHopfLowEnergyComplexSpan
          period hPeriod sector mode) =
      Module.finrank Real
        PrimitiveSpinCLowEnergyGeometricComplexCoefficients :=
      (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
        period hPeriod sector mode).finrank_eq.symm
    _ = 14 :=
      primitiveSpinCLowEnergyGeometricComplexCoefficients_finrank

/-- Consolidated exact finite-dimensionality certificate for the geometric
low-energy block. -/
theorem primitiveSpinCHopfLowEnergyComplexFinrank_closed
    (sector : NormalRootChoice) (mode : Int) :
    Module.finrank Real PrimitiveSpinCLowEnergyGeometricComplexCoefficients =
        14 ∧
      Module.finrank Real
        (PrimitiveSpinCHopfLowEnergyComplexSpan
          period hPeriod sector mode) = 14 :=
  ⟨primitiveSpinCLowEnergyGeometricComplexCoefficients_finrank,
    primitiveSpinCHopfLowEnergyComplexSpan_finrank
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexFinrank4D
end JanusFormal
