import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexActualDiracCoefficientAutomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexFinrank4D

/-!
# Consolidated faithful low-energy complex SpinC closure

At every fixed normal-root sector and circle label, the geometric Hopf zero
mode together with the complete signed first sphere is now an exact
seven-complex-coordinate block.  Its ambient synthesis is faithful, its
actual smooth-section range has real dimension fourteen, the genuine
geometric Dirac restriction is bijective with zero kernel, and its inverse is
the synthesis of the explicit coefficient inverse.

The same range is invariant under the global complex scalar action.  This is
a finite low-energy geometric closure theorem; it does not assert arbitrary
sphere levels or Hilbert-space completeness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexClosure4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexActualDiracCoefficientAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexFinrank4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexLinearity4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Complete finite geometric closure certificate for one rooted circle
label. -/
theorem primitiveSpinCHopfLowEnergyComplexGeometricClosure
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode) ∧
      Module.finrank Real
          (PrimitiveSpinCHopfLowEnergyComplexSpan
            period hPeriod sector mode) = 14 ∧
      Function.Bijective
          (primitiveSpinCHopfLowEnergyComplexActualDirac
            period hPeriod sector mode) ∧
      LinearMap.ker
          (primitiveSpinCHopfLowEnergyComplexActualDirac
            period hPeriod sector mode) = ⊥ ∧
      (∀ (scalar : Complex)
          (state : PrimitiveSpinCHopfLowEnergyComplexSpan
            period hPeriod sector mode),
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state.1 ∈
          PrimitiveSpinCHopfLowEnergyComplexSpan
            period hPeriod sector mode) ∧
      (∀ state : PrimitiveSpinCHopfLowEnergyComplexSpan
          period hPeriod sector mode,
        primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
            period hPeriod sector mode
            (primitiveSpinCHopfLowEnergyComplexActualDirac
              period hPeriod sector mode state) = state) ∧
      (∀ state : PrimitiveSpinCHopfLowEnergyComplexSpan
          period hPeriod sector mode,
        primitiveSpinCHopfLowEnergyComplexActualDirac
            period hPeriod sector mode
            (primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
              period hPeriod sector mode state) = state) :=
  ⟨primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_injective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexSpan_finrank
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_bijective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_ker_eq_bot
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexSpan_complexScalar_mem
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_left
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_right
      period hPeriod sector mode⟩

/-- The exact coefficient equivalence, the explicit coefficient automorphism
and the actual differential Dirac restriction fit into one conjugate finite
model. -/
theorem primitiveSpinCHopfLowEnergyComplexConjugateModel
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode).toLinearMap.comp
        ((primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode).comp
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
            period hPeriod sector mode).symm.toLinearMap) ∧
      Function.Bijective
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode) :=
  ⟨primitiveSpinCHopfLowEnergyComplexActualDirac_coefficient_conjugate
      period hPeriod sector mode,
    P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D.primitiveSpinCHopfLowEnergyComplexCoefficientOperator_bijective
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexClosure4D
end JanusFormal
