import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D

/-!
# Split coordinates for a Fredholm determinant family

A self-adjoint Fredholm determinant has two logically distinct pieces:

* the finite-dimensional top exterior line of the actual kernel;
* the nonzero regularized determinant of the invertible complement.

This file keeps those pieces explicit in a split coordinate packet.  It does
not identify their cartesian product with the final complex tensor-product
determinant line.  That complexification/tensor comparison remains a separate
geometric construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSplitFredholmDeterminantFamily4D

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 1300000

noncomputable section

open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Finite kernel family together with the regularized determinant coordinate
of the reduced invertible family. -/
structure SplitFredholmDeterminantFamilyData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode] where
  kernels : FiniteKernelBasisFamilyData operator ZeroMode
  reducedDeterminant : Real → Complex
  reducedDeterminant_ne_zero : ∀ parameter,
    reducedDeterminant parameter ≠ 0

/-- Split determinant section at one parameter. -/
structure SplitFredholmDeterminantSection
    {operator : Real → E →L[Real] E}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode]
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) where
  kernelVolume : FiniteKernelDeterminantFiber data.kernels parameter
  reducedCoordinate : Complex

namespace SplitFredholmDeterminantFamilyData

/-- Canonical split section: named kernel volume plus reduced determinant. -/
def canonicalSection
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    SplitFredholmDeterminantSection data parameter where
  kernelVolume := finiteKernelNamedVolume data.kernels parameter
  reducedCoordinate := data.reducedDeterminant parameter

/-- Neither component of the canonical split section vanishes. -/
theorem canonicalSection_nonzero_components
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    (data.canonicalSection parameter).kernelVolume ≠ 0 ∧
      (data.canonicalSection parameter).reducedCoordinate ≠ 0 :=
  ⟨finiteKernelNamedVolume_ne_zero data.kernels parameter,
    data.reducedDeterminant_ne_zero parameter⟩

/-- Transport only the finite kernel-line component between parameters. -/
def transportKernelComponent
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real)
    (splitSection : SplitFredholmDeterminantSection data first) :
    FiniteKernelDeterminantFiber data.kernels second :=
  finiteKernelDeterminantTransport data.kernels first second
    splitSection.kernelVolume

/-- Kernel transport sends the canonical split section's volume to the next
canonical volume. -/
theorem transportKernelComponent_canonicalSection
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.transportKernelComponent first second (data.canonicalSection first) =
      (data.canonicalSection second).kernelVolume :=
  finiteKernelDeterminantTransport_namedVolume data.kernels first second

/-- The kernel component transports transitively. -/
theorem transportKernelComponent_trans
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real)
    (volume : FiniteKernelDeterminantFiber data.kernels first) :
    finiteKernelDeterminantTransport data.kernels second third
        (finiteKernelDeterminantTransport data.kernels first second volume) =
      finiteKernelDeterminantTransport data.kernels first third volume := by
  have hMaps := finiteKernelDeterminantTransport_trans data.kernels
    first second third
  exact LinearMap.congr_fun hMaps volume

/-- Public split Fredholm-determinant checkpoint. -/
theorem split_fredholm_determinant_family_gate
    (operator : Real → E →L[Real] E)
    (data : SplitFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter,
      Module.finrank Real
        (FiniteKernelDeterminantFiber data.kernels parameter) = 1) ∧
      (∀ parameter,
        (data.canonicalSection parameter).kernelVolume ≠ 0 ∧
          (data.canonicalSection parameter).reducedCoordinate ≠ 0) ∧
      (∀ first second,
        data.transportKernelComponent first second
            (data.canonicalSection first) =
          (data.canonicalSection second).kernelVolume) :=
  ⟨finiteKernelDeterminantFiber_finrank_one data.kernels,
    data.canonicalSection_nonzero_components,
    data.transportKernelComponent_canonicalSection⟩

end SplitFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSplitFredholmDeterminantFamily4D
end JanusFormal
