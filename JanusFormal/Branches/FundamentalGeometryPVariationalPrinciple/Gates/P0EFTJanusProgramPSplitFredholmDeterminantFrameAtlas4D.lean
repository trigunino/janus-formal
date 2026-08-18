import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSplitFredholmDeterminantFamily4D

/-!
# Frame atlas for a split Fredholm determinant family

The finite kernel determinant fibre already has a canonical named volume, while
the invertible complement carries a nonzero complex regularized determinant.
To describe their product in local complex coordinates, one may choose a
nonzero complex coordinate for the complexification of the named kernel
volume.

This file records exactly that local-coordinate construction.  The full local
coordinate in frame `i` is

`k_i(a) * det_red(a)`.

Frame changes are the ratios `k_j / k_i`.  They are nonzero, satisfy the Cech
cocycle and glue the local full determinant coordinates.  No claim is made that
the cartesian split packet is already the abstract tensor-product determinant
line; this is the coordinate atlas that such a comparison must preserve.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSplitFredholmDeterminantFrameAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1500000

noncomputable section

open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D
open P0EFTJanusProgramPSplitFredholmDeterminantFamily4D

variable {E Index : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- A split Fredholm determinant together with nonzero local coordinates for
the complexified named kernel volume. -/
structure SplitFredholmDeterminantFrameAtlasData
    (operator : Real → E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode]
    (Index : Type*) where
  split : SplitFredholmDeterminantFamilyData operator ZeroMode
  kernelFrameCoordinate : Index → Real → Complex
  kernelFrameCoordinate_ne_zero : ∀ index parameter,
    kernelFrameCoordinate index parameter ≠ 0

namespace SplitFredholmDeterminantFrameAtlasData

/-- Full Fredholm determinant coordinate in one local complexified kernel
frame. -/
def localDeterminant
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (index : Index) (parameter : Real) : Complex :=
  data.kernelFrameCoordinate index parameter *
    data.split.reducedDeterminant parameter

/-- Change of local complexified kernel frame. -/
def transition
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (first second : Index) (parameter : Real) : Complex :=
  data.kernelFrameCoordinate second parameter /
    data.kernelFrameCoordinate first parameter

/-- Every full local determinant coordinate is nonzero. -/
theorem localDeterminant_ne_zero
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (index : Index) (parameter : Real) :
    data.localDeterminant index parameter ≠ 0 :=
  mul_ne_zero
    (data.kernelFrameCoordinate_ne_zero index parameter)
    (data.split.reducedDeterminant_ne_zero parameter)

/-- Every frame transition is nonzero. -/
theorem transition_ne_zero
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (first second : Index) (parameter : Real) :
    data.transition first second parameter ≠ 0 :=
  div_ne_zero
    (data.kernelFrameCoordinate_ne_zero second parameter)
    (data.kernelFrameCoordinate_ne_zero first parameter)

/-- Identity transition. -/
@[simp]
theorem transition_self
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (index : Index) (parameter : Real) :
    data.transition index index parameter = 1 := by
  exact div_self (data.kernelFrameCoordinate_ne_zero index parameter)

/-- Reverse frame changes are inverse. -/
theorem transition_inverse
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (first second : Index) (parameter : Real) :
    data.transition first second parameter *
        data.transition second first parameter = 1 := by
  unfold transition
  field_simp [data.kernelFrameCoordinate_ne_zero first parameter,
    data.kernelFrameCoordinate_ne_zero second parameter]

/-- Exact Cech cocycle law for the full determinant coordinates. -/
theorem transition_cocycle
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (first second third : Index) (parameter : Real) :
    data.transition second third parameter *
        data.transition first second parameter =
      data.transition first third parameter := by
  unfold transition
  field_simp [data.kernelFrameCoordinate_ne_zero first parameter,
    data.kernelFrameCoordinate_ne_zero second parameter,
    data.kernelFrameCoordinate_ne_zero third parameter]

/-- Local full determinant coordinates glue through the generated frame
transition. -/
theorem localDeterminant_gluing
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (first second : Index) (parameter : Real) :
    data.transition first second parameter *
        data.localDeterminant first parameter =
      data.localDeterminant second parameter := by
  unfold transition localDeterminant
  field_simp [data.kernelFrameCoordinate_ne_zero first parameter]

/-- The finite kernel-line component of the split section remains the genuine
named top exterior volume independently of the chosen complex coordinate
frame. -/
theorem canonical_kernelVolume_ne_zero
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index)
    (parameter : Real) :
    (data.split.canonicalSection parameter).kernelVolume ≠ 0 :=
  data.split.canonicalSection_nonzero_components parameter |>.1

/-- Complete local-coordinate atlas certificate. -/
structure SplitFredholmDeterminantFrameAtlasCertificate
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index) : Prop where
  local_nonzero : ∀ index parameter,
    data.localDeterminant index parameter ≠ 0
  transition_nonzero : ∀ first second parameter,
    data.transition first second parameter ≠ 0
  transition_self : ∀ index parameter,
    data.transition index index parameter = 1
  transition_cocycle : ∀ first second third parameter,
    data.transition second third parameter *
        data.transition first second parameter =
      data.transition first third parameter
  local_gluing : ∀ first second parameter,
    data.transition first second parameter *
        data.localDeterminant first parameter =
      data.localDeterminant second parameter
  kernel_volume_nonzero : ∀ parameter,
    (data.split.canonicalSection parameter).kernelVolume ≠ 0

/-- Build the frame-atlas certificate from the nonzero frame coordinates. -/
def certificate
    {operator : Real → E →L[Real] E}
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index) :
    SplitFredholmDeterminantFrameAtlasCertificate data where
  local_nonzero := data.localDeterminant_ne_zero
  transition_nonzero := data.transition_ne_zero
  transition_self := data.transition_self
  transition_cocycle := data.transition_cocycle
  local_gluing := data.localDeterminant_gluing
  kernel_volume_nonzero := data.canonical_kernelVolume_ne_zero

/-- Public split Fredholm determinant frame-atlas checkpoint. -/
theorem split_fredholm_determinant_frame_atlas_gate
    (operator : Real → E →L[Real] E)
    (data : SplitFredholmDeterminantFrameAtlasData operator ZeroMode Index) :
    SplitFredholmDeterminantFrameAtlasCertificate data :=
  data.certificate

end SplitFredholmDeterminantFrameAtlasData

end
end P0EFTJanusProgramPSplitFredholmDeterminantFrameAtlas4D
end JanusFormal
