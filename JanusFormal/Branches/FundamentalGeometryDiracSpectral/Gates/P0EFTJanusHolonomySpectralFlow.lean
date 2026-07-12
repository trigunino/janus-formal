import Mathlib

namespace JanusFormal
namespace P0EFTJanusHolonomySpectralFlow

set_option autoImplicit false

/--
Spectral flow of the chiral zero-mode tower during an integral holonomy winding.
For a product family, it is the two-sphere Dirac index times the circle winding.
-/
def spectralFlow (diracIndex circleWinding : ℤ) : ℤ :=
  diracIndex * circleWinding

@[simp] theorem unit_winding_spectral_flow
    (diracIndex : ℤ) :
    spectralFlow diracIndex 1 = diracIndex := by
  simp [spectralFlow]

@[simp] theorem primitive_positive_flow :
    spectralFlow 1 1 = 1 := by
  norm_num [spectralFlow]

@[simp] theorem primitive_negative_flow :
    spectralFlow (-1) 1 = -1 := by
  norm_num [spectralFlow]

/-- PT reverses the spectral flow. -/
theorem pt_reverses_spectral_flow
    (diracIndex circleWinding : ℤ) :
    spectralFlow (-diracIndex) circleWinding =
      -spectralFlow diracIndex circleWinding := by
  unfold spectralFlow
  ring

/-- PT-paired spectral flows cancel. -/
theorem pt_paired_spectral_flows_cancel
    (diracIndex circleWinding : ℤ) :
    spectralFlow diracIndex circleWinding +
      spectralFlow (-diracIndex) circleWinding = 0 := by
  rw [pt_reverses_spectral_flow]
  ring

/-- The spectral-flow integer agrees with the doubled induced CS level shift. -/
def doubledLevelShiftFromFlow
    (diracIndex circleWinding : ℤ) : ℤ :=
  spectralFlow diracIndex circleWinding

/-- Primitive unit winding gives one doubled half-level shift. -/
@[simp] theorem primitive_flow_gives_unit_doubled_level :
    doubledLevelShiftFromFlow 1 1 = 1 := by
  rfl

/--
The analytic theorem behind this arithmetic is the APS/family-index statement
that spectral flow of the boundary Dirac family equals the index of the
corresponding even-dimensional operator.  It is a central bridge from Program D
geometry to the parity anomaly and determinant-line holonomy.
-/
structure SpectralFlowIndexClosureStatus where
  holonomyFamilyOfSelfAdjointDiracOperatorsConstructed : Prop
  endpointsRelatedByLargeGaugeTransformation : Prop
  crossingsIsolatedAndCounted : Prop
  spectralFlowWellDefined : Prop
  suspendedEvenDimensionalOperatorConstructed : Prop
  apsOrFamilyIndexTheoremApplied : Prop
  spectralFlowEqualsBulkIndex : Prop
  determinantLineHolonomyDerived : Prop
  csLevelShiftMatched : Prop


def spectralFlowIndexClosure
    (s : SpectralFlowIndexClosureStatus) : Prop :=
  s.holonomyFamilyOfSelfAdjointDiracOperatorsConstructed /\
  s.endpointsRelatedByLargeGaugeTransformation /\
  s.crossingsIsolatedAndCounted /\
  s.spectralFlowWellDefined /\
  s.suspendedEvenDimensionalOperatorConstructed /\
  s.apsOrFamilyIndexTheoremApplied /\
  s.spectralFlowEqualsBulkIndex /\
  s.determinantLineHolonomyDerived /\
  s.csLevelShiftMatched

end P0EFTJanusHolonomySpectralFlow
end JanusFormal
