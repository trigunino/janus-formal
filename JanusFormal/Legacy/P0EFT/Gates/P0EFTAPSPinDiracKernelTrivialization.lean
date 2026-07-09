import JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinDiracSpectrumPairing

namespace JanusFormal
namespace P0EFTAPSPinDiracKernelTrivialization

set_option autoImplicit false

structure APSPinDiracKernelTrivialization where
  lichnerowiczWeitzenbockFormulaLoaded : Prop
  connectionLaplacianNonnegative : Prop
  boundaryScalarCurvaturePositive : Prop
  noBoundaryHarmonicSpinors : Prop

def lichnerowiczPositiveGap (k : APSPinDiracKernelTrivialization) : Prop :=
  k.lichnerowiczWeitzenbockFormulaLoaded /\
  k.connectionLaplacianNonnegative /\
  k.boundaryScalarCurvaturePositive

def kernelTrivializedByDSCurvature (k : APSPinDiracKernelTrivialization) : Prop :=
  lichnerowiczPositiveGap k /\ k.noBoundaryHarmonicSpinors

theorem positive_lichnerowicz_gap_trivializes_kernel
    (k : APSPinDiracKernelTrivialization)
    (hFormula : k.lichnerowiczWeitzenbockFormulaLoaded)
    (hLap : k.connectionLaplacianNonnegative)
    (hCurv : k.boundaryScalarCurvaturePositive)
    (hNoHarmonic : k.noBoundaryHarmonicSpinors) :
    kernelTrivializedByDSCurvature k := by
  exact And.intro
    (And.intro hFormula (And.intro hLap hCurv))
    hNoHarmonic

theorem kernel_trivialization_supplies_zero_mode_control
    (k : APSPinDiracKernelTrivialization)
    (s : P0EFTAPSPinDiracSpectrumPairing.APSPinDiracSpectrumPairing)
    (_hKernel : kernelTrivializedByDSCurvature k)
    (hSelf : s.boundaryOperatorSelfAdjoint)
    (hJ : s.pinMinusPairingOperatorExists)
    (hAnti : s.pairingOperatorAntiCommutesWithAAPS)
    (hPairs : s.nonzeroSpectrumPairedBySign)
    (hZero : s.zeroModesVanishOrCancel) :
    P0EFTAPSPinDiracSpectrumPairing.etaRegularizationFixedByPairing s := by
  apply P0EFTAPSPinDiracSpectrumPairing.spectral_pairing_fixes_eta_zero_mode_cancellation
  · exact P0EFTAPSPinDiracSpectrumPairing.anticommuting_pin_operator_pairs_nonzero_spectrum
      s hSelf hJ hAnti hPairs
  · exact hZero

theorem missing_positive_curvature_blocks_kernel_trivialization
    (k : APSPinDiracKernelTrivialization)
    (hMissing : Not k.boundaryScalarCurvaturePositive) :
    Not (kernelTrivializedByDSCurvature k) := by
  intro h
  exact hMissing h.left.right.right

end P0EFTAPSPinDiracKernelTrivialization
end JanusFormal
