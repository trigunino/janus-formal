namespace JanusFormal
namespace P0EFTCMBTTShapeDiagnostic

set_option autoImplicit false

structure TTShapeDiagnostic where
  stockCAMBRun : Prop
  forkCAMBRun : Prop
  bandRatiosComputed : Prop
  peakShiftsComputed : Prop

def ttShapeDiagnosticReady (d : TTShapeDiagnostic) : Prop :=
  d.stockCAMBRun /\
  d.forkCAMBRun /\
  d.bandRatiosComputed /\
  d.peakShiftsComputed

theorem tt_shape_diagnostic_ready_from_components
    (d : TTShapeDiagnostic)
    (hStock : d.stockCAMBRun)
    (hFork : d.forkCAMBRun)
    (hBands : d.bandRatiosComputed)
    (hPeaks : d.peakShiftsComputed) :
    ttShapeDiagnosticReady d := by
  exact And.intro hStock (And.intro hFork (And.intro hBands hPeaks))

end P0EFTCMBTTShapeDiagnostic
end JanusFormal
