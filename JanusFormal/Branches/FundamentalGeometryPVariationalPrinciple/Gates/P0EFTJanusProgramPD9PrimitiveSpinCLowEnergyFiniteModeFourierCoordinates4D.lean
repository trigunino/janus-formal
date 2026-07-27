import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

/-!
# Fourier separation of finite low-energy complex coefficient packets

For a fixed normal-root sector, every one of the seven complex coordinates
carries the same quarter-twisted circle exponential at a given mode.  This
gate builds the componentwise finite Fourier analysis of a low-energy
coefficient packet and proves exact recovery of every mode and every complex
coordinate by the standard period integral.

This is the coefficient-side Fourier theorem needed by the geometric finite
mode synthesis.  The subsequent gate identifies these seven analysis
functions with actual local geometric observables of the synthesized section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeFourierCoordinates4D

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate Interval
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real)

/-- Projection to the Hopf zero-mode complex coordinate. -/
def primitiveSpinCLowEnergyZeroCoordinate :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex where
  toFun coefficients := coefficients.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to one positive first-sphere complex coordinate. -/
def primitiveSpinCLowEnergyPositiveCoordinate
    (coordinate : Fin 3) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex where
  toFun coefficients := coefficients.2.1 coordinate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to one negative first-sphere complex coordinate. -/
def primitiveSpinCLowEnergyNegativeCoordinate
    (coordinate : Fin 3) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex where
  toFun coefficients := coefficients.2.2 coordinate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Apply one complex coordinate projection mode-by-mode to a finite packet. -/
def primitiveSpinCLowEnergyFiniteModeCoordinateRestriction
    (coordinate :
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  Finsupp.mapRange.linearMap coordinate

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeCoordinateRestriction_apply
    (coordinate :
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (mode : Int) :
    primitiveSpinCLowEnergyFiniteModeCoordinateRestriction coordinate
        coefficients mode =
      coordinate (coefficients mode) :=
  rfl

/-- Ordinary finite Fourier analysis of one selected low-energy coordinate. -/
def primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
    (sector : NormalRootChoice)
    (coordinate :
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex)
    (time : Real) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real] Complex :=
  (normalRootSpinFrameFinsuppPacketLinearMap
      period sector time).comp
    (primitiveSpinCLowEnergyFiniteModeCoordinateRestriction coordinate)

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_apply
    (sector : NormalRootChoice)
    (coordinate :
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex)
    (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients) :
    primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
        period sector coordinate time coefficients =
      normalRootSpinFrameFinsuppPacketLinearMap
        period sector time
        (primitiveSpinCLowEnergyFiniteModeCoordinateRestriction
          coordinate coefficients) :=
  rfl

/-- The Fourier period pairing recovers the selected coordinate of any mode. -/
theorem primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (coordinate :
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real] Complex)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (mode : Int) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameExponential
                period sector mode time) *
            primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
              period sector coordinate time coefficients) =
      coordinate (coefficients mode) := by
  simpa only [
    primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_apply,
    primitiveSpinCLowEnergyFiniteModeCoordinateRestriction_apply] using
    normalRootSpinFrameFinsuppPacket_coefficient
      period hPeriod sector
      (primitiveSpinCLowEnergyFiniteModeCoordinateRestriction
        coordinate coefficients) mode

/-- The seven componentwise Fourier packets, assembled in the original
low-energy coefficient fiber. -/
def primitiveSpinCLowEnergyFiniteModeFourierAnalysis
    (sector : NormalRootChoice) (time : Real) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients where
  toFun coefficients :=
    (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
        period sector primitiveSpinCLowEnergyZeroCoordinate
        time coefficients,
      (fun coordinate =>
        primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
          period sector
          (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
          time coefficients,
       fun coordinate =>
        primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
          period sector
          (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
          time coefficients))
  map_add' first second := by
    apply Prod.ext
    · exact map_add
        (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
          period sector primitiveSpinCLowEnergyZeroCoordinate time)
        first second
    · apply Prod.ext <;> funext coordinate
      · exact map_add
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector
            (primitiveSpinCLowEnergyPositiveCoordinate coordinate) time)
          first second
      · exact map_add
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector
            (primitiveSpinCLowEnergyNegativeCoordinate coordinate) time)
          first second
  map_smul' scalar coefficients := by
    apply Prod.ext
    · exact map_smul
        (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
          period sector primitiveSpinCLowEnergyZeroCoordinate time)
        scalar coefficients
    · apply Prod.ext <;> funext coordinate
      · exact map_smul
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector
            (primitiveSpinCLowEnergyPositiveCoordinate coordinate) time)
          scalar coefficients
      · exact map_smul
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector
            (primitiveSpinCLowEnergyNegativeCoordinate coordinate) time)
          scalar coefficients

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeFourierAnalysis_zero_apply
    (sector : NormalRootChoice) (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients) :
    (primitiveSpinCLowEnergyFiniteModeFourierAnalysis
        period sector time coefficients).1 =
      primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
        period sector primitiveSpinCLowEnergyZeroCoordinate
        time coefficients :=
  rfl

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeFourierAnalysis_positive_apply
    (sector : NormalRootChoice) (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (coordinate : Fin 3) :
    (primitiveSpinCLowEnergyFiniteModeFourierAnalysis
        period sector time coefficients).2.1 coordinate =
      primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
        period sector (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
        time coefficients :=
  rfl

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeFourierAnalysis_negative_apply
    (sector : NormalRootChoice) (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (coordinate : Fin 3) :
    (primitiveSpinCLowEnergyFiniteModeFourierAnalysis
        period sector time coefficients).2.2 coordinate =
      primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
        period sector (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
        time coefficients :=
  rfl

/-- Equality of all seven time-dependent Fourier analysis functions forces
equality of the original finite coefficient packets. -/
theorem primitiveSpinCLowEnergyFiniteModeFourierAnalysis_separates
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (first second : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (hAnalysis : ∀ time : Real,
      primitiveSpinCLowEnergyFiniteModeFourierAnalysis
          period sector time first =
        primitiveSpinCLowEnergyFiniteModeFourierAnalysis
          period sector time second) :
    first = second := by
  apply Finsupp.ext
  intro mode
  apply Prod.ext
  · have hTime : ∀ time : Real,
        primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector primitiveSpinCLowEnergyZeroCoordinate time first =
          primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
            period sector primitiveSpinCLowEnergyZeroCoordinate time second := by
      intro time
      exact congrArg Prod.fst (hAnalysis time)
    calc
      (first mode).1 =
          (period : Complex)⁻¹ *
            (∫ time in (0 : Real)..period,
              conj
                  (normalRootSpinFrameExponential
                    period sector mode time) *
                primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                  period sector primitiveSpinCLowEnergyZeroCoordinate
                  time first) :=
        (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
          period hPeriod sector primitiveSpinCLowEnergyZeroCoordinate
          first mode).symm
      _ =
          (period : Complex)⁻¹ *
            (∫ time in (0 : Real)..period,
              conj
                  (normalRootSpinFrameExponential
                    period sector mode time) *
                primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                  period sector primitiveSpinCLowEnergyZeroCoordinate
                  time second) := by
        simp_rw [hTime]
      _ = (second mode).1 :=
        primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
          period hPeriod sector primitiveSpinCLowEnergyZeroCoordinate
          second mode
  · apply Prod.ext <;> funext coordinate
    · have hTime : ∀ time : Real,
          primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
              period sector
              (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
              time first =
            primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
              period sector
              (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
              time second := by
        intro time
        exact congrFun (congrArg (fun value => value.2.1) (hAnalysis time)) coordinate
      calc
        (first mode).2.1 coordinate =
            (period : Complex)⁻¹ *
              (∫ time in (0 : Real)..period,
                conj
                    (normalRootSpinFrameExponential
                      period sector mode time) *
                  primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                    period sector
                    (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
                    time first) :=
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
            period hPeriod sector
            (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
            first mode).symm
        _ =
            (period : Complex)⁻¹ *
              (∫ time in (0 : Real)..period,
                conj
                    (normalRootSpinFrameExponential
                      period sector mode time) *
                  primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                    period sector
                    (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
                    time second) := by
          simp_rw [hTime]
        _ = (second mode).2.1 coordinate :=
          primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
            period hPeriod sector
            (primitiveSpinCLowEnergyPositiveCoordinate coordinate)
            second mode
    · have hTime : ∀ time : Real,
          primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
              period sector
              (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
              time first =
            primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
              period sector
              (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
              time second := by
        intro time
        exact congrFun (congrArg (fun value => value.2.2) (hAnalysis time)) coordinate
      calc
        (first mode).2.2 coordinate =
            (period : Complex)⁻¹ *
              (∫ time in (0 : Real)..period,
                conj
                    (normalRootSpinFrameExponential
                      period sector mode time) *
                  primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                    period sector
                    (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
                    time first) :=
          (primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
            period hPeriod sector
            (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
            first mode).symm
        _ =
            (period : Complex)⁻¹ *
              (∫ time in (0 : Real)..period,
                conj
                    (normalRootSpinFrameExponential
                      period sector mode time) *
                  primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis
                    period sector
                    (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
                    time second) := by
          simp_rw [hTime]
        _ = (second mode).2.2 coordinate :=
          primitiveSpinCLowEnergyFiniteModeCoordinateFourierAnalysis_coefficient
            period hPeriod sector
            (primitiveSpinCLowEnergyNegativeCoordinate coordinate)
            second mode

/-- In particular, the componentwise finite Fourier analysis has trivial
kernel. -/
theorem primitiveSpinCLowEnergyFiniteModeFourierAnalysis_zero_kernel
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (hAnalysis : ∀ time : Real,
      primitiveSpinCLowEnergyFiniteModeFourierAnalysis
          period sector time coefficients = 0) :
    coefficients = 0 := by
  apply primitiveSpinCLowEnergyFiniteModeFourierAnalysis_separates
    period hPeriod sector coefficients 0
  intro time
  simpa using hAnalysis time

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeFourierCoordinates4D
end JanusFormal
