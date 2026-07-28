import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCThroatFourierMonopoleDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCMonopoleFiniteFrame4D

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleSpectralBridge4D

open AddCircle
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCMonopoleFiniteFrame4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCThroatFourierMonopoleDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D
open P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

set_option autoImplicit false
noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

theorem d9ThroatPositiveTimeCircle_movingWitness
    (point : MonopoleSphere) (time : Real) :
    d9ThroatPositiveTimeCircle period hPeriod
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((time * (period⁻¹ * |period|) : Real) : AddCircle |period|) := by
  rw [d9ThroatPositiveTimeCircle, Function.comp_apply]
  rw [show
    d9ThroatTimeCircle period hPeriod
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      (time : AddCircle period) by rfl]
  exact AddCircle.homeomorphAddCircle_apply_mk
    period |period| hPeriod (abs_ne_zero.mpr hPeriod) time

theorem fourier_mul_normalRootSpinFrameExponential
    (point : MonopoleSphere) (fourierMode circleMode : Int) (time : Real)
    (sector : NormalRootChoice) :
    fourier fourierMode
          (d9ThroatPositiveTimeCircle period hPeriod
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) *
        normalRootSpinFrameExponential
          period sector circleMode time =
      normalRootSpinFrameExponential
        period sector (circleMode + fourierMode) time := by
  rw [show
    d9ThroatPositiveTimeCircle period hPeriod
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((time * (period⁻¹ * |period|) : Real) : AddCircle |period|) by
        rw [d9ThroatPositiveTimeCircle, Function.comp_apply]
        rw [show
          d9ThroatTimeCircle period hPeriod
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time) =
            (time : AddCircle period) by rfl]
        exact AddCircle.homeomorphAddCircle_apply_mk
          period |period| hPeriod (abs_ne_zero.mpr hPeriod) time]
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  have hIndex :
      normalRootSpinFrameModeIndex sector
          (circleMode + fourierMode) =
        normalRootSpinFrameModeIndex sector circleMode +
          2 * fourierMode := by
    cases sector <;>
      simp [normalRootSpinFrameModeIndex] <;>
      ring
  rw [fourier_coe_apply]
  unfold normalRootSpinFrameExponential normalRootSpinFrameFrequency
  rw [hIndex]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [hPeriod, abs_ne_zero.mpr hPeriod]
  ring

theorem localHopfFrameSeed_zero_time_mode_independent
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (firstMode secondMode : Int) :
    localHopfFrameSeed
        period hPeriod point chart sector firstMode 0 =
      localHopfFrameSeed
        period hPeriod point chart sector secondMode 0 := by
  unfold localHopfFrameSeed
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  cases sector
  · rw [
      primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
        period hPeriod point chart hChart firstMode 0,
      primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
        period hPeriod point chart hChart secondMode 0]
    simp [normalRootSpinFramePhase,
      normalRootSpinFramePhaseAngle]
  · rw [
      primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
        period hPeriod point chart hChart firstMode 0,
      primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
        period hPeriod point chart hChart secondMode 0]
    simp [normalRootSpinFramePhase,
      normalRootSpinFramePhaseAngle]

theorem d9ThroatFourierMonopoleMode_movingWitness
    (label : FourierMonopoleLabel)
    (point : MonopoleSphere) (time : Real) :
    d9ThroatFourierMonopoleMode period hPeriod label
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      solidHarmonicPacketSphereRestriction label.1 point *
        fourier label.2
          (d9ThroatPositiveTimeCircle period hPeriod
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) := by
  change
    solidHarmonicPacketSphereRestriction label.1
          (d9ThroatMonopoleSphereProjection period hPeriod
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) *
        fourier label.2
          (d9ThroatPositiveTimeCircle period hPeriod
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) =
      _
  rw [primitiveSpinCNullPacketMovingWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere]

theorem solidHarmonicPacketSphereRestriction_apply
    (label : SolidHarmonicPacketLabel)
    (point : MonopoleSphere) :
    solidHarmonicPacketSphereRestriction label point =
      primitiveSpinCNullSphereScalar
          (primitiveSpinCSolidPacketParameter label.1 label.2) point ^
        label.1 := by
  have hRestriction
      (polynomial : PrimitiveSpinCSolidPolynomial) :
      primitiveSpinCSpherePolynomialRestriction polynomial point =
        MvPolynomial.eval
          (fun coordinate : Fin 3 =>
            (monopoleSphereCoordinate point coordinate : Complex))
          polynomial := by
    induction polynomial using MvPolynomial.induction_on' with
    | add left right hLeft hRight =>
        simp only [map_add, ContinuousMap.add_apply, hLeft, hRight]
    | monomial exponent coefficient =>
        simp [primitiveSpinCSpherePolynomialRestriction,
          MvPolynomial.aeval_def,
          primitiveSpinCSphereCoordinateContinuousMap,
          MvPolynomial.eval_monomial]
  rw [solidHarmonicPacketSphereRestriction, hRestriction]
  exact primitiveSpinCSolidHarmonicPacket_eval_sphere
    label.1 label.2 point

theorem d9ThroatFourierMonopoleMode_mul_seed_eq_nullPower
    (degree : Nat) (multiplicity : Fin (2 * degree + 1))
    (fourierMode circleMode : Int)
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (time : Real) :
    d9PrimitiveSpinCComplexActionCLM
        (d9ThroatFourierMonopoleMode period hPeriod
          ((⟨degree, multiplicity⟩ :
              SolidHarmonicPacketLabel), fourierMode)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time))
        (localHopfFrameSeed
          period hPeriod point chart sector circleMode time) =
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullPowerSection
          period hPeriod
          (primitiveSpinCSolidPacketParameter degree multiplicity)
          sector (circleMode + fourierMode) degree) := by
  rw [d9ThroatFourierMonopoleMode_movingWitness]
  rw [solidHarmonicPacketSphereRestriction_apply]
  rw [primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
    period hPeriod point chart hChart]
  unfold localHopfFrameSeed
  rw [
    primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart sector circleMode time,
    primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart sector
        (circleMode + fourierMode) time]
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  rw [mul_assoc]
  rw [fourier_mul_normalRootSpinFrameExponential
    period hPeriod point fourierMode circleMode time sector]
  have hSeed :=
    localHopfFrameSeed_zero_time_mode_independent
      period hPeriod point chart hChart sector circleMode
        (circleMode + fourierMode)
  unfold localHopfFrameSeed at hSeed
  rw [hSeed]

end
end P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleSpectralBridge4D
end JanusFormal
