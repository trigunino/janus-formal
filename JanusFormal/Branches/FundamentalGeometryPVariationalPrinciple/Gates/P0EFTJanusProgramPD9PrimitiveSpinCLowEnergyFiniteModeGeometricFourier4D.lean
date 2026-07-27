import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeFourierCoordinates4D

/-!
# Geometric Fourier faithfulness of finite low-energy SpinC packets

The moving phase and antipodal quotient witnesses turn every supported circle
mode into its normal-root exponential times a fixed local fiber value.  Reading
the four complex doubled-spinor coordinates therefore reduces the actual
geometric observations to the finite Fourier packets already separated in the
preceding gate.

Applying the genuine Dirac operator twice separates the Hopf zero block from
the two first-sphere signs.  The existing two-witness local multiplicity
theorems then recover all seven complex coefficients mode by mode.  Hence the
finite geometric synthesis is injective, with no new hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeGeometricFourier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstNegativeSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingPhaseLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexLinearity4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem primitiveSpinCLowEnergyFiniteModeGeometric_phase_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCHopfMovingPhaseWitnessValue
        period hPeriod sector mode time =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode 0) := by
  have hExponential :
      normalRootSpinFrameExponential period sector mode time =
        normalRootSpinFramePhase period hPeriod sector mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time) := by
    simpa using
      (normalRootSpinFrameExponential_eq_phase
        period hPeriod sector mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time))
  rw [primitiveSpinCHopfMovingPhaseWitnessValue_eq_two_smul,
    primitiveSpinCHopfMovingPhaseWitnessValue_eq_two_smul, map_smul,
    hExponential]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [map_smul, map_smul,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  have zero_apply (choice : NormalRootChoice)
      (point : MappingTorusCover (fixedEquatorData period hPeriod)) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice) point = 0 :=
    rfl
  cases sector <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCGeometricZeroModeWitnessCover,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv, zero_apply]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_lift_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
        (primitiveSpinCHopfAntipodalWitnessCover
          period hPeriod time) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod 0)) := by
  have hExponential :
      normalRootSpinFrameExponential period sector mode time =
        normalRootSpinFramePhase period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time) := by
    simpa using
      (normalRootSpinFrameExponential_eq_phase
        period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time))
  rw [hExponential]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  have zero_apply (choice : NormalRootChoice)
      (point : MappingTorusCover (fixedEquatorData period hPeriod)) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice) point = 0 :=
    rfl
  cases sector <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCHopfAntipodalWitnessCover,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv, zero_apply]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCHopfMovingAntipodalWitnessValue
        period hPeriod sector mode time =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode 0) := by
  rw [primitiveSpinCHopfMovingAntipodalWitnessValue_eq,
    primitiveSpinCHopfMovingAntipodalWitnessValue_eq, map_smul,
    d9PrimitiveSpinCComplexAction_imaginary,
    d9PrimitiveSpinCComplexAction_clifford,
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_lift_factor]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_positive_phase_basis_factor
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod coordinate sector mode)) := by
  have hCoordinate :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) =
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0) := by
    unfold d9PrimitiveMonopoleBaseCoordinate
    rw [primitiveSpinCGeometricZeroModeWitnessBase,
      primitiveSpinCGeometricZeroModeWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCGeometricZeroModeWitnessCover_sphere,
      primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase,
    hCoordinate, primitiveSpinCLowEnergyFiniteModeGeometric_phase_factor]
  simp only [map_add, map_sub, map_smul,
    d9PrimitiveSpinCComplexAction_clifford,
    d9PrimitiveSpinCComplexAction_imaginary]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_negative_phase_basis_factor
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod coordinate sector mode)) := by
  have hCoordinate :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) =
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0) := by
    unfold d9PrimitiveMonopoleBaseCoordinate
    rw [primitiveSpinCGeometricZeroModeWitnessBase,
      primitiveSpinCGeometricZeroModeWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCGeometricZeroModeWitnessCover_sphere,
      primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase,
    hCoordinate, primitiveSpinCLowEnergyFiniteModeGeometric_phase_factor]
  simp only [map_add, map_sub, map_smul,
    d9PrimitiveSpinCComplexAction_clifford,
    d9PrimitiveSpinCComplexAction_imaginary]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_positive_antipodal_basis_factor
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod coordinate sector mode)) := by
  have hCoordinate :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) =
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0) := by
    unfold d9PrimitiveMonopoleBaseCoordinate
    rw [primitiveSpinCHopfAntipodalWitnessBase,
      primitiveSpinCHopfAntipodalWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCHopfAntipodalWitnessCover_sphere,
      primitiveSpinCHopfAntipodalWitnessCover_sphere]
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal,
    hCoordinate, primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_factor]
  simp only [map_add, map_sub, map_smul,
    d9PrimitiveSpinCComplexAction_clifford,
    d9PrimitiveSpinCComplexAction_imaginary]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_negative_antipodal_basis_factor
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod coordinate sector mode)) := by
  have hCoordinate :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) =
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0) := by
    unfold d9PrimitiveMonopoleBaseCoordinate
    rw [primitiveSpinCHopfAntipodalWitnessBase,
      primitiveSpinCHopfAntipodalWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCHopfAntipodalWitnessCover_sphere,
      primitiveSpinCHopfAntipodalWitnessCover_sphere]
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal,
    hCoordinate, primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_factor]
  simp only [map_add, map_sub, map_smul,
    d9PrimitiveSpinCComplexAction_clifford,
    d9PrimitiveSpinCComplexAction_imaginary]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_complex_line_local_factor
    (indexNow indexZero : D9PrimitiveSpinCIndex period hPeriod)
    (baseNow baseZero : MappingTorus (fixedEquatorData period hPeriod))
    (hNow : baseNow ∈ d9PrimitiveSpinCBaseSet period hPeriod indexNow)
    (hZero : baseZero ∈ d9PrimitiveSpinCBaseSet period hPeriod indexZero)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (coefficient phase : Complex)
    (hState :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod indexNow baseNow state =
        d9PrimitiveSpinCComplexActionCLM phase
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod indexZero baseZero state)) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod indexNow baseNow
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter state coefficient) =
      d9PrimitiveSpinCComplexActionCLM phase
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod indexZero baseZero
          (d9PrimitiveSpinCComplexLineLinearMap
            period hPeriod .positiveQuarter state coefficient)) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
      period hPeriod indexNow baseNow hNow,
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
      period hPeriod indexZero baseZero hZero,
    hState, ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul, mul_comm]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_positive_phase_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    map_sum, map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simpa [primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap]
    using
      (primitiveSpinCLowEnergyFiniteModeGeometric_complex_line_local_factor period hPeriod
        (hNow := primitiveSpinCGeometricZeroModeWitnessBase_mem
          period hPeriod time)
        (hZero := primitiveSpinCGeometricZeroModeWitnessBase_mem
          period hPeriod 0)
        (coefficient := coefficients coordinate)
        (phase := normalRootSpinFrameExponential period sector mode time)
        (hState := primitiveSpinCLowEnergyFiniteModeGeometric_positive_phase_basis_factor
          period hPeriod coordinate sector mode time))

theorem primitiveSpinCLowEnergyFiniteModeGeometric_complex_packet_local_factor
    (indexNow indexZero : D9PrimitiveSpinCIndex period hPeriod)
    (baseNow baseZero : MappingTorus (fixedEquatorData period hPeriod))
    (hNow : baseNow ∈ d9PrimitiveSpinCBaseSet period hPeriod indexNow)
    (hZero : baseZero ∈ d9PrimitiveSpinCBaseSet period hPeriod indexZero)
    (states :
      Fin 3 →
        D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (coefficients : Fin 3 → Complex) (phase : Complex)
    (hStates : ∀ coordinate,
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod indexNow baseNow (states coordinate) =
        d9PrimitiveSpinCComplexActionCLM phase
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod indexZero baseZero (states coordinate))) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod indexNow baseNow
        (∑ coordinate,
          d9PrimitiveSpinCComplexLineLinearMap
            period hPeriod .positiveQuarter
            (states coordinate) (coefficients coordinate)) =
      d9PrimitiveSpinCComplexActionCLM phase
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod indexZero baseZero
          (∑ coordinate,
            d9PrimitiveSpinCComplexLineLinearMap
              period hPeriod .positiveQuarter
              (states coordinate) (coefficients coordinate))) := by
  rw [map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact primitiveSpinCLowEnergyFiniteModeGeometric_complex_line_local_factor period hPeriod
    indexNow indexZero baseNow baseZero hNow hZero
    (states coordinate) (coefficients coordinate) phase
    (hStates coordinate)

theorem primitiveSpinCLowEnergyFiniteModeGeometric_negative_phase_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply]
  simpa [primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap]
    using
      (primitiveSpinCLowEnergyFiniteModeGeometric_complex_packet_local_factor period hPeriod
        (hNow := primitiveSpinCGeometricZeroModeWitnessBase_mem
          period hPeriod time)
        (hZero := primitiveSpinCGeometricZeroModeWitnessBase_mem
          period hPeriod 0)
        (states := fun coordinate =>
          primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod coordinate sector mode)
        (coefficients := coefficients)
        (phase := normalRootSpinFrameExponential period sector mode time)
        (hStates := fun coordinate =>
          primitiveSpinCLowEnergyFiniteModeGeometric_negative_phase_basis_factor
            period hPeriod coordinate sector mode time))

theorem primitiveSpinCLowEnergyFiniteModeGeometric_positive_antipodal_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply]
  simpa [primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap]
    using
      (primitiveSpinCLowEnergyFiniteModeGeometric_complex_packet_local_factor period hPeriod
        (hNow := primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod time)
        (hZero := primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod 0)
        (states := fun coordinate =>
          primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod coordinate sector mode)
        (coefficients := coefficients)
        (phase := normalRootSpinFrameExponential period sector mode time)
        (hStates := fun coordinate =>
          primitiveSpinCLowEnergyFiniteModeGeometric_positive_antipodal_basis_factor
            period hPeriod coordinate sector mode time))

theorem primitiveSpinCLowEnergyFiniteModeGeometric_negative_antipodal_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply]
  simpa [primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap]
    using
      (primitiveSpinCLowEnergyFiniteModeGeometric_complex_packet_local_factor period hPeriod
        (hNow := primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod time)
        (hZero := primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod 0)
        (states := fun coordinate =>
          primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod coordinate sector mode)
        (coefficients := coefficients)
        (phase := normalRootSpinFrameExponential period sector mode time)
        (hStates := fun coordinate =>
          primitiveSpinCLowEnergyFiniteModeGeometric_negative_antipodal_basis_factor
            period hPeriod coordinate sector mode time))

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_coefficient_eq_complex_line
    (sector : NormalRootChoice) (mode : Int) (coefficient : Complex) :
    primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, mode) coefficient =
      d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) coefficient := by
  calc
    _ = primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) (coefficient * 1) := by
        rw [mul_one]
    _ = d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter coefficient
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) 1) :=
        primitiveSpinCHopfZeroModeCoefficientLinearMap_complex_smul
          period hPeriod sector mode coefficient 1
    _ = d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter coefficient
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode) := by
        congr 1
        simp [primitiveSpinCHopfZeroModeCoefficientLinearMap]
    _ = _ := rfl

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_phase_section_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase]
  exact primitiveSpinCLowEnergyFiniteModeGeometric_phase_factor period hPeriod sector mode time

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_antipodal_section_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) := by
  rw [
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal]
  exact primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_factor period hPeriod sector mode time

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_phase_coefficient_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficient : Complex) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficient) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficient)) := by
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_zero_coefficient_eq_complex_line]
  exact primitiveSpinCLowEnergyFiniteModeGeometric_complex_line_local_factor period hPeriod
    (hNow := primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time)
    (hZero := primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod 0)
    (coefficient := coefficient)
    (phase := normalRootSpinFrameExponential period sector mode time)
    (hState := primitiveSpinCLowEnergyFiniteModeGeometric_zero_phase_section_factor
      period hPeriod sector mode time)

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_antipodal_coefficient_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficient : Complex) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficient) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficient)) := by
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_zero_coefficient_eq_complex_line]
  exact primitiveSpinCLowEnergyFiniteModeGeometric_complex_line_local_factor period hPeriod
    (hNow := primitiveSpinCHopfAntipodalWitnessBase_mem
      period hPeriod time)
    (hZero := primitiveSpinCHopfAntipodalWitnessBase_mem
      period hPeriod 0)
    (coefficient := coefficient)
    (phase := normalRootSpinFrameExponential period sector mode time)
    (hState := primitiveSpinCLowEnergyFiniteModeGeometric_zero_antipodal_section_factor
      period hPeriod sector mode time)

theorem primitiveSpinCLowEnergyFiniteModeGeometric_signed_phase_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add, map_add, primitiveSpinCLowEnergyFiniteModeGeometric_positive_phase_packet_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_negative_phase_packet_factor, map_add]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_signed_antipodal_packet_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add, map_add, primitiveSpinCLowEnergyFiniteModeGeometric_positive_antipodal_packet_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_negative_antipodal_packet_factor, map_add]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_phase_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
    map_add, map_add, primitiveSpinCLowEnergyFiniteModeGeometric_zero_phase_coefficient_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_signed_phase_packet_factor, map_add]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_antipodal_factor
    (sector : NormalRootChoice) (mode : Int) (time : Real)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode coefficients)) := by
  rw [primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
    map_add, map_add, primitiveSpinCLowEnergyFiniteModeGeometric_zero_antipodal_coefficient_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_signed_antipodal_packet_factor, map_add]

/-- One of the four complex coordinates of the doubled matter fiber. -/
def primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate
    (component : NormalRootChoice) (coordinate : Fin 2) :
    D9DoubledMatterFiber →ₗ[Real] Complex where
  toFun matter :=
    match component with
    | .positiveQuarter =>
        (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).1 coordinate
    | .negativeQuarter =>
        (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).2 coordinate
  map_add' first second := by
    cases component <;> simp
  map_smul' scalar matter := by
    cases component <;> simp

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate_action
    (component : NormalRootChoice) (coordinate : Fin 2)
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      scalar *
        primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate matter := by
  have hAction :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction scalar matter
  cases component
  · simpa [primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate] using
      congrFun (congrArg Prod.fst hAction) coordinate
  · simpa [primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate] using
      congrFun (congrArg Prod.snd hAction) coordinate

theorem primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_eq_zero_of_coordinates
    (matter : D9DoubledMatterFiber)
    (hCoordinates : ∀ component coordinate,
      primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate matter = 0) :
    matter = 0 := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  apply Prod.ext
  · funext coordinate
    simpa [primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate] using
      hCoordinates .positiveQuarter coordinate
  · funext coordinate
    simpa [primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate] using
      hCoordinates .negativeQuarter coordinate

def primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficient_block
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  (Finsupp.lsingle mode).comp
    ((primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
      ((primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod 0)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod 0)).comp
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode)))

def primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
    (sector component : NormalRootChoice) (coordinate : Fin 2) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  Finsupp.lsum Real fun mode =>
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficient_block
      period hPeriod sector component coordinate mode

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients_single
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
        period hPeriod sector component coordinate
        (Finsupp.single mode coefficients) =
      Finsupp.single mode
        (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessIndex
              period hPeriod 0)
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod 0)
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
              period hPeriod sector mode coefficients))) := by
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients, Finsupp.lsum_single]
  rfl

theorem primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients_apply
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (mode : Int) :
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
        period hPeriod sector component coordinate coefficients mode =
      primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode (coefficients mode))) := by
  have hMap :
      (Finsupp.lapply mode).comp
          (primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
            period hPeriod sector component coordinate) =
        ((primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
          ((primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessIndex
              period hPeriod 0)
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod 0)).comp
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
              period hPeriod sector mode))).comp
          (Finsupp.lapply mode) := by
    apply Finsupp.lhom_ext
    intro source value
    simp only [LinearMap.comp_apply,
      primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients_single, Finsupp.lapply_apply]
    by_cases hSource : source = mode
    · subst source
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hSource),
        Finsupp.single_eq_of_ne (Ne.symm hSource)]
      simp only [map_zero]
  exact LinearMap.congr_fun hMap coefficients

theorem primitiveSpinCLowEnergyFiniteModeGeometric_phase_moving_coordinate_eq_fourier
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
        (primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
          period hPeriod sector time) =
      (normalRootSpinFrameFinsuppPacketLinearMap
        period sector time).comp
        (primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
          period hPeriod sector component coordinate) := by
  apply Finsupp.lhom_ext
  intro mode coefficients
  simp only [LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal_single,
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients_single,
    normalRootSpinFrameFinsuppPacketLinearMap_single]
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_phase_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate_action, mul_comm]

def primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficient_block
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  (Finsupp.lsingle mode).comp
    ((primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
      ((primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod 0)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod 0)).comp
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode)))

def primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
    (sector component : NormalRootChoice) (coordinate : Fin 2) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  Finsupp.lsum Real fun mode =>
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficient_block
      period hPeriod sector component coordinate mode

@[simp]
theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients_single
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
        period hPeriod sector component coordinate
        (Finsupp.single mode coefficients) =
      Finsupp.single mode
        (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod 0)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod 0)
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
              period hPeriod sector mode coefficients))) := by
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients, Finsupp.lsum_single]
  rfl

theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients_apply
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (mode : Int) :
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
        period hPeriod sector component coordinate coefficients mode =
      primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode (coefficients mode))) := by
  have hMap :
      (Finsupp.lapply mode).comp
          (primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
            period hPeriod sector component coordinate) =
        ((primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
          ((primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod 0)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod 0)).comp
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
              period hPeriod sector mode))).comp
          (Finsupp.lapply mode) := by
    apply Finsupp.lhom_ext
    intro source value
    simp only [LinearMap.comp_apply,
      primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients_single, Finsupp.lapply_apply]
    by_cases hSource : source = mode
    · subst source
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hSource),
        Finsupp.single_eq_of_ne (Ne.symm hSource)]
      simp only [map_zero]
  exact LinearMap.congr_fun hMap coefficients

theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_moving_coordinate_eq_fourier
    (sector component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
        (primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
          period hPeriod sector time) =
      (normalRootSpinFrameFinsuppPacketLinearMap
        period sector time).comp
        (primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
          period hPeriod sector component coordinate) := by
  apply Finsupp.lhom_ext
  intro mode coefficients
  simp only [LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal_single,
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients_single,
    normalRootSpinFrameFinsuppPacketLinearMap_single]
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_antipodal_factor,
    primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate_action, mul_comm]

theorem primitiveSpinCLowEnergyFiniteModeGeometric_fourier_coefficients_eq_zero
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (staticCoefficients :
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
        (Int →₀ Complex))
    (observed : Real →
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real] Complex)
    (hFourier : ∀ time,
      observed time =
        (normalRootSpinFrameFinsuppPacketLinearMap
          period sector time).comp staticCoefficients)
    (hObserved : ∀ time, observed time coefficients = 0) :
    staticCoefficients coefficients = 0 := by
  apply
    (normalRootSpinFrameFinsuppPacketFunctionLinearMap_injective
      period hPeriod sector)
  funext time
  change
    normalRootSpinFrameFinsuppPacketLinearMap
        period sector time (staticCoefficients coefficients) =
      normalRootSpinFrameFinsuppPacketLinearMap
        period sector time 0
  rw [map_zero]
  have hTime := LinearMap.congr_fun (hFourier time) coefficients
  rw [hObserved time] at hTime
  exact hTime.symm

theorem primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_local_eq_zero
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (hLocal : ∀ time,
      primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
        period hPeriod sector time coefficients = 0)
    (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod 0)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod 0)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode (coefficients mode)) = 0 := by
  apply primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_eq_zero_of_coordinates
  intro component coordinate
  have hStatic :=
    primitiveSpinCLowEnergyFiniteModeGeometric_fourier_coefficients_eq_zero period hPeriod sector coefficients
      (primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients
        period hPeriod sector component coordinate)
      (fun time =>
        (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
          (primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
            period hPeriod sector time))
      (fun time =>
        primitiveSpinCLowEnergyFiniteModeGeometric_phase_moving_coordinate_eq_fourier
          period hPeriod sector component coordinate time)
      (fun time => by
        rw [LinearMap.comp_apply, hLocal time, map_zero])
  have hMode := congrArg (fun packet : Int →₀ Complex => packet mode) hStatic
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_phase_fourier_coefficients_apply] at hMode
  exact hMode

theorem primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_local_eq_zero
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (hLocal : ∀ time,
      primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
        period hPeriod sector time coefficients = 0)
    (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod 0)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod 0)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode (coefficients mode)) = 0 := by
  apply primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_eq_zero_of_coordinates
  intro component coordinate
  have hStatic :=
    primitiveSpinCLowEnergyFiniteModeGeometric_fourier_coefficients_eq_zero period hPeriod sector coefficients
      (primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients
        period hPeriod sector component coordinate)
      (fun time =>
        (primitiveSpinCLowEnergyFiniteModeGeometric_doubled_fiber_complex_coordinate component coordinate).comp
          (primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
            period hPeriod sector time))
      (fun time =>
        primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_moving_coordinate_eq_fourier
          period hPeriod sector component coordinate time)
      (fun time => by
        rw [LinearMap.comp_apply, hLocal time, map_zero])
  have hMode := congrArg (fun packet : Int →₀ Complex => packet mode) hStatic
  rw [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_fourier_coefficients_apply] at hMode
  exact hMode

theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_sq
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode
          (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode coefficients) =
      (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 •
          coefficients.1,
        (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2) •
          coefficients.2) := by
  rw [primitiveSpinCHopfLowEnergyComplexCoefficientOperator_apply,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator_apply]
  apply Prod.ext
  · change
      (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
          ((-normalRootLeviCivitaCorrectedFrequency period sector mode) •
            coefficients.1) =
        normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 •
          coefficients.1
    rw [smul_smul]
    congr 1
    ring
  · exact primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_sq
      period sector mode coefficients.2

theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_square_gap
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode
          (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode coefficients) -
        (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2) •
          coefficients =
      ((-2 : Real) • coefficients.1, 0) := by
  rw [primitiveSpinCHopfLowEnergyComplexCoefficientOperator_sq]
  apply Prod.ext
  · change
      normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 •
            coefficients.1 -
          (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2) •
            coefficients.1 =
        (-2 : Real) • coefficients.1
    module
  · simp

theorem primitiveSpinCLowEnergyFiniteModeGeometric_zero_coefficient_eq_zero_of_phase_local
    (sector : NormalRootChoice) (mode : Int) (coefficient : Complex)
    (hLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficient) = 0) :
    coefficient = 0 := by
  have hSector := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hLocal
  rw [primitiveSpinCHopfZeroModeCoefficient_witness,
    map_smul,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_scaledMode]
    at hSector
  rw [← normalRootSpinFrameExponential_eq_phase
    period hPeriod sector mode
    (primitiveSpinCGeometricZeroModeWitnessCover period hPeriod 0)]
    at hSector
  simp [normalRootSpinFrameExponential] at hSector
  exact hSector

def primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      D9DoubledMatterFiber :=
  (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod 0)
      (primitiveSpinCGeometricZeroModeWitnessBase period hPeriod 0)).comp
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
      period hPeriod sector mode)

def primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      D9DoubledMatterFiber :=
  (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCHopfAntipodalWitnessIndex period hPeriod 0)
      (primitiveSpinCHopfAntipodalWitnessBase period hPeriod 0)).comp
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
      period hPeriod sector mode)

theorem primitiveSpinCLowEnergyFiniteModeGeometric_signed_local_components_eq_zero
    (frequency : Real) (hFrequency : frequency ≠ 0)
    (positive negative : D9DoubledMatterFiber)
    (hSum : positive + negative = 0)
    (hDifference :
      frequency • positive + (-frequency) • negative = 0) :
    positive = 0 ∧ negative = 0 := by
  have hTwiceFrequency : 2 * frequency ≠ 0 :=
    mul_ne_zero (by norm_num) hFrequency
  have hPositiveScaled : (2 * frequency) • positive = 0 := by
    calc
      (2 * frequency) • positive =
          frequency • (positive + negative) +
            (frequency • positive + (-frequency) • negative) := by
        module
      _ = 0 := by rw [hSum, hDifference]; simp
  have hPositive : positive = 0 :=
    (smul_eq_zero.mp hPositiveScaled).resolve_left hTwiceFrequency
  have hNegative : negative = 0 := by
    rw [hPositive, zero_add] at hSum
    exact hSum
  exact ⟨hPositive, hNegative⟩

theorem primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_mode_coefficients_eq_zero
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients)
    (hPhase :
      primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block
        period hPeriod sector mode coefficients = 0)
    (hAntipodal :
      primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block
        period hPeriod sector mode coefficients = 0)
    (hOperatorPhase :
      primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) = 0)
    (hOperatorAntipodal :
      primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) = 0)
    (hOperatorSqPhase :
      primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode
          (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode coefficients)) = 0)
    : coefficients = 0 := by
  let squaredFrequency :=
    normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2
  have hGapPhase :
      primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block period hPeriod sector mode
          (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
              period sector mode
              (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
                period sector mode coefficients) -
            squaredFrequency • coefficients) = 0 := by
    rw [map_sub, map_smul, hOperatorSqPhase, hPhase,
      smul_zero, sub_zero]
  rw [show squaredFrequency =
      normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2 by
        rfl,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator_square_gap] at hGapPhase
  have hScaledZeroLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode)
            ((-2 : Real) • coefficients.1)) = 0 := by
    simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
      map_zero, add_zero] using hGapPhase
  have hScaledZero :
      (-2 : Real) • coefficients.1 = 0 :=
    primitiveSpinCLowEnergyFiniteModeGeometric_zero_coefficient_eq_zero_of_phase_local
      period hPeriod sector mode ((-2 : Real) • coefficients.1)
      hScaledZeroLocal
  have hZero : coefficients.1 = 0 :=
    (smul_eq_zero.mp hScaledZero).resolve_left (by norm_num)
  have hSignedPhase :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2) = 0 := by
    simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
      hZero, map_zero, zero_add] using hPhase
  have hSignedAntipodal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2) = 0 := by
    simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block, LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
      hZero, map_zero, zero_add] using hAntipodal
  have hSignedOperatorPhase :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod 0)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode
            (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients.2)) = 0 := by
    simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientOperator_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
      hZero, smul_zero, map_zero, zero_add] using hOperatorPhase
  have hSignedOperatorAntipodal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex period hPeriod 0)
          (primitiveSpinCHopfAntipodalWitnessBase period hPeriod 0)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode
            (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients.2)) = 0 := by
    simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block, LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientOperator_apply,
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply,
      hZero, smul_zero, map_zero, zero_add] using hOperatorAntipodal
  have hPhaseSum := hSignedPhase
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add] at hPhaseSum
  have hPhaseDifference := hSignedOperatorPhase
  rw [primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_apply,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add, map_smul, map_smul] at hPhaseDifference
  simp only [map_smul] at hPhaseDifference
  have hAntipodalSum := hSignedAntipodal
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add] at hAntipodalSum
  have hAntipodalDifference := hSignedOperatorAntipodal
  rw [primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_apply,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_add, map_smul, map_smul] at hAntipodalDifference
  simp only [map_smul] at hAntipodalDifference
  have hFrequency :
      primitiveSpinCHopfFirstSphereDiracFrequency
        period sector mode ≠ 0 :=
    ne_of_gt
      (primitiveSpinCHopfFirstSphereDiracFrequency_pos period sector mode)
  rcases primitiveSpinCLowEnergyFiniteModeGeometric_signed_local_components_eq_zero
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
      hFrequency _ _ hPhaseSum hPhaseDifference with
    ⟨hPositivePhase, hNegativePhase⟩
  rcases primitiveSpinCLowEnergyFiniteModeGeometric_signed_local_components_eq_zero
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
      hFrequency _ _ hAntipodalSum hAntipodalDifference with
    ⟨hPositiveAntipodal, hNegativeAntipodal⟩
  have hPositivePhase' :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
          (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients.2.1) = 0 := by
    simpa only [primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase] using hPositivePhase
  have hNegativePhase' :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
          (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients.2.2) = 0 := by
    simpa only [primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase] using hNegativePhase
  have hPositiveAntipodal' :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients.2.1) = 0 := by
    simpa only [primitiveSpinCHopfAntipodalZeroIndex,
      primitiveSpinCHopfAntipodalZeroBase] using hPositiveAntipodal
  have hNegativeAntipodal' :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients.2.2) = 0 := by
    simpa only [primitiveSpinCHopfAntipodalZeroIndex,
      primitiveSpinCHopfAntipodalZeroBase] using hNegativeAntipodal
  have hPositiveCoefficients :
      coefficients.2.1 = 0 :=
    primitiveSpinCHopfFirstSpherePositiveComplexPacketLocal_eq_zero_coefficients
      period hPeriod sector mode coefficients.2.1
      hPositivePhase' hPositiveAntipodal'
  have hNegativeCoefficients :
      coefficients.2.2 = 0 :=
    primitiveSpinCHopfFirstSphereNegativeComplexPacketLocal_eq_zero_coefficients
      period hPeriod sector mode coefficients.2.2
      hNegativePhase' hNegativeAntipodal'
  apply Prod.ext
  · exact hZero
  · apply Prod.ext
    · exact hPositiveCoefficients
    · exact hNegativeCoefficients

/-- The finite coefficient operator acts modewise by the concrete low-energy
Dirac coefficient operator. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_apply
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (mode : Int) :
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector coefficients mode =
      primitiveSpinCHopfLowEnergyComplexCoefficientOperator
        period sector mode (coefficients mode) := by
  have hMap :
      (Finsupp.lapply mode).comp
          (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
            period sector) =
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode).comp (Finsupp.lapply mode) := by
    apply Finsupp.lhom_ext
    intro source value
    simp only [LinearMap.comp_apply,
      primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_single,
      Finsupp.lapply_apply]
    by_cases hSource : source = mode
    · subst source
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hSource),
        Finsupp.single_eq_of_ne (Ne.symm hSource)]
      simp only [map_zero]
  exact LinearMap.congr_fun hMap coefficients

/-- A vanishing finite geometric low-energy packet has zero coefficient at
every circle mode. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeSynthesis_eq_zero_coefficients
    (sector : NormalRootChoice)
    (coefficients : PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients)
    (hSynthesis :
      primitiveSpinCHopfLowEnergyFiniteModeSynthesis
        period hPeriod sector coefficients = 0) :
    coefficients = 0 := by
  let coefficientOperator :=
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator period sector
  have hOperatorSynthesis :
      primitiveSpinCHopfLowEnergyFiniteModeSynthesis
          period hPeriod sector (coefficientOperator coefficients) = 0 := by
    have hIntertwining := LinearMap.congr_fun
      (primitiveSpinCHopfLowEnergyFiniteModeSynthesis_intertwines_dirac
        period hPeriod sector) coefficients
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hSynthesis, map_zero]
      at hIntertwining
    exact hIntertwining.symm
  have hOperatorSqSynthesis :
      primitiveSpinCHopfLowEnergyFiniteModeSynthesis
          period hPeriod sector
          (coefficientOperator (coefficientOperator coefficients)) = 0 := by
    have hIntertwining := LinearMap.congr_fun
      (primitiveSpinCHopfLowEnergyFiniteModeSynthesis_intertwines_dirac
        period hPeriod sector) (coefficientOperator coefficients)
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      hOperatorSynthesis, map_zero] at hIntertwining
    exact hIntertwining.symm
  have hPhase :
      ∀ time,
        primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
          period hPeriod sector time coefficients = 0 := by
    intro time
    rw [primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal,
      LinearMap.comp_apply, hSynthesis, map_zero]
  have hAntipodal :
      ∀ time,
        primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
          period hPeriod sector time coefficients = 0 := by
    intro time
    rw [primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal,
      LinearMap.comp_apply, hSynthesis, map_zero]
  have hOperatorPhase :
      ∀ time,
        primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
          period hPeriod sector time (coefficientOperator coefficients) = 0 := by
    intro time
    rw [primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal,
      LinearMap.comp_apply, hOperatorSynthesis, map_zero]
  have hOperatorAntipodal :
      ∀ time,
        primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
          period hPeriod sector time (coefficientOperator coefficients) = 0 := by
    intro time
    rw [primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal,
      LinearMap.comp_apply, hOperatorSynthesis, map_zero]
  have hOperatorSqPhase :
      ∀ time,
        primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
          period hPeriod sector time
          (coefficientOperator (coefficientOperator coefficients)) = 0 := by
    intro time
    rw [primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal,
      LinearMap.comp_apply, hOperatorSqSynthesis, map_zero]
  apply Finsupp.ext
  intro mode
  have hPhaseMode :=
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_local_eq_zero
      period hPeriod sector coefficients hPhase mode
  have hAntipodalMode :=
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_local_eq_zero
      period hPeriod sector coefficients hAntipodal mode
  have hOperatorPhaseMode :=
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_local_eq_zero
      period hPeriod sector (coefficientOperator coefficients)
      hOperatorPhase mode
  have hOperatorAntipodalMode :=
    primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_local_eq_zero
      period hPeriod sector (coefficientOperator coefficients)
      hOperatorAntipodal mode
  have hOperatorSqPhaseMode :=
    primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_local_eq_zero
      period hPeriod sector
      (coefficientOperator (coefficientOperator coefficients))
      hOperatorSqPhase mode
  rw [show coefficientOperator =
      primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector by rfl,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_apply] at hOperatorPhaseMode
  rw [show coefficientOperator =
      primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector by rfl,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_apply] at hOperatorAntipodalMode
  rw [show coefficientOperator =
      primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector by rfl,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_apply,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_apply] at hOperatorSqPhaseMode
  apply primitiveSpinCLowEnergyFiniteModeGeometric_low_energy_mode_coefficients_eq_zero
    period hPeriod sector mode (coefficients mode)
  · simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply]
      using hPhaseMode
  · simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block, LinearMap.comp_apply]
      using hAntipodalMode
  · simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply]
      using hOperatorPhaseMode
  · simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_antipodal_mode_block, LinearMap.comp_apply]
      using hOperatorAntipodalMode
  · simpa only [primitiveSpinCLowEnergyFiniteModeGeometric_phase_mode_block, LinearMap.comp_apply]
      using hOperatorSqPhaseMode

/-- In each fixed normal-root sector, finite geometric synthesis of the Hopf
zero block and both first-sphere signed blocks is injective across circle
modes. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeSynthesis_injective
    (sector : NormalRootChoice) :
    Function.Injective
      (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
        period hPeriod sector) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply primitiveSpinCHopfLowEnergyFiniteModeSynthesis_eq_zero_coefficients
    period hPeriod sector (first - second)
  rw [map_sub, hEqual, sub_self]

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeGeometricFourier4D
end JanusFormal
