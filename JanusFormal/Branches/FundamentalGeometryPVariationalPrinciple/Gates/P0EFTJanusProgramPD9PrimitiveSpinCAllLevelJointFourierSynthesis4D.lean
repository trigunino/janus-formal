import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D

/-!
# Joint normal-root Fourier synthesis for the all-level SpinC packet

The positive and negative normal-root towers occupy respectively the odd
and even rotating-frame Fourier indices.  After doubling the cover time,
their union is therefore one ordinary integer Fourier packet.  This gives
finite Fourier faithfulness simultaneously in the sector and circle-mode
labels.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators Manifold ContDiff
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance jointFourierPrimitiveSpinCComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance jointFourierPrimitiveSpinCComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-- Joint normal-root/circle-mode label. -/
abbrev PrimitiveSpinCJointNormalFourierLabel :=
  NormalRootChoice × Int

/-- The two normal-root sectors jointly enumerate all rotating-frame
integer frequencies. -/
def primitiveSpinCJointNormalFourierModeIndex
    (label : PrimitiveSpinCJointNormalFourierLabel) : Int :=
  normalRootSpinFrameModeIndex label.1 label.2

theorem primitiveSpinCJointNormalFourierModeIndex_injective :
    Function.Injective primitiveSpinCJointNormalFourierModeIndex := by
  rintro ⟨firstSector, firstMode⟩ ⟨secondSector, secondMode⟩ hEqual
  cases firstSector <;> cases secondSector <;>
    simp [primitiveSpinCJointNormalFourierModeIndex,
      normalRootSpinFrameModeIndex] at hEqual ⊢ <;>
    omega

/-- Doubling cover time identifies the joint pair/even packet with the
ordinary negative-sector integer Fourier packet. -/
theorem normalRootSpinFrameExponential_double_time
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    normalRootSpinFrameExponential period sector mode (2 * time) =
      normalRootSpinFrameExponential period .negativeQuarter
        (primitiveSpinCJointNormalFourierModeIndex (sector, mode)) time := by
  cases sector <;>
    simp only [normalRootSpinFrameExponential,
      normalRootSpinFrameFrequency,
      primitiveSpinCJointNormalFourierModeIndex,
      normalRootSpinFrameModeIndex] <;>
    congr 1 <;>
    push_cast <;>
    ring

/-- Finitely supported scalar Fourier synthesis across both normal-root
sectors and all circle modes. -/
def primitiveSpinCJointNormalFourierPacketLinearMap
    (time : Real) :
    (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) →ₗ[Real] Complex :=
  Finsupp.lsum Real fun label =>
    (normalModeComplexRightMulRealCLM
      (normalRootSpinFrameExponential
        period label.1 label.2 time)).toLinearMap

@[simp]
theorem primitiveSpinCJointNormalFourierPacketLinearMap_single
    (time : Real) (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficient : Complex) :
    primitiveSpinCJointNormalFourierPacketLinearMap
        period time (Finsupp.single label coefficient) =
      coefficient *
        normalRootSpinFrameExponential
          period label.1 label.2 time := by
  rw [primitiveSpinCJointNormalFourierPacketLinearMap,
    Finsupp.lsum_single]
  rfl

theorem primitiveSpinCJointNormalFourierPacketLinearMap_double_time
    (time : Real)
    (coefficients :
      PrimitiveSpinCJointNormalFourierLabel →₀ Complex) :
    primitiveSpinCJointNormalFourierPacketLinearMap
        period (2 * time) coefficients =
      normalRootSpinFrameFinsuppPacketLinearMap
        period .negativeQuarter time
        (Finsupp.mapDomain
          primitiveSpinCJointNormalFourierModeIndex coefficients) := by
  simp only [primitiveSpinCJointNormalFourierPacketLinearMap,
    normalRootSpinFrameFinsuppPacketLinearMap,
    Finsupp.lsum_apply]
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro label hLabel
    rw [normalRootSpinFrameExponential_double_time]
  · intro mode
    exact map_zero _
  · intro mode first second
    exact map_add _ first second

/-- A joint packet viewed as its scalar function on the cover time. -/
def primitiveSpinCJointNormalFourierPacketFunctionLinearMap :
    (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) →ₗ[Real]
      (Real → Complex) where
  toFun coefficients time :=
    primitiveSpinCJointNormalFourierPacketLinearMap
      period time coefficients
  map_add' first second := by
    funext time
    exact map_add
      (primitiveSpinCJointNormalFourierPacketLinearMap period time)
      first second
  map_smul' scalar coefficients := by
    funext time
    exact map_smul
      (primitiveSpinCJointNormalFourierPacketLinearMap period time)
      scalar coefficients

/-- Finite Fourier synthesis is faithful jointly in both normal-root
sectors and all circle modes. -/
theorem primitiveSpinCJointNormalFourierPacketFunctionLinearMap_injective :
    period ≠ 0 →
    Function.Injective
      (primitiveSpinCJointNormalFourierPacketFunctionLinearMap period) := by
  intro hPeriod
  intro first second hEqual
  apply Finsupp.mapDomain_injective
    primitiveSpinCJointNormalFourierModeIndex_injective
  apply normalRootSpinFrameFinsuppPacketFunctionLinearMap_injective
    period hPeriod .negativeQuarter
  funext time
  have hTime := congrFun hEqual (2 * time)
  change
    primitiveSpinCJointNormalFourierPacketLinearMap
        period (2 * time) first =
      primitiveSpinCJointNormalFourierPacketLinearMap
        period (2 * time) second at hTime
  rw [primitiveSpinCJointNormalFourierPacketLinearMap_double_time,
    primitiveSpinCJointNormalFourierPacketLinearMap_double_time] at hTime
  exact hTime

/-! ## Moving witnesses over arbitrary sphere points -/

/-- Cover representative over an arbitrary sphere point and cover time. -/
def primitiveSpinCNullPacketMovingWitnessCover
    (point : MonopoleSphere) (time : Real) :
    ThroatCover period hPeriod :=
  ⟨equatorialTwoSphereHomeomorph.symm point, time⟩

/-- Quotient-throat representative of the moving witness. -/
def primitiveSpinCNullPacketMovingWitnessBase
    (point : MonopoleSphere) (time : Real) :
    ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCNullPacketMovingWitnessCover
      period hPeriod point time)

/-- North local chart at the moving witness. -/
def primitiveSpinCNullPacketMovingWitnessIndex
    (point : MonopoleSphere) (time : Real) :
    D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCNullPacketMovingWitnessCover
    period hPeriod point time, .north)

@[simp]
theorem primitiveSpinCNullPacketMovingWitnessCover_time
    (point : MonopoleSphere) (time : Real) :
    (primitiveSpinCNullPacketMovingWitnessCover
      period hPeriod point time).time = time :=
  rfl

@[simp]
theorem primitiveSpinCNullPacketMovingWitnessCover_sphere
    (point : MonopoleSphere) (time : Real) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCNullPacketMovingWitnessCover
          period hPeriod point time) =
      point := by
  simp [primitiveSpinCNullPacketMovingWitnessCover,
    d9MonopoleSphereCoverProjection]

@[simp]
theorem primitiveSpinCNullPacketMovingWitnessBase_coordinate
    (point : MonopoleSphere) (time : Real) (coordinate : Fin 3) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      monopoleSphereCoordinate point coordinate := by
  unfold d9PrimitiveMonopoleBaseCoordinate
    primitiveSpinCNullPacketMovingWitnessBase
  rw [d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere]

theorem primitiveSpinCNullPacketMovingWitnessBase_mem
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (time : Real) :
    primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time) := by
  constructor
  · exact ((mappingTorusMk_isCoveringMap
      (ThroatData period hPeriod)).isLocalHomeomorph)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time) ∈
        monopoleChartDomain .north
    rw [primitiveSpinCNullPacketMovingWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCNullPacketMovingWitnessCover_sphere]
    exact hNorth

/-- A moving normal mode is its time-zero value multiplied by the exact
rotating-frame exponential. -/
theorem primitiveSpinCNormalModeDoubledLift_moving_factor
    (point : MonopoleSphere)
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
        (primitiveSpinCNullPacketMovingWitnessCover
          period hPeriod point time) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point 0)) := by
  have hExponential :
      normalRootSpinFrameExponential period sector mode time =
        normalRootSpinFramePhase period hPeriod sector mode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time) := by
    simpa using
      (normalRootSpinFrameExponential_eq_phase
        period hPeriod sector mode
        (primitiveSpinCNullPacketMovingWitnessCover
          period hPeriod point time))
  rw [hExponential]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  have zero_apply (choice : NormalRootChoice)
      (coverPoint : ThroatCover period hPeriod) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice)
          coverPoint = 0 := rfl
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCNullPacketMovingWitnessCover,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv, zero_apply]

/-- The arbitrary-sphere Hopf zero mode has the same exact moving Fourier
factor. -/
theorem primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) := by
  let phase :=
    normalRootSpinFrameExponential period sector mode time
  let zeroMode :=
    primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessCover
        period hPeriod point 0)
  have hFirst :
      d9PrimitiveSpinCHopfFirstFrameCLM sector
          (d9PrimitiveSpinCComplexActionCLM phase zeroMode) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9PrimitiveSpinCHopfFirstFrameCLM sector zeroMode) := by
    simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply]
    rw [← d9PrimitiveSpinCComplexAction_clifford,
      ← d9PrimitiveSpinCComplexAction_imaginary, map_sub]
  have hSecond :
      d9PrimitiveSpinCHopfSecondFrameCLM sector
          (d9PrimitiveSpinCComplexActionCLM phase zeroMode) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9PrimitiveSpinCHopfSecondFrameCLM sector zeroMode) := by
    simp only [d9PrimitiveSpinCHopfSecondFrameCLM_apply]
    rw [← d9PrimitiveSpinCComplexAction_clifford,
      ← d9PrimitiveSpinCComplexAction_imaginary, map_add]
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth time),
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth 0)]
  change
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCNullPacketMovingWitnessCover
          period hPeriod point time, .north)
        (mappingTorusMk (ThroatData period hPeriod)
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time)) =
      d9PrimitiveSpinCComplexActionCLM phase
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCNullPacketMovingWitnessCover
              period hPeriod point 0, .north)
            (mappingTorusMk (ThroatData period hPeriod)
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point 0)))
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere,
    primitiveSpinCNullPacketMovingWitnessCover_sphere,
    primitiveSpinCNormalModeDoubledLift_moving_factor]
  change
    d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroLocalValue .north point)
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (d9PrimitiveSpinCComplexActionCLM phase zeroMode)) +
        d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroComplementLocalValue .north point)
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (d9PrimitiveSpinCComplexActionCLM phase zeroMode)) =
      d9PrimitiveSpinCComplexActionCLM phase
        (d9PrimitiveSpinCComplexActionCLM
            (primitiveMonopoleZeroLocalValue .north point)
            (d9PrimitiveSpinCHopfFirstFrameCLM sector zeroMode) +
          d9PrimitiveSpinCComplexActionCLM
            (primitiveMonopoleZeroComplementLocalValue .north point)
            (d9PrimitiveSpinCHopfSecondFrameCLM sector zeroMode))
  rw [hFirst, hSecond, map_add,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1 <;> ring

/-- Local evaluation turns the smooth null multiplier into the transported
complex action of its scalar null form, uniformly in cover time. -/
theorem primitiveSpinCNullMultiplicationLocalCoordinate_moving
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (time : Real) (parameter : Complex)
    (state : SmoothSection period hPeriod) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point time)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          state) := by
  rw [primitiveSpinCNullMultiplicationLinearMap_apply, map_sum]
  simp_rw [
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth time),
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    primitiveSpinCGeometricSectionLocalCoordinate_realScalarMul,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [map_sum,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp_rw [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_smul]
  unfold primitiveSpinCNullSphereScalar
  simp_rw [← Complex.coe_smul, smul_smul]
  rw [← Finset.sum_smul]

/-- Every smooth null-power packet member has one exact joint Fourier
factor; the entire sphere polynomial remains in its time-zero fiber value. -/
theorem primitiveSpinCNullPowerLocalCoordinate_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (parameter : Complex)
    (sector : NormalRootChoice) (mode : Int)
    (degree : Nat) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector mode degree) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullPowerSection
            period hPeriod parameter sector mode degree)) := by
  induction degree with
  | zero =>
      simpa only [primitiveSpinCNullPowerSection_zero] using
        primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor
          period hPeriod point hNorth sector mode time
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullPowerSection_succ,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving
          period hPeriod point hNorth time,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving
          period hPeriod point hNorth 0,
        inductionHypothesis,
        ← d9PrimitiveSpinCComplexAction_mul,
        ← d9PrimitiveSpinCComplexAction_mul,
        mul_comm]

/-! ## Fixed-level synthesis across both sectors and every circle mode -/

/-- One of the four complex coordinates of the doubled matter fiber. -/
def primitiveSpinCJointDoubledFiberComplexCoordinate
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
theorem primitiveSpinCJointDoubledFiberComplexCoordinate_action
    (component : NormalRootChoice) (coordinate : Fin 2)
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    primitiveSpinCJointDoubledFiberComplexCoordinate component coordinate
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      scalar *
        primitiveSpinCJointDoubledFiberComplexCoordinate
          component coordinate matter := by
  have hAction :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction scalar matter
  cases component
  · simpa [primitiveSpinCJointDoubledFiberComplexCoordinate] using
      congrFun (congrArg Prod.fst hAction) coordinate
  · simpa [primitiveSpinCJointDoubledFiberComplexCoordinate] using
      congrFun (congrArg Prod.snd hAction) coordinate

theorem primitiveSpinCJointDoubledFiber_eq_zero_of_coordinates
    (matter : D9DoubledMatterFiber)
    (hCoordinates : ∀ component coordinate,
      primitiveSpinCJointDoubledFiberComplexCoordinate
        component coordinate matter = 0) :
    matter = 0 := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  apply Prod.ext
  · funext coordinate
    simpa [primitiveSpinCJointDoubledFiberComplexCoordinate] using
      hCoordinates .positiveQuarter coordinate
  · funext coordinate
    simpa [primitiveSpinCJointDoubledFiberComplexCoordinate] using
      hCoordinates .negativeQuarter coordinate

/-- Full finite label at one fixed positive sphere level. -/
abbrev PrimitiveSpinCFixedPositiveJointIndex (positiveLevel : Nat) :=
  PrimitiveSpinCJointNormalFourierLabel ×
    Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))

/-- Genuine null-harmonic section indexed jointly by sector, circle mode
and the complete multiplicity packet at one positive level. -/
def primitiveSpinCFixedPositiveJointFamily
    (positiveLevel : Nat)
    (index : PrimitiveSpinCFixedPositiveJointIndex positiveLevel) :
    SmoothSection period hPeriod :=
  (primitiveSpinCAllLevelNullHarmonicSquaredSeed
    period hPeriod positiveLevel index.2 index.1.1 index.1.2
  ).scalarSection

theorem primitiveSpinCFixedPositiveJointFamily_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (positiveLevel : Nat)
    (index : PrimitiveSpinCFixedPositiveJointIndex positiveLevel)
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCFixedPositiveJointFamily
          period hPeriod positiveLevel index) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential
          period index.1.1 index.1.2 time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCFixedPositiveJointFamily
            period hPeriod positiveLevel index)) := by
  simpa [primitiveSpinCFixedPositiveJointFamily,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed] using
    primitiveSpinCNullPowerLocalCoordinate_moving_factor
      period hPeriod point hNorth
      (primitiveSpinCNullGeometricParameter positiveLevel index.2)
      index.1.1 index.1.2 (positiveLevel + 1) time

/-- Complex finite synthesis at one positive sphere level, now with both
normal-root sectors and every circle mode in the domain. -/
def primitiveSpinCFixedPositiveJointSynthesis
    (positiveLevel : Nat) :
    (PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCFixedPositiveJointFamily
      period hPeriod positiveLevel)

/-- The same coefficient synthesis viewed over the underlying real module,
so it composes directly with local trivializations. -/
def primitiveSpinCFixedPositiveJointRealSynthesis
    (positiveLevel : Nat) :
    (PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) →ₗ[Real]
      SmoothSection period hPeriod :=
  Finsupp.lsum Real fun index =>
    d9PrimitiveSpinCComplexLineLinearMap
      period hPeriod .positiveQuarter
      (primitiveSpinCFixedPositiveJointFamily
        period hPeriod positiveLevel index)

/-- The real-line implementation of coefficient synthesis is definitionally
the same intrinsic complex synthesis. -/
theorem primitiveSpinCFixedPositiveJointRealSynthesis_eq_synthesis
    (positiveLevel : Nat)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) :
    primitiveSpinCFixedPositiveJointRealSynthesis
        period hPeriod positiveLevel coefficients =
      primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel coefficients := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCFixedPositiveJointRealSynthesis,
        primitiveSpinCFixedPositiveJointSynthesis]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, inductionHypothesis]
      simp [primitiveSpinCFixedPositiveJointRealSynthesis,
        primitiveSpinCFixedPositiveJointSynthesis,
        primitiveSpinCComplex_smul,
        d9PrimitiveSpinCComplexLineLinearMap_apply,
        d9PrimitiveSpinCComplexScalarSection_eq_re_add_im]

/-- One static time-zero fiber coordinate inserted at its joint Fourier
label. -/
def primitiveSpinCFixedPositiveJointLocalFourierCoefficientBlock
    (point : MonopoleSphere) (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCFixedPositiveJointIndex positiveLevel) :
    Complex →ₗ[Real]
      (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) :=
  (Finsupp.lsingle index.1).comp
    ((normalModeComplexRightMulRealCLM
      (primitiveSpinCJointDoubledFiberComplexCoordinate
        component coordinate
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCFixedPositiveJointFamily
            period hPeriod positiveLevel index)))).toLinearMap)

/-- Static Fourier coefficients obtained by grouping all multiplicities
with the same sector and circle mode. -/
def primitiveSpinCFixedPositiveJointLocalFourierCoefficients
    (point : MonopoleSphere) (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    (PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) →ₗ[Real]
      (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) :=
  Finsupp.lsum Real fun index =>
    primitiveSpinCFixedPositiveJointLocalFourierCoefficientBlock
      period hPeriod point positiveLevel component coordinate index

@[simp]
theorem primitiveSpinCFixedPositiveJointLocalFourierCoefficients_single
    (point : MonopoleSphere) (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCFixedPositiveJointIndex positiveLevel)
    (coefficient : Complex) :
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients
        period hPeriod point positiveLevel component coordinate
        (Finsupp.single index coefficient) =
      Finsupp.single index.1
        (coefficient *
          primitiveSpinCJointDoubledFiberComplexCoordinate
            component coordinate
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCNullPacketMovingWitnessIndex
                period hPeriod point 0)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0)
              (primitiveSpinCFixedPositiveJointFamily
                period hPeriod positiveLevel index))) := by
  rw [primitiveSpinCFixedPositiveJointLocalFourierCoefficients,
    Finsupp.lsum_single]
  rfl

/-- Evaluation at one Fourier label is exactly the finite sum over the
sphere multiplicities carrying that label. -/
theorem primitiveSpinCFixedPositiveJointLocalFourierCoefficients_apply
    (point : MonopoleSphere) (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel) :
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients
        period hPeriod point positiveLevel component coordinate
        coefficients label =
      ∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
        coefficients (label, multiplicity) *
          primitiveSpinCJointDoubledFiberComplexCoordinate
            component coordinate
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCNullPacketMovingWitnessIndex
                period hPeriod point 0)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0)
              (primitiveSpinCFixedPositiveJointFamily
                period hPeriod positiveLevel (label, multiplicity))) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCFixedPositiveJointLocalFourierCoefficients]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [inductionHypothesis]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib,
        primitiveSpinCFixedPositiveJointLocalFourierCoefficients_single]
      rcases index with ⟨indexLabel, indexMultiplicity⟩
      by_cases hLabel : indexLabel = label
      · subst label
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, hLabel]

/-- One moving local fiber coordinate of the full fixed-level synthesis. -/
def primitiveSpinCFixedPositiveJointMovingCoordinate
    (point : MonopoleSphere) (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    (PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) →ₗ[Real]
      Complex :=
  (primitiveSpinCJointDoubledFiberComplexCoordinate
      component coordinate).comp
    ((primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)).comp
      (primitiveSpinCFixedPositiveJointRealSynthesis
        period hPeriod positiveLevel))

theorem primitiveSpinCFixedPositiveJointMovingCoordinate_single
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real)
    (index : PrimitiveSpinCFixedPositiveJointIndex positiveLevel)
    (coefficient : Complex) :
    primitiveSpinCFixedPositiveJointMovingCoordinate
        period hPeriod point positiveLevel component coordinate time
        (Finsupp.single index coefficient) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCFixedPositiveJointLocalFourierCoefficients
          period hPeriod point positiveLevel component coordinate
          (Finsupp.single index coefficient)) := by
  simp only [primitiveSpinCFixedPositiveJointMovingCoordinate,
    LinearMap.comp_apply, primitiveSpinCFixedPositiveJointRealSynthesis,
    Finsupp.lsum_single]
  rw [
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth time)
      (primitiveSpinCFixedPositiveJointFamily
        period hPeriod positiveLevel index)
      coefficient,
    primitiveSpinCFixedPositiveJointFamily_moving_factor
      period hPeriod point hNorth positiveLevel index time,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients_single,
    primitiveSpinCJointNormalFourierPacketLinearMap_single]
  ring

/-- Every moving fiber coordinate is exactly the joint scalar Fourier
packet of its grouped time-zero coordinates. -/
theorem primitiveSpinCFixedPositiveJointMovingCoordinate_eq_fourier
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    primitiveSpinCFixedPositiveJointMovingCoordinate
        period hPeriod point positiveLevel component coordinate time =
      (primitiveSpinCJointNormalFourierPacketLinearMap period time).comp
        (primitiveSpinCFixedPositiveJointLocalFourierCoefficients
          period hPeriod point positiveLevel component coordinate) := by
  apply Finsupp.lhom_ext
  intro index coefficient
  simp only [LinearMap.comp_apply]
  exact primitiveSpinCFixedPositiveJointMovingCoordinate_single
    period hPeriod point hNorth positiveLevel component coordinate
    time index coefficient

/-- If the global fixed-level synthesis vanishes, every grouped
sector/mode Fourier coefficient vanishes at every north-chart point. -/
theorem primitiveSpinCFixedPositiveJointLocalFourierCoefficients_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (positiveLevel : Nat)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (hSynthesis :
      primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel coefficients = 0) :
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients
        period hPeriod point positiveLevel component coordinate
        coefficients = 0 := by
  apply
    (primitiveSpinCJointNormalFourierPacketFunctionLinearMap_injective
      period hPeriod)
  funext time
  change
    primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCFixedPositiveJointLocalFourierCoefficients
          period hPeriod point positiveLevel component coordinate
          coefficients) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time 0
  rw [map_zero, ← LinearMap.comp_apply,
    ← primitiveSpinCFixedPositiveJointMovingCoordinate_eq_fourier
      period hPeriod point hNorth positiveLevel component coordinate time]
  simp only [primitiveSpinCFixedPositiveJointMovingCoordinate,
    LinearMap.comp_apply,
    primitiveSpinCFixedPositiveJointRealSynthesis_eq_synthesis,
    hSynthesis, map_zero]

/-- Time-zero local fiber sum carried by one fixed sector/mode label. -/
def primitiveSpinCFixedPositiveJointLocalModeFiber
    (point : MonopoleSphere) (positiveLevel : Nat)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex) :
    D9DoubledMatterFiber :=
  ∑ multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
    d9PrimitiveSpinCComplexActionCLM
      (coefficients (label, multiplicity))
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point 0)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0)
        (primitiveSpinCFixedPositiveJointFamily
          period hPeriod positiveLevel (label, multiplicity)))

theorem primitiveSpinCFixedPositiveJointLocalModeFiber_coordinate
    (point : MonopoleSphere) (positiveLevel : Nat)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    primitiveSpinCJointDoubledFiberComplexCoordinate component coordinate
        (primitiveSpinCFixedPositiveJointLocalModeFiber
          period hPeriod point positiveLevel label coefficients) =
      primitiveSpinCFixedPositiveJointLocalFourierCoefficients
        period hPeriod point positiveLevel component coordinate
        coefficients label := by
  rw [primitiveSpinCFixedPositiveJointLocalModeFiber, map_sum,
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients_apply]
  apply Finset.sum_congr rfl
  intro multiplicity _
  exact primitiveSpinCJointDoubledFiberComplexCoordinate_action
    component coordinate _ _

/-- Fourier separation makes every individual sector/mode local fiber sum
zero. -/
theorem primitiveSpinCFixedPositiveJointLocalModeFiber_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (positiveLevel : Nat)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (hSynthesis :
      primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel coefficients = 0) :
    primitiveSpinCFixedPositiveJointLocalModeFiber
        period hPeriod point positiveLevel label coefficients = 0 := by
  apply primitiveSpinCJointDoubledFiber_eq_zero_of_coordinates
  intro component coordinate
  rw [primitiveSpinCFixedPositiveJointLocalModeFiber_coordinate]
  have hCoefficients :=
    primitiveSpinCFixedPositiveJointLocalFourierCoefficients_eq_zero
      period hPeriod point hNorth positiveLevel component coordinate
      coefficients hSynthesis
  exact DFunLike.congr_fun hCoefficients label

/-- The separated sector/mode block satisfies the physical null-harmonic
scalar relation on the positive north-chart locus. -/
theorem primitiveSpinCFixedPositiveJointLocalMode_scalar_relation
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hCoordinate : 0 < monopoleSphereCoordinate point 0)
    (positiveLevel : Nat)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (hSynthesis :
      primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel coefficients = 0) :
    ∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
      coefficients (label, multiplicity) *
        primitiveSpinCNullSphereScalar
          (primitiveSpinCNullGeometricParameter
            positiveLevel multiplicity) point ^ (positiveLevel + 1) = 0 := by
  have hFiber :=
    primitiveSpinCFixedPositiveJointLocalModeFiber_eq_zero
      period hPeriod point hNorth positiveLevel label coefficients hSynthesis
  have hLocal := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap label.1)
    hFiber
  rw [primitiveSpinCFixedPositiveJointLocalModeFiber,
    map_sum, map_zero] at hLocal
  simp_rw [
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction
  ] at hLocal
  change
    (∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
      coefficients (label, multiplicity) *
        primitiveSpinCNullPacketLocalCoefficientLinearMap
          period hPeriod point label.1
          (primitiveSpinCFixedPositiveJointFamily
            period hPeriod positiveLevel (label, multiplicity))) = 0 at hLocal
  simp_rw [primitiveSpinCFixedPositiveJointFamily,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed,
    primitiveSpinCNullPacketLocalCoefficient_powerSection
      period hPeriod point hNorth] at hLocal
  have hFactored :
      (∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
        coefficients (label, multiplicity) *
          primitiveSpinCNullSphereScalar
            (primitiveSpinCNullGeometricParameter
              positiveLevel multiplicity) point ^ (positiveLevel + 1)) *
        primitiveSpinCNullPacketLocalCoefficientLinearMap
          period hPeriod point label.1
          (primitiveSpinCHopfZeroModeSection
            period hPeriod label.1 label.2) = 0 := by
    rw [Finset.sum_mul]
    convert hLocal using 1
    apply Finset.sum_congr rfl
    intro multiplicity _
    ring
  exact (mul_eq_zero.mp hFactored).resolve_right
    (primitiveSpinCNullPacketLocalCoefficient_zeroMode_ne_zero
      period hPeriod point hNorth hCoordinate label.1 label.2)

/-- At a fixed positive sphere level, global vanishing forces every
sector/mode/multiplicity coefficient to vanish. -/
theorem primitiveSpinCFixedPositiveJoint_coefficient_eq_zero
    (positiveLevel : Nat)
    (coefficients :
      PrimitiveSpinCFixedPositiveJointIndex positiveLevel →₀ Complex)
    (hSynthesis :
      primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel coefficients = 0)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    coefficients (label, multiplicity) = 0 := by
  classical
  let reindex :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) ≃
        Fin (2 * (positiveLevel + 1) + 1) :=
    finCongr
      (primitiveSpinCSolidPacket_degeneracy_eq (positiveLevel + 1))
  let solidCoefficients :
      Fin (2 * (positiveLevel + 1) + 1) → Complex :=
    fun basis => coefficients (label, reindex.symm basis)
  have hSolid :=
    primitiveSpinCNullHarmonicSmoothPacket_coefficients_eq_zero_of_scalar_relation
      (positiveLevel + 1) solidCoefficients
      (fun point hNorth hCoordinate => by
        have hPhysical :=
          primitiveSpinCFixedPositiveJointLocalMode_scalar_relation
            period hPeriod point hNorth hCoordinate positiveLevel label
            coefficients hSynthesis
        calc
          (∑ basis : Fin (2 * (positiveLevel + 1) + 1),
              solidCoefficients basis *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (positiveLevel + 1) basis)
                  point ^ (positiveLevel + 1)) =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
              solidCoefficients (reindex physical) *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (positiveLevel + 1) (reindex physical))
                  point ^ (positiveLevel + 1) := by
              symm
              exact reindex.sum_comp
                (fun basis : Fin (2 * (positiveLevel + 1) + 1) =>
                  solidCoefficients basis *
                    primitiveSpinCNullSphereScalar
                      (primitiveSpinCSolidPacketParameter
                        (positiveLevel + 1) basis)
                      point ^ (positiveLevel + 1))
          _ =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)),
              coefficients (label, physical) *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCNullGeometricParameter
                    positiveLevel physical)
                  point ^ (positiveLevel + 1) := by
              apply Finset.sum_congr rfl
              intro physical _
              simp [solidCoefficients, reindex,
                primitiveSpinCNullGeometricParameter]
          _ = 0 := hPhysical)
  have hAt := hSolid (reindex multiplicity)
  simpa [solidCoefficients, reindex] using hAt

/-- The full finite synthesis at one positive level is faithful jointly in
both normal-root sectors, every circle mode and every multiplicity. -/
theorem primitiveSpinCFixedPositiveJointSynthesis_injective
    (positiveLevel : Nat) :
    Function.Injective
      (primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel) := by
  intro first second hEqual
  have hKernel :
      primitiveSpinCFixedPositiveJointSynthesis
          period hPeriod positiveLevel (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  apply sub_eq_zero.mp
  apply Finsupp.ext
  rintro ⟨label, multiplicity⟩
  exact primitiveSpinCFixedPositiveJoint_coefficient_eq_zero
    period hPeriod positiveLevel (first - second) hKernel label multiplicity

/-- Equivalently, the complete fixed-level family is jointly
complex-linearly independent in all of its physical labels. -/
theorem primitiveSpinCFixedPositiveJointFamily_linearIndependent
    (positiveLevel : Nat) :
    LinearIndependent Complex
      (primitiveSpinCFixedPositiveJointFamily
        period hPeriod positiveLevel) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  exact primitiveSpinCFixedPositiveJointSynthesis_injective
    period hPeriod positiveLevel

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
end JanusFormal
