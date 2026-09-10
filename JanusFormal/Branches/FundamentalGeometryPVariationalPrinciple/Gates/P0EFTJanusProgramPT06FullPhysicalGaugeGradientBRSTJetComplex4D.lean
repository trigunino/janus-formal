import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FullPhysicalFiniteBVJetComplex4D

/-!
# Full physical carrier with formal Abelian gauge-gradient BRST

This gate enlarges the Gate895 carrier by four covector-valued Abelian ghost
gradients, one for each actual gauge-potential value slot.  The differential
sends those gradients into the four genuine physical gauge slots, kills the
gradient slots, and retains the existing finite metric-BV differential.
It is nonzero on every nonzero ghost gradient and square-zero.

The differential prolongs coefficientwise through the Gate875 spatial jet
tower and commutes with truncation and formal total derivatives.  The added
ghost data model `dc` directly in a fixed frame; no scalar-ghost jet whose
derivative is proved to equal these covectors, and no nonlinear physical BV
action, is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FullPhysicalGaugeGradientBRSTJetComplex4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D
open P0EFTJanusProgramPT06FiniteMetricBVAffineExactComplex4D
open P0EFTJanusProgramPT06FullPhysicalFiniteBVJetComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

private abbrev GaugeValueFiber := ActualGaugeValueProductFiber
private abbrev LLValueFiber := ActualLLValueProductFiber
private abbrev MetricValueFiber := ActualMetricValueProductFiber
private abbrev SpinCValueFiber := ActualSpinCValueProductFiber
private abbrev PhysicalValueFiber := ActualPhysicalValueProductFiber

local instance physicalValueFiberFiniteDimensional :
    FiniteDimensional Real PhysicalValueFiber :=
  FiniteDimensional.of_injective
    (programPT06ThroatSpatialJetCoordinateInjection
      (Fiber := PhysicalValueFiber)
      programPT06SecondOrderZeroMultiIndex).toLinearMap
    (by
      intro first second hEqual
      simpa using congrArg
        (fun jet => jet programPT06SecondOrderZeroMultiIndex) hEqual)

/-- Inclusion of the four actual gauge-potential values into the eleven-slot
physical value product. -/
def programPT06FullPhysicalGaugeValueInclusion :
    GaugeValueFiber →L[Real] PhysicalValueFiber :=
  (ContinuousLinearMap.inl Real
      ((GaugeValueFiber × LLValueFiber) × MetricValueFiber)
      SpinCValueFiber).comp
    ((ContinuousLinearMap.inl Real
        (GaugeValueFiber × LLValueFiber) MetricValueFiber).comp
      (ContinuousLinearMap.inl Real GaugeValueFiber LLValueFiber))

/-- Projection from the eleven-slot physical product to its four gauge
values. -/
def programPT06FullPhysicalGaugeValueProjection :
    PhysicalValueFiber →L[Real] GaugeValueFiber :=
  (ContinuousLinearMap.fst Real GaugeValueFiber LLValueFiber).comp
    ((ContinuousLinearMap.fst Real
        (GaugeValueFiber × LLValueFiber) MetricValueFiber).comp
      (ContinuousLinearMap.fst Real
        ((GaugeValueFiber × LLValueFiber) × MetricValueFiber)
        SpinCValueFiber))

@[simp] theorem programPT06FullPhysicalGaugeValueProjection_inclusion
    (gauge : GaugeValueFiber) :
    programPT06FullPhysicalGaugeValueProjection
        (programPT06FullPhysicalGaugeValueInclusion gauge) = gauge :=
  rfl

local instance gaugeValueFiberFiniteDimensional :
    FiniteDimensional Real GaugeValueFiber :=
  FiniteDimensional.of_injective
    programPT06FullPhysicalGaugeValueInclusion.toLinearMap
    (by
      intro first second hEqual
      simpa using congrArg
        programPT06FullPhysicalGaugeValueProjection hEqual)

/-- Four fixed-frame covectors representing the gradients of the two U(1)
ghost components in each of the two physical sectors. -/
abbrev ProgramPT06PairedAbelianGhostGradientFiber4D := GaugeValueFiber

/-- Gate895's carrier, enlarged by the four Abelian ghost gradients. -/
abbrev ProgramPT06FullPhysicalGaugeGradientFiniteBVFiber4D :=
  PhysicalValueFiber ×
    (ProgramPT06PairedAbelianGhostGradientFiber4D × FiniteMetricBVPhase)

private abbrev ExtendedFiber :=
  ProgramPT06FullPhysicalGaugeGradientFiniteBVFiber4D

private def programPT06FullPhysicalGaugeGradientProjection :
    ExtendedFiber →L[Real] ProgramPT06PairedAbelianGhostGradientFiber4D :=
  (ContinuousLinearMap.fst Real
      ProgramPT06PairedAbelianGhostGradientFiber4D FiniteMetricBVPhase).comp
    (ContinuousLinearMap.snd Real PhysicalValueFiber
      (ProgramPT06PairedAbelianGhostGradientFiber4D × FiniteMetricBVPhase))

private def programPT06FullPhysicalGaugeGradientBVProjection :
    ExtendedFiber →L[Real] FiniteMetricBVPhase :=
  (ContinuousLinearMap.snd Real
      ProgramPT06PairedAbelianGhostGradientFiber4D FiniteMetricBVPhase).comp
    (ContinuousLinearMap.snd Real PhysicalValueFiber
      (ProgramPT06PairedAbelianGhostGradientFiber4D × FiniteMetricBVPhase))

/-- Linear BRST/BV differential
`s(physical, dc, metricBV) = (dc in gauge slots, 0, s_metricBV)`. -/
def programPT06FullPhysicalGaugeGradientContinuousBRST :
    ExtendedFiber →L[Real] ExtendedFiber :=
  (programPT06FullPhysicalGaugeValueInclusion.comp
      programPT06FullPhysicalGaugeGradientProjection).prod
    ((0 : ExtendedFiber →L[Real]
        ProgramPT06PairedAbelianGhostGradientFiber4D).prod
      (programPT06FiniteMetricBVContinuousBRST.comp
        programPT06FullPhysicalGaugeGradientBVProjection))

@[simp] theorem programPT06FullPhysicalGaugeGradientContinuousBRST_apply
    (state : ExtendedFiber) :
    programPT06FullPhysicalGaugeGradientContinuousBRST state =
      (programPT06FullPhysicalGaugeValueInclusion state.2.1,
        (0, programPT06FiniteMetricBVContinuousBRST state.2.2)) :=
  rfl

/-- Every nonzero ghost gradient produces a nonzero variation of the actual
physical gauge slots. -/
theorem programPT06FullPhysicalGaugeGradientContinuousBRST_nonzero_on
    (ghostGradient : ProgramPT06PairedAbelianGhostGradientFiber4D)
    (hGhostGradient : ghostGradient ≠ 0) :
    programPT06FullPhysicalGaugeGradientContinuousBRST
        (0, (ghostGradient, 0)) ≠ 0 := by
  intro hZero
  apply hGhostGradient
  simpa using congrArg
    (fun state : ExtendedFiber =>
      programPT06FullPhysicalGaugeValueProjection state.1) hZero

theorem programPT06FullPhysicalGaugeGradientContinuousBRST_square_zero
    (state : ExtendedFiber) :
    programPT06FullPhysicalGaugeGradientContinuousBRST
        (programPT06FullPhysicalGaugeGradientContinuousBRST state) = 0 := by
  apply Prod.ext
  · simp
  · apply Prod.ext
    · rfl
    · simpa [programPT06FiniteMetricBVContinuousBRST] using
        finiteMetricBVBRST_square_zero state.2.2

/-- Gate895 embeds as the zero-gradient subcomplex. -/
def programPT06FullPhysicalFiniteBVToGaugeGradientInclusion :
    ProgramPT06FullPhysicalFiniteBVFiber4D →L[Real] ExtendedFiber :=
  (ContinuousLinearMap.fst Real PhysicalValueFiber FiniteMetricBVPhase).prod
    ((0 : ProgramPT06FullPhysicalFiniteBVFiber4D →L[Real]
        ProgramPT06PairedAbelianGhostGradientFiber4D).prod
      (ContinuousLinearMap.snd Real PhysicalValueFiber FiniteMetricBVPhase))

theorem programPT06FullPhysicalFiniteBVToGaugeGradientInclusion_chainMap
    (state : ProgramPT06FullPhysicalFiniteBVFiber4D) :
    programPT06FullPhysicalGaugeGradientContinuousBRST
        (programPT06FullPhysicalFiniteBVToGaugeGradientInclusion state) =
      programPT06FullPhysicalFiniteBVToGaugeGradientInclusion
        (programPT06FullPhysicalFiniteBVContinuousBRST state) := by
  simp [programPT06FullPhysicalGaugeGradientContinuousBRST,
    programPT06FullPhysicalGaugeGradientProjection,
    programPT06FullPhysicalGaugeGradientBVProjection,
    programPT06FullPhysicalGaugeValueInclusion,
    programPT06FullPhysicalFiniteBVToGaugeGradientInclusion,
    programPT06FullPhysicalFiniteBVContinuousBRST]

/-- Square-zero fiber datum for the generic affine T06 construction. -/
def programPT06FullPhysicalGaugeGradientSquareZeroDifferential :
    ProgramPT06SquareZeroContinuousFiberDifferential4D
      (Fiber := ExtendedFiber) where
  differential := programPT06FullPhysicalGaugeGradientContinuousBRST
  square_zero :=
    programPT06FullPhysicalGaugeGradientContinuousBRST_square_zero

/-- Gate875 jets with complete physical values, four Abelian ghost gradients,
and the finite metric-BV phase. -/
abbrev ProgramPT06FullPhysicalGaugeGradientSpatialJet4D (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet ExtendedFiber order

/-- Coefficientwise prolongation to every order of the Gate875 tower. -/
def programPT06FullPhysicalGaugeGradientJetBRST (order : Nat) :
    ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order →L[Real]
      ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order :=
  programPT06ContinuousFiberDifferentialJetProlongation
    programPT06FullPhysicalGaugeGradientSquareZeroDifferential order

@[simp] theorem programPT06FullPhysicalGaugeGradientJetBRST_apply
    (order : Nat)
    (jet : ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06FullPhysicalGaugeGradientJetBRST order jet index =
      programPT06FullPhysicalGaugeGradientContinuousBRST (jet index) :=
  rfl

theorem programPT06FullPhysicalGaugeGradientJetBRST_square_zero
    (order : Nat)
    (jet : ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order) :
    programPT06FullPhysicalGaugeGradientJetBRST order
        (programPT06FullPhysicalGaugeGradientJetBRST order jet) = 0 :=
  programPT06ContinuousFiberDifferentialJetProlongation_square_zero
    programPT06FullPhysicalGaugeGradientSquareZeroDifferential order jet

theorem programPT06FullPhysicalGaugeGradientJetBRST_commutes_truncation
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : ProgramPT06FullPhysicalGaugeGradientSpatialJet4D higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06FullPhysicalGaugeGradientJetBRST higher jet) =
      programPT06FullPhysicalGaugeGradientJetBRST lower
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  rfl

theorem programPT06FullPhysicalGaugeGradientJetBRST_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : ProgramPT06FullPhysicalGaugeGradientSpatialJet4D (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06FullPhysicalGaugeGradientJetBRST (order + 1) jet) =
      programPT06FullPhysicalGaugeGradientJetBRST order
        (throatSpatialTotalDerivative direction jet) :=
  programPT06ContinuousFiberDifferentialJetProlongation_commutes_totalDerivative
    programPT06FullPhysicalGaugeGradientSquareZeroDifferential direction jet

/-- A pure ghost-gradient jet. -/
def programPT06FullPhysicalGaugeGradientGhostJetInclusion (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ProgramPT06PairedAbelianGhostGradientFiber4D order) :
    ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order :=
  fun index => (0, (jet index, 0))

/-- The corresponding jet in the four actual physical gauge slots. -/
def programPT06FullPhysicalGaugeGradientPhysicalGaugeJetInclusion (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ProgramPT06PairedAbelianGhostGradientFiber4D order) :
    ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order :=
  fun index =>
    (programPT06FullPhysicalGaugeValueInclusion (jet index), (0, 0))

/-- On the full Gate875 tower, the ghost-gradient differential lands exactly
in the actual physical gauge-potential slots. -/
@[simp] theorem programPT06FullPhysicalGaugeGradientJetBRST_ghostJet
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ProgramPT06PairedAbelianGhostGradientFiber4D order) :
    programPT06FullPhysicalGaugeGradientJetBRST order
        (programPT06FullPhysicalGaugeGradientGhostJetInclusion order jet) =
      programPT06FullPhysicalGaugeGradientPhysicalGaugeJetInclusion order jet := by
  funext index
  simp [programPT06FullPhysicalGaugeGradientJetBRST,
    programPT06FullPhysicalGaugeGradientGhostJetInclusion,
    programPT06FullPhysicalGaugeGradientPhysicalGaugeJetInclusion,
    programPT06FullPhysicalGaugeGradientSquareZeroDifferential]

end
end P0EFTJanusProgramPT06FullPhysicalGaugeGradientBRSTJetComplex4D
end JanusFormal
