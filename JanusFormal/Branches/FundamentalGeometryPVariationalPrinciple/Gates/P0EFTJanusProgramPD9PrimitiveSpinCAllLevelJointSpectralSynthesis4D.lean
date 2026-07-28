import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D

/-!
# All-level joint spectral synthesis for the primitive SpinC packet

The fixed-level joint Fourier theorem is strengthened here to allow the
positive sphere level to depend on the sector/circle-mode label.  This is the
exact collision block needed before distinct squared-Dirac eigenvalues are
separated.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D

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
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
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
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
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

local instance jointSpectralPrimitiveSpinCComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance jointSpectralPrimitiveSpinCComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-- A positive sphere level assigned independently to each joint Fourier
label. -/
abbrev PrimitiveSpinCJointPositiveLevelAssignment :=
  PrimitiveSpinCJointNormalFourierLabel → Nat

/-- Dependent multiplicity index for a label-dependent positive level. -/
abbrev PrimitiveSpinCJointAssignedPositiveIndex
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment) :=
  Σ label : PrimitiveSpinCJointNormalFourierLabel,
    Fin (primitiveSphereModeDegeneracy (levelAt label + 1))

/-- Null-harmonic family with a potentially different sphere level at each
sector/circle-mode label. -/
def primitiveSpinCJointAssignedPositiveFamily
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (index : PrimitiveSpinCJointAssignedPositiveIndex levelAt) :
    SmoothSection period hPeriod :=
  primitiveSpinCFixedPositiveJointFamily
    period hPeriod (levelAt index.1) (index.1, index.2)

theorem primitiveSpinCJointAssignedPositiveFamily_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (index : PrimitiveSpinCJointAssignedPositiveIndex levelAt)
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCJointAssignedPositiveFamily
          period hPeriod levelAt index) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential
          period index.1.1 index.1.2 time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCJointAssignedPositiveFamily
            period hPeriod levelAt index)) := by
  exact primitiveSpinCFixedPositiveJointFamily_moving_factor
    period hPeriod point hNorth (levelAt index.1)
    (index.1, index.2) time

/-- Complex finite synthesis for a label-dependent positive-level packet. -/
def primitiveSpinCJointAssignedPositiveSynthesis
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment) :
    (PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCJointAssignedPositiveFamily
      period hPeriod levelAt)

/-- Underlying real implementation of the same synthesis. -/
def primitiveSpinCJointAssignedPositiveRealSynthesis
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment) :
    (PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) →ₗ[Real]
      SmoothSection period hPeriod :=
  Finsupp.lsum Real fun index =>
    d9PrimitiveSpinCComplexLineLinearMap
      period hPeriod .positiveQuarter
      (primitiveSpinCJointAssignedPositiveFamily
        period hPeriod levelAt index)

theorem primitiveSpinCJointAssignedPositiveRealSynthesis_eq_synthesis
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) :
    primitiveSpinCJointAssignedPositiveRealSynthesis
        period hPeriod levelAt coefficients =
      primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt coefficients := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCJointAssignedPositiveRealSynthesis,
        primitiveSpinCJointAssignedPositiveSynthesis]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, inductionHypothesis]
      simp [primitiveSpinCJointAssignedPositiveRealSynthesis,
        primitiveSpinCJointAssignedPositiveSynthesis,
        primitiveSpinCComplex_smul,
        d9PrimitiveSpinCComplexLineLinearMap_apply,
        d9PrimitiveSpinCComplexScalarSection_eq_re_add_im]

def primitiveSpinCJointAssignedLocalFourierCoefficientBlock
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCJointAssignedPositiveIndex levelAt) :
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
          (primitiveSpinCJointAssignedPositiveFamily
            period hPeriod levelAt index)))).toLinearMap)

def primitiveSpinCJointAssignedLocalFourierCoefficients
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    (PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) →ₗ[Real]
      (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) :=
  Finsupp.lsum Real fun index =>
    primitiveSpinCJointAssignedLocalFourierCoefficientBlock
      period hPeriod point levelAt component coordinate index

@[simp]
theorem primitiveSpinCJointAssignedLocalFourierCoefficients_single
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCJointAssignedPositiveIndex levelAt)
    (coefficient : Complex) :
    primitiveSpinCJointAssignedLocalFourierCoefficients
        period hPeriod point levelAt component coordinate
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
              (primitiveSpinCJointAssignedPositiveFamily
                period hPeriod levelAt index))) := by
  rw [primitiveSpinCJointAssignedLocalFourierCoefficients,
    Finsupp.lsum_single]
  rfl

theorem primitiveSpinCJointAssignedLocalFourierCoefficients_apply
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel) :
    primitiveSpinCJointAssignedLocalFourierCoefficients
        period hPeriod point levelAt component coordinate coefficients label =
      ∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
        coefficients ⟨label, multiplicity⟩ *
          primitiveSpinCJointDoubledFiberComplexCoordinate
            component coordinate
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCNullPacketMovingWitnessIndex
                period hPeriod point 0)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0)
              (primitiveSpinCJointAssignedPositiveFamily
                period hPeriod levelAt ⟨label, multiplicity⟩)) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCJointAssignedLocalFourierCoefficients]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [inductionHypothesis]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib,
        primitiveSpinCJointAssignedLocalFourierCoefficients_single]
      rcases index with ⟨indexLabel, indexMultiplicity⟩
      by_cases hLabel : indexLabel = label
      · subst label
        simp [Finsupp.single_apply]
      · simp [hLabel]

/-- One moving local coordinate of the assigned-level synthesis. -/
def primitiveSpinCJointAssignedMovingCoordinate
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    (PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) →ₗ[Real]
      Complex :=
  (primitiveSpinCJointDoubledFiberComplexCoordinate
      component coordinate).comp
    ((primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)).comp
      (primitiveSpinCJointAssignedPositiveRealSynthesis
        period hPeriod levelAt))

theorem primitiveSpinCJointAssignedMovingCoordinate_single
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real)
    (index : PrimitiveSpinCJointAssignedPositiveIndex levelAt)
    (coefficient : Complex) :
    primitiveSpinCJointAssignedMovingCoordinate
        period hPeriod point levelAt component coordinate time
        (Finsupp.single index coefficient) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCJointAssignedLocalFourierCoefficients
          period hPeriod point levelAt component coordinate
          (Finsupp.single index coefficient)) := by
  simp only [primitiveSpinCJointAssignedMovingCoordinate,
    LinearMap.comp_apply, primitiveSpinCJointAssignedPositiveRealSynthesis,
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
      (primitiveSpinCJointAssignedPositiveFamily
        period hPeriod levelAt index)
      coefficient,
    primitiveSpinCJointAssignedPositiveFamily_moving_factor
      period hPeriod point hNorth levelAt index time,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCJointAssignedLocalFourierCoefficients_single,
    primitiveSpinCJointNormalFourierPacketLinearMap_single]
  ring

theorem primitiveSpinCJointAssignedMovingCoordinate_eq_fourier
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    primitiveSpinCJointAssignedMovingCoordinate
        period hPeriod point levelAt component coordinate time =
      (primitiveSpinCJointNormalFourierPacketLinearMap period time).comp
        (primitiveSpinCJointAssignedLocalFourierCoefficients
          period hPeriod point levelAt component coordinate) := by
  apply Finsupp.lhom_ext
  intro index coefficient
  simp only [LinearMap.comp_apply]
  exact primitiveSpinCJointAssignedMovingCoordinate_single
    period hPeriod point hNorth levelAt component coordinate time
    index coefficient

theorem primitiveSpinCJointAssignedLocalFourierCoefficients_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt coefficients = 0) :
    primitiveSpinCJointAssignedLocalFourierCoefficients
        period hPeriod point levelAt component coordinate coefficients = 0 := by
  apply
    (primitiveSpinCJointNormalFourierPacketFunctionLinearMap_injective
      period hPeriod)
  funext time
  change
    primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCJointAssignedLocalFourierCoefficients
          period hPeriod point levelAt component coordinate coefficients) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time 0
  rw [map_zero, ← LinearMap.comp_apply,
    ← primitiveSpinCJointAssignedMovingCoordinate_eq_fourier
      period hPeriod point hNorth levelAt component coordinate time]
  simp only [primitiveSpinCJointAssignedMovingCoordinate,
    LinearMap.comp_apply,
    primitiveSpinCJointAssignedPositiveRealSynthesis_eq_synthesis,
    hSynthesis, map_zero]

/-- Time-zero local fiber sum belonging to one assigned sector/mode block. -/
def primitiveSpinCJointAssignedLocalModeFiber
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex) :
    D9DoubledMatterFiber :=
  ∑ multiplicity :
      Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
    d9PrimitiveSpinCComplexActionCLM
      (coefficients ⟨label, multiplicity⟩)
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point 0)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0)
        (primitiveSpinCJointAssignedPositiveFamily
          period hPeriod levelAt ⟨label, multiplicity⟩))

theorem primitiveSpinCJointAssignedLocalModeFiber_coordinate
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    primitiveSpinCJointDoubledFiberComplexCoordinate component coordinate
        (primitiveSpinCJointAssignedLocalModeFiber
          period hPeriod point levelAt label coefficients) =
      primitiveSpinCJointAssignedLocalFourierCoefficients
        period hPeriod point levelAt component coordinate
        coefficients label := by
  rw [primitiveSpinCJointAssignedLocalModeFiber, map_sum,
    primitiveSpinCJointAssignedLocalFourierCoefficients_apply]
  apply Finset.sum_congr rfl
  intro multiplicity _
  exact primitiveSpinCJointDoubledFiberComplexCoordinate_action
    component coordinate _ _

theorem primitiveSpinCJointAssignedLocalModeFiber_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt coefficients = 0) :
    primitiveSpinCJointAssignedLocalModeFiber
        period hPeriod point levelAt label coefficients = 0 := by
  apply primitiveSpinCJointDoubledFiber_eq_zero_of_coordinates
  intro component coordinate
  rw [primitiveSpinCJointAssignedLocalModeFiber_coordinate]
  have hCoefficients :=
    primitiveSpinCJointAssignedLocalFourierCoefficients_eq_zero
      period hPeriod point hNorth levelAt component coordinate
      coefficients hSynthesis
  exact DFunLike.congr_fun hCoefficients label

/-- The separated assigned block satisfies the scalar null-harmonic relation
at the positive level attached to its Fourier label. -/
theorem primitiveSpinCJointAssignedLocalMode_scalar_relation
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hCoordinate : 0 < monopoleSphereCoordinate point 0)
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt coefficients = 0) :
    ∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
      coefficients ⟨label, multiplicity⟩ *
        primitiveSpinCNullSphereScalar
          (primitiveSpinCNullGeometricParameter
            (levelAt label) multiplicity) point ^ (levelAt label + 1) = 0 := by
  have hFiber :=
    primitiveSpinCJointAssignedLocalModeFiber_eq_zero
      period hPeriod point hNorth levelAt label coefficients hSynthesis
  have hLocal := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap label.1)
    hFiber
  rw [primitiveSpinCJointAssignedLocalModeFiber,
    map_sum, map_zero] at hLocal
  simp_rw [
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction
  ] at hLocal
  change
    (∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
      coefficients ⟨label, multiplicity⟩ *
        primitiveSpinCNullPacketLocalCoefficientLinearMap
          period hPeriod point label.1
          (primitiveSpinCJointAssignedPositiveFamily
            period hPeriod levelAt ⟨label, multiplicity⟩)) = 0 at hLocal
  simp_rw [primitiveSpinCJointAssignedPositiveFamily,
    primitiveSpinCFixedPositiveJointFamily,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed,
    primitiveSpinCNullPacketLocalCoefficient_powerSection
      period hPeriod point hNorth] at hLocal
  have hFactored :
      (∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
        coefficients ⟨label, multiplicity⟩ *
          primitiveSpinCNullSphereScalar
            (primitiveSpinCNullGeometricParameter
              (levelAt label) multiplicity) point ^ (levelAt label + 1)) *
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

/-- Every coefficient in a label-dependent positive-level synthesis vanishes
when the synthesized smooth section does. -/
theorem primitiveSpinCJointAssignedPositive_coefficient_eq_zero
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment)
    (coefficients :
      PrimitiveSpinCJointAssignedPositiveIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt coefficients = 0)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (levelAt label + 1))) :
    coefficients ⟨label, multiplicity⟩ = 0 := by
  classical
  let reindex :
      Fin (primitiveSphereModeDegeneracy (levelAt label + 1)) ≃
        Fin (2 * (levelAt label + 1) + 1) :=
    finCongr
      (primitiveSpinCSolidPacket_degeneracy_eq (levelAt label + 1))
  let solidCoefficients :
      Fin (2 * (levelAt label + 1) + 1) → Complex :=
    fun basis => coefficients ⟨label, reindex.symm basis⟩
  have hSolid :=
    primitiveSpinCNullHarmonicSmoothPacket_coefficients_eq_zero_of_scalar_relation
      (levelAt label + 1) solidCoefficients
      (fun point hNorth hCoordinate => by
        have hPhysical :=
          primitiveSpinCJointAssignedLocalMode_scalar_relation
            period hPeriod point hNorth hCoordinate levelAt label
            coefficients hSynthesis
        calc
          (∑ basis : Fin (2 * (levelAt label + 1) + 1),
              solidCoefficients basis *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (levelAt label + 1) basis)
                  point ^ (levelAt label + 1)) =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
              solidCoefficients (reindex physical) *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (levelAt label + 1) (reindex physical))
                  point ^ (levelAt label + 1) := by
              symm
              exact reindex.sum_comp
                (fun basis : Fin (2 * (levelAt label + 1) + 1) =>
                  solidCoefficients basis *
                    primitiveSpinCNullSphereScalar
                      (primitiveSpinCSolidPacketParameter
                        (levelAt label + 1) basis)
                      point ^ (levelAt label + 1))
          _ =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (levelAt label + 1)),
              coefficients ⟨label, physical⟩ *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCNullGeometricParameter
                    (levelAt label) physical)
                  point ^ (levelAt label + 1) := by
              apply Finset.sum_congr rfl
              intro physical _
              simp [solidCoefficients, reindex,
                primitiveSpinCNullGeometricParameter]
          _ = 0 := hPhysical)
  have hAt := hSolid (reindex multiplicity)
  simpa [solidCoefficients, reindex] using hAt

/-- Finite synthesis is faithful for every label-dependent assignment of
positive sphere levels. -/
theorem primitiveSpinCJointAssignedPositiveSynthesis_injective
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment) :
    Function.Injective
      (primitiveSpinCJointAssignedPositiveSynthesis
        period hPeriod levelAt) := by
  intro first second hEqual
  have hKernel :
      primitiveSpinCJointAssignedPositiveSynthesis
          period hPeriod levelAt (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  apply sub_eq_zero.mp
  apply Finsupp.ext
  rintro ⟨label, multiplicity⟩
  exact primitiveSpinCJointAssignedPositive_coefficient_eq_zero
    period hPeriod levelAt (first - second) hKernel label multiplicity

theorem primitiveSpinCJointAssignedPositiveFamily_linearIndependent
    (levelAt : PrimitiveSpinCJointPositiveLevelAssignment) :
    LinearIndependent Complex
      (primitiveSpinCJointAssignedPositiveFamily
        period hPeriod levelAt) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  exact primitiveSpinCJointAssignedPositiveSynthesis_injective
    period hPeriod levelAt

/-! ## Simultaneous synthesis over every positive level and Fourier label -/

/-- Complete positive-level label: sector, circle mode, sphere level and
multiplicity. -/
abbrev PrimitiveSpinCAllPositiveJointIndex :=
  Σ label : PrimitiveSpinCJointNormalFourierLabel,
    PrimitiveSpinCAllPositiveNullHarmonicIndex

def primitiveSpinCAllPositiveJointFamily
    (index : PrimitiveSpinCAllPositiveJointIndex) :
    SmoothSection period hPeriod :=
  primitiveSpinCAllPositiveNullHarmonicFamily
    period hPeriod index.1.1 index.1.2 index.2

def primitiveSpinCAllPositiveJointSquaredEigenvalue
    (index : PrimitiveSpinCAllPositiveJointIndex) : Complex :=
  primitiveSpinCAllPositiveNullHarmonicSquaredEigenvalue
    period index.2.1 index.1.1 index.1.2

theorem primitiveSpinCAllPositiveJointFamily_mem_eigenspace
    (index : PrimitiveSpinCAllPositiveJointIndex) :
    primitiveSpinCAllPositiveJointFamily period hPeriod index ∈
      Module.End.eigenspace
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap
          period hPeriod)
        (primitiveSpinCAllPositiveJointSquaredEigenvalue period index) := by
  exact primitiveSpinCAllPositiveNullHarmonicFamily_mem_eigenspace
    period hPeriod index.2.1 index.2.2 index.1.1 index.1.2

/-- At a fixed squared-Dirac eigenvalue, choose the unique positive sphere
level when it exists for a given Fourier label. -/
def primitiveSpinCJointEigenvalueCollisionLevel
    (eigenvalue : Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel) : Nat := by
  classical
  exact if hExists :
      ∃ positiveLevel,
        primitiveSpinCAllPositiveNullHarmonicSquaredEigenvalue
          period positiveLevel label.1 label.2 = eigenvalue then
    Classical.choose hExists
  else
    0

theorem primitiveSpinCJointEigenvalueCollisionLevel_eq
    (eigenvalue : Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (positiveLevel : Nat)
    (hEigenvalue :
      primitiveSpinCAllPositiveNullHarmonicSquaredEigenvalue
        period positiveLevel label.1 label.2 = eigenvalue) :
    primitiveSpinCJointEigenvalueCollisionLevel
        period eigenvalue label = positiveLevel := by
  unfold primitiveSpinCJointEigenvalueCollisionLevel
  split
  next hExists =>
    apply
      (primitiveSpinCAllPositiveNullHarmonicSquaredEigenvalue_injective
        period label.1 label.2)
    exact (Classical.choose_spec hExists).trans hEigenvalue.symm
  next hMissing =>
    exact False.elim (hMissing ⟨positiveLevel, hEigenvalue⟩)

/-- Embed one fixed-eigenvalue collision fiber into the corresponding
label-dependent level packet. -/
def primitiveSpinCJointEigenvalueCollisionEmbedding
    (eigenvalue : Complex) :
    { index : PrimitiveSpinCAllPositiveJointIndex //
        primitiveSpinCAllPositiveJointSquaredEigenvalue period index =
          eigenvalue } →
      PrimitiveSpinCJointAssignedPositiveIndex
        (primitiveSpinCJointEigenvalueCollisionLevel period eigenvalue) :=
  fun index =>
    ⟨index.1.1,
      Fin.cast
        (congrArg
          (fun positiveLevel =>
            primitiveSphereModeDegeneracy (positiveLevel + 1))
          (primitiveSpinCJointEigenvalueCollisionLevel_eq
            period eigenvalue index.1.1 index.1.2.1 index.2).symm)
        index.1.2.2⟩

theorem primitiveSpinCJointEigenvalueCollisionEmbedding_injective
    (eigenvalue : Complex) :
    Function.Injective
      (primitiveSpinCJointEigenvalueCollisionEmbedding
        period eigenvalue) := by
  rintro ⟨⟨firstLabel, ⟨firstLevel, firstMultiplicity⟩⟩, firstEigen⟩
    ⟨⟨secondLabel, ⟨secondLevel, secondMultiplicity⟩⟩, secondEigen⟩
    hEqual
  have hLabel : firstLabel = secondLabel :=
    congrArg Sigma.fst hEqual
  cases hLabel
  have hFirstLevel :=
    primitiveSpinCJointEigenvalueCollisionLevel_eq
      period eigenvalue firstLabel firstLevel firstEigen
  have hSecondLevel :=
    primitiveSpinCJointEigenvalueCollisionLevel_eq
      period eigenvalue firstLabel secondLevel secondEigen
  cases hFirstLevel
  cases hSecondLevel
  have hMultiplicity :
      firstMultiplicity = secondMultiplicity := by
    simpa [primitiveSpinCJointEigenvalueCollisionEmbedding] using hEqual
  cases hMultiplicity
  rfl

theorem primitiveSpinCJointAssignedFamily_collisionEmbedding
    (eigenvalue : Complex)
    (index :
      { index : PrimitiveSpinCAllPositiveJointIndex //
        primitiveSpinCAllPositiveJointSquaredEigenvalue period index =
          eigenvalue }) :
    primitiveSpinCJointAssignedPositiveFamily
        period hPeriod
        (primitiveSpinCJointEigenvalueCollisionLevel period eigenvalue)
        (primitiveSpinCJointEigenvalueCollisionEmbedding
          period eigenvalue index) =
      primitiveSpinCAllPositiveJointFamily
        period hPeriod index.1 := by
  rcases index with
    ⟨⟨label, ⟨positiveLevel, multiplicity⟩⟩, hEigenvalue⟩
  have hLevel :=
    primitiveSpinCJointEigenvalueCollisionLevel_eq
      period eigenvalue label positiveLevel hEigenvalue
  cases hLevel
  simp [primitiveSpinCJointAssignedPositiveFamily,
    primitiveSpinCFixedPositiveJointFamily,
    primitiveSpinCAllPositiveJointFamily,
    primitiveSpinCAllPositiveNullHarmonicFamily,
    primitiveSpinCJointEigenvalueCollisionEmbedding]

/-- Every collision fiber of the squared-Dirac eigenvalue remains jointly
independent across all sectors and circle modes. -/
theorem primitiveSpinCAllPositiveJointFamily_collision_linearIndependent
    (eigenvalue : Complex) :
    LinearIndependent Complex
      (fun index :
          { index : PrimitiveSpinCAllPositiveJointIndex //
            primitiveSpinCAllPositiveJointSquaredEigenvalue period index =
              eigenvalue } =>
        primitiveSpinCAllPositiveJointFamily
          period hPeriod index.1) := by
  have hAssigned :=
    (primitiveSpinCJointAssignedPositiveFamily_linearIndependent
      period hPeriod
      (primitiveSpinCJointEigenvalueCollisionLevel period eigenvalue)).comp
      (primitiveSpinCJointEigenvalueCollisionEmbedding period eigenvalue)
      (primitiveSpinCJointEigenvalueCollisionEmbedding_injective
        period eigenvalue)
  simpa only [Function.comp_def,
    primitiveSpinCJointAssignedFamily_collisionEmbedding] using hAssigned

/-- The null-harmonic family is jointly independent simultaneously across
every positive sphere level, both sectors, all circle modes and every
multiplicity. -/
theorem primitiveSpinCAllPositiveJointFamily_linearIndependent :
    LinearIndependent Complex
      (primitiveSpinCAllPositiveJointFamily period hPeriod) := by
  classical
  let collisionPacket :
      (eigenvalue : Complex) →
        { index : PrimitiveSpinCAllPositiveJointIndex //
          primitiveSpinCAllPositiveJointSquaredEigenvalue period index =
            eigenvalue } →
          SmoothSection period hPeriod :=
    fun _ index =>
      primitiveSpinCAllPositiveJointFamily period hPeriod index.1
  have hEigenspaces :
      iSupIndep
        (fun eigenvalue =>
          Module.End.eigenspace
            (primitiveSpinCGeometricDiracSquaredComplexLinearMap
              period hPeriod)
            eigenvalue) :=
    Module.End.eigenspaces_iSupIndep
      (primitiveSpinCGeometricDiracSquaredComplexLinearMap
        period hPeriod)
  have hCombined :
      LinearIndependent Complex
        (fun index :
            Σ eigenvalue : Complex,
              { mode : PrimitiveSpinCAllPositiveJointIndex //
                primitiveSpinCAllPositiveJointSquaredEigenvalue period mode =
                  eigenvalue } =>
          collisionPacket index.1 index.2) := by
    apply linearIndependent_iUnion_finite
    · intro eigenvalue
      exact
        primitiveSpinCAllPositiveJointFamily_collision_linearIndependent
          period hPeriod eigenvalue
    · intro eigenvalue eigenvalues _ hNotMem
      apply (hEigenspaces.disjoint_biSup hNotMem).mono
      · rw [Submodule.span_le]
        rintro state ⟨index, rfl⟩
        change
          primitiveSpinCAllPositiveJointFamily period hPeriod index.1 ∈
            Module.End.eigenspace
              (primitiveSpinCGeometricDiracSquaredComplexLinearMap
                period hPeriod) eigenvalue
        simpa only [index.2] using
          (primitiveSpinCAllPositiveJointFamily_mem_eigenspace
            period hPeriod index.1)
      · refine iSup₂_le fun otherEigenvalue hOther => ?_
        rw [Submodule.span_le]
        rintro state ⟨index, rfl⟩
        apply Submodule.mem_iSup_of_mem otherEigenvalue
        apply Submodule.mem_iSup_of_mem hOther
        change
          primitiveSpinCAllPositiveJointFamily period hPeriod index.1 ∈
            Module.End.eigenspace
              (primitiveSpinCGeometricDiracSquaredComplexLinearMap
                period hPeriod) otherEigenvalue
        simpa only [index.2] using
          (primitiveSpinCAllPositiveJointFamily_mem_eigenspace
            period hPeriod index.1)
  let classify :
      PrimitiveSpinCAllPositiveJointIndex →
        Σ eigenvalue : Complex,
          { mode : PrimitiveSpinCAllPositiveJointIndex //
            primitiveSpinCAllPositiveJointSquaredEigenvalue period mode =
              eigenvalue } :=
    fun index =>
      ⟨primitiveSpinCAllPositiveJointSquaredEigenvalue period index,
        ⟨index, rfl⟩⟩
  have hClassify : Function.Injective classify := by
    intro first second hEqual
    exact congrArg (fun current => current.2.1) hEqual
  have hAll := hCombined.comp classify hClassify
  simpa only [collisionPacket, classify, Function.comp_def] using hAll

/-- One finite-support synthesis over every positive geometric label. -/
def primitiveSpinCAllPositiveJointSynthesis :
    (PrimitiveSpinCAllPositiveJointIndex →₀ Complex) →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCAllPositiveJointFamily period hPeriod)

/-- The fully joint all-positive-level synthesis loses no coefficient. -/
theorem primitiveSpinCAllPositiveJointSynthesis_injective :
    Function.Injective
      (primitiveSpinCAllPositiveJointSynthesis period hPeriod) :=
  (primitiveSpinCAllPositiveJointFamily_linearIndependent
    period hPeriod).finsuppLinearCombination_injective

@[simp]
theorem primitiveSpinCAllPositiveJointSynthesis_single
    (index : PrimitiveSpinCAllPositiveJointIndex)
    (coefficient : Complex) :
    primitiveSpinCAllPositiveJointSynthesis period hPeriod
        (Finsupp.single index coefficient) =
      coefficient •
        primitiveSpinCAllPositiveJointFamily period hPeriod index := by
  simp [primitiveSpinCAllPositiveJointSynthesis]

def primitiveSpinCAllPositiveJointSquaredCoefficientBlock
    (index : PrimitiveSpinCAllPositiveJointIndex) :
    Complex →ₗ[Complex]
      (PrimitiveSpinCAllPositiveJointIndex →₀ Complex) :=
  (Finsupp.lsingle index).comp
    (primitiveSpinCAllPositiveJointSquaredEigenvalue period index •
      (LinearMap.id : Complex →ₗ[Complex] Complex))

/-- Exact squared-Dirac diagonal on the fully joint finite coefficient
space. -/
def primitiveSpinCAllPositiveJointSquaredCoefficientOperator :
    (PrimitiveSpinCAllPositiveJointIndex →₀ Complex) →ₗ[Complex]
      (PrimitiveSpinCAllPositiveJointIndex →₀ Complex) :=
  Finsupp.lsum Complex fun index =>
    primitiveSpinCAllPositiveJointSquaredCoefficientBlock period index

@[simp]
theorem primitiveSpinCAllPositiveJointSquaredCoefficientOperator_single
    (index : PrimitiveSpinCAllPositiveJointIndex)
    (coefficient : Complex) :
    primitiveSpinCAllPositiveJointSquaredCoefficientOperator period
        (Finsupp.single index coefficient) =
      primitiveSpinCAllPositiveJointSquaredEigenvalue period index •
        Finsupp.single index coefficient := by
  simp [primitiveSpinCAllPositiveJointSquaredCoefficientOperator,
    primitiveSpinCAllPositiveJointSquaredCoefficientBlock]

theorem primitiveSpinCAllPositiveJointFamily_dirac_sq
    (index : PrimitiveSpinCAllPositiveJointIndex) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCAllPositiveJointFamily period hPeriod index) =
      primitiveSpinCAllPositiveJointSquaredEigenvalue period index •
        primitiveSpinCAllPositiveJointFamily period hPeriod index :=
  Module.End.mem_eigenspace_iff.mp
    (primitiveSpinCAllPositiveJointFamily_mem_eigenspace
      period hPeriod index)

/-- The genuine geometric squared Dirac operator intertwines the fully joint
finite synthesis with its exact coefficient diagonal. -/
theorem primitiveSpinCAllPositiveJointSynthesis_intertwines_dirac_sq
    (coefficients :
      PrimitiveSpinCAllPositiveJointIndex →₀ Complex) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCAllPositiveJointSynthesis
          period hPeriod coefficients) =
      primitiveSpinCAllPositiveJointSynthesis period hPeriod
        (primitiveSpinCAllPositiveJointSquaredCoefficientOperator
          period coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      change
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod 0 = 0
      exact map_zero
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap
          period hPeriod)
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add,
        primitiveSpinCAllPositiveJointSynthesis_single,
        map_smul,
        primitiveSpinCAllPositiveJointFamily_dirac_sq,
        inductionHypothesis,
        primitiveSpinCAllPositiveJointSquaredCoefficientOperator_single,
        map_add, map_smul,
        primitiveSpinCAllPositiveJointSynthesis_single]
      rw [smul_smul, smul_smul, mul_comm]

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D
end JanusFormal
