import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D

/-!
# Full all-level primitive SpinC spectral synthesis

This file adjoins the Hopf sphere-level-zero tower to the already joint
positive-level synthesis.  The key collision packet allows one arbitrary
nonnegative sphere level for each sector/circle-mode label.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators Manifold ContDiff
open P0EFTJanusGlobalSeparatedDiracModel
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
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
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

local instance fullSpectralPrimitiveSpinCComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance fullSpectralPrimitiveSpinCComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-! ## One arbitrary nonnegative sphere level at each Fourier label -/

/-- Null-curve parameter for every sphere level, including degree zero. -/
def primitiveSpinCFullLevelNullGeometricParameter
    (level : Nat)
    (multiplicity : Fin (primitiveSphereModeDegeneracy level)) : Complex :=
  primitiveSpinCSolidPacketParameter level
    (Fin.cast (primitiveSpinCSolidPacket_degeneracy_eq level) multiplicity)

/-- A nonnegative sphere level assigned independently to every joint Fourier
label. -/
abbrev PrimitiveSpinCJointFullLevelAssignment :=
  PrimitiveSpinCJointNormalFourierLabel → Nat

/-- Dependent multiplicity index for a label-dependent full sphere level. -/
abbrev PrimitiveSpinCJointAssignedFullIndex
    (levelAt : PrimitiveSpinCJointFullLevelAssignment) :=
  Σ label : PrimitiveSpinCJointNormalFourierLabel,
    Fin (primitiveSphereModeDegeneracy (levelAt label))

/-- Smooth null-power family with a potentially different nonnegative sphere
level at each sector/circle-mode label. -/
def primitiveSpinCJointAssignedFullFamily
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (index : PrimitiveSpinCJointAssignedFullIndex levelAt) :
    SmoothSection period hPeriod :=
  primitiveSpinCNullPowerSection
    period hPeriod
    (primitiveSpinCFullLevelNullGeometricParameter
      (levelAt index.1) index.2)
    index.1.1 index.1.2 (levelAt index.1)

theorem primitiveSpinCJointAssignedFullFamily_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (index : PrimitiveSpinCJointAssignedFullIndex levelAt)
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCJointAssignedFullFamily
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
          (primitiveSpinCJointAssignedFullFamily
            period hPeriod levelAt index)) := by
  exact primitiveSpinCNullPowerLocalCoordinate_moving_factor
    period hPeriod point hNorth
    (primitiveSpinCFullLevelNullGeometricParameter
      (levelAt index.1) index.2)
    index.1.1 index.1.2 (levelAt index.1) time

/-- Complex finite synthesis for a label-dependent full-level packet. -/
def primitiveSpinCJointAssignedFullSynthesis
    (levelAt : PrimitiveSpinCJointFullLevelAssignment) :
    (PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCJointAssignedFullFamily period hPeriod levelAt)

/-- Underlying real implementation of the same synthesis. -/
def primitiveSpinCJointAssignedFullRealSynthesis
    (levelAt : PrimitiveSpinCJointFullLevelAssignment) :
    (PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) →ₗ[Real]
      SmoothSection period hPeriod :=
  Finsupp.lsum Real fun index =>
    d9PrimitiveSpinCComplexLineLinearMap
      period hPeriod .positiveQuarter
      (primitiveSpinCJointAssignedFullFamily
        period hPeriod levelAt index)

theorem primitiveSpinCJointAssignedFullRealSynthesis_eq_synthesis
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) :
    primitiveSpinCJointAssignedFullRealSynthesis
        period hPeriod levelAt coefficients =
      primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt coefficients := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCJointAssignedFullRealSynthesis,
        primitiveSpinCJointAssignedFullSynthesis]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, inductionHypothesis]
      simp [primitiveSpinCJointAssignedFullRealSynthesis,
        primitiveSpinCJointAssignedFullSynthesis,
        primitiveSpinCComplex_smul,
        d9PrimitiveSpinCComplexLineLinearMap_apply,
        d9PrimitiveSpinCComplexScalarSection_eq_re_add_im]

def primitiveSpinCJointAssignedFullLocalFourierCoefficientBlock
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCJointAssignedFullIndex levelAt) :
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
          (primitiveSpinCJointAssignedFullFamily
            period hPeriod levelAt index)))).toLinearMap)

def primitiveSpinCJointAssignedFullLocalFourierCoefficients
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    (PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) →ₗ[Real]
      (PrimitiveSpinCJointNormalFourierLabel →₀ Complex) :=
  Finsupp.lsum Real fun index =>
    primitiveSpinCJointAssignedFullLocalFourierCoefficientBlock
      period hPeriod point levelAt component coordinate index

@[simp]
theorem primitiveSpinCJointAssignedFullLocalFourierCoefficients_single
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (index : PrimitiveSpinCJointAssignedFullIndex levelAt)
    (coefficient : Complex) :
    primitiveSpinCJointAssignedFullLocalFourierCoefficients
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
              (primitiveSpinCJointAssignedFullFamily
                period hPeriod levelAt index))) := by
  rw [primitiveSpinCJointAssignedFullLocalFourierCoefficients,
    Finsupp.lsum_single]
  rfl

theorem primitiveSpinCJointAssignedFullLocalFourierCoefficients_apply
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel) :
    primitiveSpinCJointAssignedFullLocalFourierCoefficients
        period hPeriod point levelAt component coordinate coefficients label =
      ∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (levelAt label)),
        coefficients ⟨label, multiplicity⟩ *
          primitiveSpinCJointDoubledFiberComplexCoordinate
            component coordinate
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCNullPacketMovingWitnessIndex
                period hPeriod point 0)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0)
              (primitiveSpinCJointAssignedFullFamily
                period hPeriod levelAt ⟨label, multiplicity⟩)) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCJointAssignedFullLocalFourierCoefficients]
  | single_add index coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [inductionHypothesis]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib,
        primitiveSpinCJointAssignedFullLocalFourierCoefficients_single]
      rcases index with ⟨indexLabel, indexMultiplicity⟩
      by_cases hLabel : indexLabel = label
      · subst label
        simp [Finsupp.single_apply]
      · simp [hLabel]

def primitiveSpinCJointAssignedFullMovingCoordinate
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    (PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) →ₗ[Real]
      Complex :=
  (primitiveSpinCJointDoubledFiberComplexCoordinate
      component coordinate).comp
    ((primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)).comp
      (primitiveSpinCJointAssignedFullRealSynthesis
        period hPeriod levelAt))

theorem primitiveSpinCJointAssignedFullMovingCoordinate_single
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real)
    (index : PrimitiveSpinCJointAssignedFullIndex levelAt)
    (coefficient : Complex) :
    primitiveSpinCJointAssignedFullMovingCoordinate
        period hPeriod point levelAt component coordinate time
        (Finsupp.single index coefficient) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCJointAssignedFullLocalFourierCoefficients
          period hPeriod point levelAt component coordinate
          (Finsupp.single index coefficient)) := by
  simp only [primitiveSpinCJointAssignedFullMovingCoordinate,
    LinearMap.comp_apply, primitiveSpinCJointAssignedFullRealSynthesis,
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
      (primitiveSpinCJointAssignedFullFamily
        period hPeriod levelAt index)
      coefficient,
    primitiveSpinCJointAssignedFullFamily_moving_factor
      period hPeriod point hNorth levelAt index time,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCJointDoubledFiberComplexCoordinate_action,
    primitiveSpinCJointAssignedFullLocalFourierCoefficients_single,
    primitiveSpinCJointNormalFourierPacketLinearMap_single]
  ring

theorem primitiveSpinCJointAssignedFullMovingCoordinate_eq_fourier
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (time : Real) :
    primitiveSpinCJointAssignedFullMovingCoordinate
        period hPeriod point levelAt component coordinate time =
      (primitiveSpinCJointNormalFourierPacketLinearMap period time).comp
        (primitiveSpinCJointAssignedFullLocalFourierCoefficients
          period hPeriod point levelAt component coordinate) := by
  apply Finsupp.lhom_ext
  intro index coefficient
  simp only [LinearMap.comp_apply]
  exact primitiveSpinCJointAssignedFullMovingCoordinate_single
    period hPeriod point hNorth levelAt component coordinate time
    index coefficient

theorem primitiveSpinCJointAssignedFullLocalFourierCoefficients_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (component : NormalRootChoice) (coordinate : Fin 2)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt coefficients = 0) :
    primitiveSpinCJointAssignedFullLocalFourierCoefficients
        period hPeriod point levelAt component coordinate coefficients = 0 := by
  apply
    (primitiveSpinCJointNormalFourierPacketFunctionLinearMap_injective
      period hPeriod)
  funext time
  change
    primitiveSpinCJointNormalFourierPacketLinearMap period time
        (primitiveSpinCJointAssignedFullLocalFourierCoefficients
          period hPeriod point levelAt component coordinate coefficients) =
      primitiveSpinCJointNormalFourierPacketLinearMap period time 0
  rw [map_zero, ← LinearMap.comp_apply,
    ← primitiveSpinCJointAssignedFullMovingCoordinate_eq_fourier
      period hPeriod point hNorth levelAt component coordinate time]
  simp only [primitiveSpinCJointAssignedFullMovingCoordinate,
    LinearMap.comp_apply,
    primitiveSpinCJointAssignedFullRealSynthesis_eq_synthesis,
    hSynthesis, map_zero]

def primitiveSpinCJointAssignedFullLocalModeFiber
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex) :
    D9DoubledMatterFiber :=
  ∑ multiplicity :
      Fin (primitiveSphereModeDegeneracy (levelAt label)),
    d9PrimitiveSpinCComplexActionCLM
      (coefficients ⟨label, multiplicity⟩)
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point 0)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0)
        (primitiveSpinCJointAssignedFullFamily
          period hPeriod levelAt ⟨label, multiplicity⟩))

theorem primitiveSpinCJointAssignedFullLocalModeFiber_coordinate
    (point : MonopoleSphere)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (component : NormalRootChoice) (coordinate : Fin 2) :
    primitiveSpinCJointDoubledFiberComplexCoordinate component coordinate
        (primitiveSpinCJointAssignedFullLocalModeFiber
          period hPeriod point levelAt label coefficients) =
      primitiveSpinCJointAssignedFullLocalFourierCoefficients
        period hPeriod point levelAt component coordinate
        coefficients label := by
  rw [primitiveSpinCJointAssignedFullLocalModeFiber, map_sum,
    primitiveSpinCJointAssignedFullLocalFourierCoefficients_apply]
  apply Finset.sum_congr rfl
  intro multiplicity _
  exact primitiveSpinCJointDoubledFiberComplexCoordinate_action
    component coordinate _ _

theorem primitiveSpinCJointAssignedFullLocalModeFiber_eq_zero
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt coefficients = 0) :
    primitiveSpinCJointAssignedFullLocalModeFiber
        period hPeriod point levelAt label coefficients = 0 := by
  apply primitiveSpinCJointDoubledFiber_eq_zero_of_coordinates
  intro component coordinate
  rw [primitiveSpinCJointAssignedFullLocalModeFiber_coordinate]
  have hCoefficients :=
    primitiveSpinCJointAssignedFullLocalFourierCoefficients_eq_zero
      period hPeriod point hNorth levelAt component coordinate
      coefficients hSynthesis
  exact DFunLike.congr_fun hCoefficients label

theorem primitiveSpinCJointAssignedFullLocalMode_scalar_relation
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hCoordinate : 0 < monopoleSphereCoordinate point 0)
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt coefficients = 0) :
    ∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (levelAt label)),
      coefficients ⟨label, multiplicity⟩ *
        primitiveSpinCNullSphereScalar
          (primitiveSpinCFullLevelNullGeometricParameter
            (levelAt label) multiplicity) point ^ levelAt label = 0 := by
  have hFiber :=
    primitiveSpinCJointAssignedFullLocalModeFiber_eq_zero
      period hPeriod point hNorth levelAt label coefficients hSynthesis
  have hLocal := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap label.1)
    hFiber
  rw [primitiveSpinCJointAssignedFullLocalModeFiber,
    map_sum, map_zero] at hLocal
  simp_rw [
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction
  ] at hLocal
  change
    (∑ multiplicity :
        Fin (primitiveSphereModeDegeneracy (levelAt label)),
      coefficients ⟨label, multiplicity⟩ *
        primitiveSpinCNullPacketLocalCoefficientLinearMap
          period hPeriod point label.1
          (primitiveSpinCJointAssignedFullFamily
            period hPeriod levelAt ⟨label, multiplicity⟩)) = 0 at hLocal
  simp_rw [primitiveSpinCJointAssignedFullFamily,
    primitiveSpinCNullPacketLocalCoefficient_powerSection
      period hPeriod point hNorth] at hLocal
  have hFactored :
      (∑ multiplicity :
          Fin (primitiveSphereModeDegeneracy (levelAt label)),
        coefficients ⟨label, multiplicity⟩ *
          primitiveSpinCNullSphereScalar
            (primitiveSpinCFullLevelNullGeometricParameter
              (levelAt label) multiplicity) point ^ levelAt label) *
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

theorem primitiveSpinCJointAssignedFull_coefficient_eq_zero
    (levelAt : PrimitiveSpinCJointFullLevelAssignment)
    (coefficients :
      PrimitiveSpinCJointAssignedFullIndex levelAt →₀ Complex)
    (hSynthesis :
      primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt coefficients = 0)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (levelAt label))) :
    coefficients ⟨label, multiplicity⟩ = 0 := by
  classical
  let reindex :
      Fin (primitiveSphereModeDegeneracy (levelAt label)) ≃
        Fin (2 * levelAt label + 1) :=
    finCongr (primitiveSpinCSolidPacket_degeneracy_eq (levelAt label))
  let solidCoefficients :
      Fin (2 * levelAt label + 1) → Complex :=
    fun basis => coefficients ⟨label, reindex.symm basis⟩
  have hSolid :=
    primitiveSpinCNullHarmonicSmoothPacket_coefficients_eq_zero_of_scalar_relation
      (levelAt label) solidCoefficients
      (fun point hNorth hCoordinate => by
        have hPhysical :=
          primitiveSpinCJointAssignedFullLocalMode_scalar_relation
            period hPeriod point hNorth hCoordinate levelAt label
            coefficients hSynthesis
        calc
          (∑ basis : Fin (2 * levelAt label + 1),
              solidCoefficients basis *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (levelAt label) basis)
                  point ^ levelAt label) =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (levelAt label)),
              solidCoefficients (reindex physical) *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCSolidPacketParameter
                    (levelAt label) (reindex physical))
                  point ^ levelAt label := by
              symm
              exact reindex.sum_comp
                (fun basis : Fin (2 * levelAt label + 1) =>
                  solidCoefficients basis *
                    primitiveSpinCNullSphereScalar
                      (primitiveSpinCSolidPacketParameter
                        (levelAt label) basis)
                      point ^ levelAt label)
          _ =
            ∑ physical :
                Fin (primitiveSphereModeDegeneracy (levelAt label)),
              coefficients ⟨label, physical⟩ *
                primitiveSpinCNullSphereScalar
                  (primitiveSpinCFullLevelNullGeometricParameter
                    (levelAt label) physical)
                  point ^ levelAt label := by
              apply Finset.sum_congr rfl
              intro physical _
              simp [solidCoefficients, reindex,
                primitiveSpinCFullLevelNullGeometricParameter]
          _ = 0 := hPhysical)
  have hAt := hSolid (reindex multiplicity)
  simpa [solidCoefficients, reindex] using hAt

/-- Finite synthesis is faithful for every label-dependent assignment of
nonnegative sphere levels. -/
theorem primitiveSpinCJointAssignedFullSynthesis_injective
    (levelAt : PrimitiveSpinCJointFullLevelAssignment) :
    Function.Injective
      (primitiveSpinCJointAssignedFullSynthesis
        period hPeriod levelAt) := by
  intro first second hEqual
  have hKernel :
      primitiveSpinCJointAssignedFullSynthesis
          period hPeriod levelAt (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  apply sub_eq_zero.mp
  apply Finsupp.ext
  rintro ⟨label, multiplicity⟩
  exact primitiveSpinCJointAssignedFull_coefficient_eq_zero
    period hPeriod levelAt (first - second) hKernel label multiplicity

theorem primitiveSpinCJointAssignedFullFamily_linearIndependent
    (levelAt : PrimitiveSpinCJointFullLevelAssignment) :
    LinearIndependent Complex
      (primitiveSpinCJointAssignedFullFamily
        period hPeriod levelAt) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  exact primitiveSpinCJointAssignedFullSynthesis_injective
    period hPeriod levelAt

/-! ## Simultaneous synthesis over the complete zero-plus-positive tower -/

/-- Joint presentation of the complete coefficient label: sector/circle
label followed by the full nonnegative sphere mode. -/
abbrev PrimitiveSpinCAllFullJointIndex :=
  Σ label : PrimitiveSpinCJointNormalFourierLabel,
    PrimitiveSpinCFullSphereMode

/-- Canonical reordering from the joint presentation to the repository's
complete geometric coefficient mode. -/
def primitiveSpinCAllFullJointIndexEquiv :
    PrimitiveSpinCAllFullJointIndex ≃ PrimitiveSpinCGeometricFullMode where
  toFun index := (index.1.1, (index.2, index.1.2))
  invFun mode := ⟨(mode.1, mode.2.2), mode.2.1⟩
  left_inv index := by
    rcases index with ⟨⟨sector, circleMode⟩, ⟨level, multiplicity⟩⟩
    rfl
  right_inv mode := by
    rcases mode with ⟨sector, ⟨⟨level, multiplicity⟩, circleMode⟩⟩
    rfl

/-- One genuine smooth null-power section for every full joint label. -/
def primitiveSpinCAllFullJointFamily
    (index : PrimitiveSpinCAllFullJointIndex) :
    SmoothSection period hPeriod :=
  primitiveSpinCNullPowerSection
    period hPeriod
    (primitiveSpinCFullLevelNullGeometricParameter
      index.2.1 index.2.2)
    index.1.1 index.1.2 index.2.1

/-- The joint family is exactly the pre-existing all-mode smooth geometric
representative after canonical reordering. -/
theorem primitiveSpinCAllFullJointFamily_eq_allMode
    (index : PrimitiveSpinCAllFullJointIndex) :
    primitiveSpinCAllFullJointFamily period hPeriod index =
      primitiveSpinCAllModeNullHarmonicRealSection
        period hPeriod
        (primitiveSpinCAllFullJointIndexEquiv index) := by
  rcases index with
    ⟨⟨sector, circleMode⟩, ⟨level, multiplicity⟩⟩
  cases level with
  | zero =>
      change
        primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode =
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode
      rfl
  | succ positiveLevel =>
      rfl

/-- Exact complex squared-Dirac weight on one full joint label. -/
def primitiveSpinCAllFullJointSquaredEigenvalue
    (index : PrimitiveSpinCAllFullJointIndex) : Complex :=
  ((primitiveSpinCFullSphereEigenvalueSquared index.2.1 +
      normalRootLeviCivitaCorrectedFrequency
        period index.1.1 index.1.2 ^ 2 : Real) : Complex)

theorem primitiveSpinCAllFullJointSquaredEigenvalue_eq_geometric
    (index : PrimitiveSpinCAllFullJointIndex) :
    primitiveSpinCAllFullJointSquaredEigenvalue period index =
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCAllFullJointIndexEquiv index) : Complex) := by
  rcases index with
    ⟨⟨sector, circleMode⟩, ⟨level, multiplicity⟩⟩
  change
    ((primitiveSpinCFullSphereEigenvalueSquared level +
        normalRootLeviCivitaCorrectedFrequency
          period sector circleMode ^ 2 : Real) : Complex) =
      ((primitiveSpinCFullSphereEigenvalueSquared level +
        circleEigenvalue
          (PrimitiveSpinCSpectralData period hPeriod)
          sector circleMode ^ 2 : Real) : Complex)
  rw [normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
    period hPeriod sector circleMode]

theorem primitiveSpinCFullSphereEigenvalueSquared_strictMono :
    StrictMono primitiveSpinCFullSphereEigenvalueSquared := by
  intro first second hLess
  unfold primitiveSpinCFullSphereEigenvalueSquared
  have hCast : (first : Real) < second := by
    exact_mod_cast hLess
  have hFirst : 0 ≤ (first : Real) := by positivity
  push_cast
  nlinarith

theorem primitiveSpinCAllFullJointSquaredEigenvalue_level_injective
    (label : PrimitiveSpinCJointNormalFourierLabel) :
    Function.Injective
      (fun level =>
        ((primitiveSpinCFullSphereEigenvalueSquared level +
            normalRootLeviCivitaCorrectedFrequency
              period label.1 label.2 ^ 2 : Real) : Complex)) := by
  intro first second hEqual
  apply primitiveSpinCFullSphereEigenvalueSquared_strictMono.injective
  apply add_right_cancel
  exact Complex.ofReal_injective hEqual

theorem primitiveSpinCAllFullJointFamily_mem_eigenspace
    (index : PrimitiveSpinCAllFullJointIndex) :
    primitiveSpinCAllFullJointFamily period hPeriod index ∈
      Module.End.eigenspace
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap
          period hPeriod)
        (primitiveSpinCAllFullJointSquaredEigenvalue period index) := by
  rw [Module.End.mem_eigenspace_iff,
    primitiveSpinCAllFullJointFamily_eq_allMode,
    primitiveSpinCAllFullJointSquaredEigenvalue_eq_geometric]
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv index))) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter
        ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod
          (primitiveSpinCAllFullJointIndexEquiv index) : Real) : Complex)
        (primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod
          (primitiveSpinCAllFullJointIndexEquiv index))
  rw [primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq,
    d9PrimitiveSpinCComplexScalarSection_ofReal]

/-! ### Collision fibers and global independence -/

/-- At a fixed squared eigenvalue, choose the unique nonnegative sphere
level when it exists for a given Fourier label. -/
def primitiveSpinCFullJointEigenvalueCollisionLevel
    (eigenvalue : Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel) : Nat := by
  classical
  exact if hExists :
      ∃ level,
        ((primitiveSpinCFullSphereEigenvalueSquared level +
            normalRootLeviCivitaCorrectedFrequency
              period label.1 label.2 ^ 2 : Real) : Complex) =
          eigenvalue then
    Classical.choose hExists
  else
    0

theorem primitiveSpinCFullJointEigenvalueCollisionLevel_eq
    (eigenvalue : Complex)
    (label : PrimitiveSpinCJointNormalFourierLabel)
    (level : Nat)
    (hEigenvalue :
      ((primitiveSpinCFullSphereEigenvalueSquared level +
          normalRootLeviCivitaCorrectedFrequency
            period label.1 label.2 ^ 2 : Real) : Complex) =
        eigenvalue) :
    primitiveSpinCFullJointEigenvalueCollisionLevel
        period eigenvalue label = level := by
  unfold primitiveSpinCFullJointEigenvalueCollisionLevel
  split
  next hExists =>
    apply
      (primitiveSpinCAllFullJointSquaredEigenvalue_level_injective
        period label)
    exact (Classical.choose_spec hExists).trans hEigenvalue.symm
  next hMissing =>
    exact False.elim (hMissing ⟨level, hEigenvalue⟩)

/-- Embed one complete fixed-eigenvalue collision fiber into the
corresponding label-dependent full-level packet. -/
def primitiveSpinCFullJointEigenvalueCollisionEmbedding
    (eigenvalue : Complex) :
    { index : PrimitiveSpinCAllFullJointIndex //
        primitiveSpinCAllFullJointSquaredEigenvalue period index =
          eigenvalue } →
      PrimitiveSpinCJointAssignedFullIndex
        (primitiveSpinCFullJointEigenvalueCollisionLevel
          period eigenvalue) :=
  fun index =>
    ⟨index.1.1,
      Fin.cast
        (congrArg primitiveSphereModeDegeneracy
          (primitiveSpinCFullJointEigenvalueCollisionLevel_eq
            period eigenvalue index.1.1 index.1.2.1 index.2).symm)
        index.1.2.2⟩

theorem primitiveSpinCFullJointEigenvalueCollisionEmbedding_injective
    (eigenvalue : Complex) :
    Function.Injective
      (primitiveSpinCFullJointEigenvalueCollisionEmbedding
        period eigenvalue) := by
  rintro
    ⟨⟨firstLabel, ⟨firstLevel, firstMultiplicity⟩⟩, firstEigen⟩
    ⟨⟨secondLabel, ⟨secondLevel, secondMultiplicity⟩⟩, secondEigen⟩
    hEqual
  have hLabel : firstLabel = secondLabel :=
    congrArg Sigma.fst hEqual
  cases hLabel
  have hFirstLevel :=
    primitiveSpinCFullJointEigenvalueCollisionLevel_eq
      period eigenvalue firstLabel firstLevel firstEigen
  have hSecondLevel :=
    primitiveSpinCFullJointEigenvalueCollisionLevel_eq
      period eigenvalue firstLabel secondLevel secondEigen
  cases hFirstLevel
  cases hSecondLevel
  have hMultiplicity :
      firstMultiplicity = secondMultiplicity := by
    simpa [primitiveSpinCFullJointEigenvalueCollisionEmbedding] using hEqual
  cases hMultiplicity
  rfl

theorem primitiveSpinCJointAssignedFullFamily_collisionEmbedding
    (eigenvalue : Complex)
    (index :
      { index : PrimitiveSpinCAllFullJointIndex //
        primitiveSpinCAllFullJointSquaredEigenvalue period index =
          eigenvalue }) :
    primitiveSpinCJointAssignedFullFamily
        period hPeriod
        (primitiveSpinCFullJointEigenvalueCollisionLevel
          period eigenvalue)
        (primitiveSpinCFullJointEigenvalueCollisionEmbedding
          period eigenvalue index) =
      primitiveSpinCAllFullJointFamily period hPeriod index.1 := by
  rcases index with
    ⟨⟨label, ⟨level, multiplicity⟩⟩, hEigenvalue⟩
  have hLevel :=
    primitiveSpinCFullJointEigenvalueCollisionLevel_eq
      period eigenvalue label level hEigenvalue
  cases hLevel
  simp [primitiveSpinCJointAssignedFullFamily,
    primitiveSpinCAllFullJointFamily,
    primitiveSpinCFullJointEigenvalueCollisionEmbedding]

theorem primitiveSpinCAllFullJointFamily_collision_linearIndependent
    (eigenvalue : Complex) :
    LinearIndependent Complex
      (fun index :
          { index : PrimitiveSpinCAllFullJointIndex //
            primitiveSpinCAllFullJointSquaredEigenvalue period index =
              eigenvalue } =>
        primitiveSpinCAllFullJointFamily
          period hPeriod index.1) := by
  have hAssigned :=
    (primitiveSpinCJointAssignedFullFamily_linearIndependent
      period hPeriod
      (primitiveSpinCFullJointEigenvalueCollisionLevel
        period eigenvalue)).comp
      (primitiveSpinCFullJointEigenvalueCollisionEmbedding
        period eigenvalue)
      (primitiveSpinCFullJointEigenvalueCollisionEmbedding_injective
        period eigenvalue)
  simpa only [Function.comp_def,
    primitiveSpinCJointAssignedFullFamily_collisionEmbedding] using hAssigned

/-- The complete smooth family is jointly independent across the Hopf zero
tower, every positive sphere level, both sectors, all circle modes and all
multiplicities. -/
theorem primitiveSpinCAllFullJointFamily_linearIndependent :
    LinearIndependent Complex
      (primitiveSpinCAllFullJointFamily period hPeriod) := by
  classical
  let collisionPacket :
      (eigenvalue : Complex) →
        { index : PrimitiveSpinCAllFullJointIndex //
          primitiveSpinCAllFullJointSquaredEigenvalue period index =
            eigenvalue } →
          SmoothSection period hPeriod :=
    fun _ index =>
      primitiveSpinCAllFullJointFamily period hPeriod index.1
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
              { mode : PrimitiveSpinCAllFullJointIndex //
                primitiveSpinCAllFullJointSquaredEigenvalue period mode =
                  eigenvalue } =>
          collisionPacket index.1 index.2) := by
    apply linearIndependent_iUnion_finite
    · intro eigenvalue
      exact
        primitiveSpinCAllFullJointFamily_collision_linearIndependent
          period hPeriod eigenvalue
    · intro eigenvalue eigenvalues _ hNotMem
      apply (hEigenspaces.disjoint_biSup hNotMem).mono
      · rw [Submodule.span_le]
        rintro state ⟨index, rfl⟩
        change
          primitiveSpinCAllFullJointFamily period hPeriod index.1 ∈
            Module.End.eigenspace
              (primitiveSpinCGeometricDiracSquaredComplexLinearMap
                period hPeriod) eigenvalue
        simpa only [index.2] using
          (primitiveSpinCAllFullJointFamily_mem_eigenspace
            period hPeriod index.1)
      · refine iSup₂_le fun otherEigenvalue hOther => ?_
        rw [Submodule.span_le]
        rintro state ⟨index, rfl⟩
        apply Submodule.mem_iSup_of_mem otherEigenvalue
        apply Submodule.mem_iSup_of_mem hOther
        change
          primitiveSpinCAllFullJointFamily period hPeriod index.1 ∈
            Module.End.eigenspace
              (primitiveSpinCGeometricDiracSquaredComplexLinearMap
                period hPeriod) otherEigenvalue
        simpa only [index.2] using
          (primitiveSpinCAllFullJointFamily_mem_eigenspace
            period hPeriod index.1)
  let classify :
      PrimitiveSpinCAllFullJointIndex →
        Σ eigenvalue : Complex,
          { mode : PrimitiveSpinCAllFullJointIndex //
            primitiveSpinCAllFullJointSquaredEigenvalue period mode =
              eigenvalue } :=
    fun index =>
      ⟨primitiveSpinCAllFullJointSquaredEigenvalue period index,
        ⟨index, rfl⟩⟩
  have hClassify : Function.Injective classify := by
    intro first second hEqual
    exact congrArg (fun current => current.2.1) hEqual
  have hAll := hCombined.comp classify hClassify
  simpa only [collisionPacket, classify, Function.comp_def] using hAll

/-! ### Canonical full geometric coefficient synthesis -/

theorem primitiveSpinCAllModeNullHarmonicRealSection_linearIndependent :
    LinearIndependent Complex
      (primitiveSpinCAllModeNullHarmonicRealSection period hPeriod) := by
  have hReindexed :=
    (primitiveSpinCAllFullJointFamily_linearIndependent
      period hPeriod).comp
      primitiveSpinCAllFullJointIndexEquiv.symm
      primitiveSpinCAllFullJointIndexEquiv.symm.injective
  simpa only [Function.comp_def,
    primitiveSpinCAllFullJointFamily_eq_allMode,
    Equiv.apply_symm_apply] using hReindexed

/-- Canonically indexed finite synthesis over the complete geometric
zero-plus-positive spectrum. -/
def primitiveSpinCAllModeNullHarmonicSynthesis :
    (PrimitiveSpinCGeometricFullMode →₀ Complex) →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCAllModeNullHarmonicRealSection period hPeriod)

theorem primitiveSpinCAllModeNullHarmonicSynthesis_injective :
    Function.Injective
      (primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod) :=
  (primitiveSpinCAllModeNullHarmonicRealSection_linearIndependent
    period hPeriod).finsuppLinearCombination_injective

@[simp]
theorem primitiveSpinCAllModeNullHarmonicSynthesis_single
    (mode : PrimitiveSpinCGeometricFullMode)
    (coefficient : Complex) :
    primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod
        (Finsupp.single mode coefficient) =
      coefficient •
        primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod mode := by
  simp [primitiveSpinCAllModeNullHarmonicSynthesis]

def primitiveSpinCAllModeNullHarmonicSquaredCoefficientBlock
    (mode : PrimitiveSpinCGeometricFullMode) :
    Complex →ₗ[Complex]
      (PrimitiveSpinCGeometricFullMode →₀ Complex) :=
  (Finsupp.lsingle mode).comp
    (((primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod mode : Real) : Complex) •
      (LinearMap.id : Complex →ₗ[Complex] Complex))

/-- Exact canonical squared-Dirac diagonal on finite full-spectrum
coefficients. -/
def primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator :
    (PrimitiveSpinCGeometricFullMode →₀ Complex) →ₗ[Complex]
      (PrimitiveSpinCGeometricFullMode →₀ Complex) :=
  Finsupp.lsum Complex fun mode =>
    primitiveSpinCAllModeNullHarmonicSquaredCoefficientBlock
      period hPeriod mode

@[simp]
theorem
    primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator_single
    (mode : PrimitiveSpinCGeometricFullMode)
    (coefficient : Complex) :
    primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
        period hPeriod (Finsupp.single mode coefficient) =
      ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Real) : Complex) •
        Finsupp.single mode coefficient := by
  simp [primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator,
    primitiveSpinCAllModeNullHarmonicSquaredCoefficientBlock]

theorem primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq_complex
    (mode : PrimitiveSpinCGeometricFullMode) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod mode) =
      ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Real) : Complex) •
        primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod mode := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod mode)) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter
        ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Real) : Complex)
        (primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod mode)
  rw [primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq,
    d9PrimitiveSpinCComplexScalarSection_ofReal]

/-- The genuine geometric squared Dirac operator intertwines the canonical
complete finite synthesis with the exact full coefficient diagonal. -/
theorem primitiveSpinCAllModeNullHarmonicSynthesis_intertwines_dirac_sq
    (coefficients :
      PrimitiveSpinCGeometricFullMode →₀ Complex) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCAllModeNullHarmonicSynthesis
          period hPeriod coefficients) =
      primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod
        (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
          period hPeriod coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      change
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod 0 = 0
      exact map_zero
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap
          period hPeriod)
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add,
        primitiveSpinCAllModeNullHarmonicSynthesis_single,
        map_smul,
        primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq_complex,
        inductionHypothesis,
        primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator_single,
        map_add, map_smul,
        primitiveSpinCAllModeNullHarmonicSynthesis_single]
      rw [smul_smul, smul_smul, mul_comm]

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
end JanusFormal
