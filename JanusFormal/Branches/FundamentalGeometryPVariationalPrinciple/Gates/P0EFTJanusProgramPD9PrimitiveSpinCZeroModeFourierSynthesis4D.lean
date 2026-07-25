import Mathlib.LinearAlgebra.Finsupp.LSum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D

/-!
# Geometric finite Fourier synthesis of the primitive SpinC zero tower

The two normal-root towers are realized by the explicit global smooth
sections constructed from the Hopf zero mode.  Complex coefficients are
handled by two real section representatives, so no global complex
trivialization of the nontrivial SpinC bundle is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate Interval
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (ThroatData period hPeriod)).isLocalHomeomorph

/-- Labels of the complete monopole-sphere zero-mode tower. -/
abbrev PrimitiveSpinCGeometricZeroModeLabel :=
  NormalRootChoice × Int

/-- Finite complex coefficient packets for both normal-root sectors. -/
abbrev PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  PrimitiveSpinCGeometricZeroModeLabel →₀ Complex

/-- Coefficient of a matter spinor on the explicit `+i` eigenline, read
through the first ambient half-spinor coordinate. -/
def d9MatterGammaPositiveCoefficientLinearMap :
    MatterFiber →ₗ[Real] Complex where
  toFun matter := matterFiberHalfSpinorLinearEquiv matter 0
  map_add' first second := by
    simp
  map_smul' scalar matter := by
    simp

@[simp]
theorem d9MatterGammaPositiveCoefficientLinearMap_eigenline
    (coefficient : Complex) :
    d9MatterGammaPositiveCoefficientLinearMap
        (d9MatterGammaPositiveEigenlineCLM coefficient) =
      coefficient := by
  simp [d9MatterGammaPositiveCoefficientLinearMap,
    d9MatterGammaPositiveEigenlineCLM,
    d9MatterFiberHalfSpinorContinuousLinearEquiv,
    ambientHalfGammaPositiveEigenvector]

@[simp]
theorem d9MatterGammaPositiveCoefficientLinearMap_complexAction
    (coefficient : Complex) :
    d9MatterGammaPositiveCoefficientLinearMap
        (d9MatterComplexAction coefficient
          d9MatterGammaPositiveEigenvector) =
      coefficient := by
  rw [← d9MatterGammaPositiveEigenlineCLM_apply]
  exact d9MatterGammaPositiveCoefficientLinearMap_eigenline coefficient

/-- Read the eigenline coefficient from the component occupied by one of
the two normal-root sectors. -/
def primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
    (sector : NormalRootChoice) :
    D9DoubledMatterFiber →ₗ[Real] Complex where
  toFun matter :=
    match sector with
    | .positiveQuarter =>
        d9MatterGammaPositiveCoefficientLinearMap matter.1
    | .negativeQuarter =>
        d9MatterGammaPositiveCoefficientLinearMap matter.2
  map_add' first second := by
    cases sector <;> simp
  map_smul' scalar matter := by
    cases sector <;> simp

theorem
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_scaledMode
    (target source : NormalRootChoice)
    (coefficient : Complex) (mode : Int)
    (point : ThroatCover period hPeriod) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap target
        (primitiveSpinCScaledNormalModeDoubledLift
          period hPeriod coefficient source mode point) =
      if source = target then
        coefficient *
          normalRootSpinFramePhase
            period hPeriod source mode point
      else 0 := by
  cases target <;> cases source
  · simp [primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
      primitiveSpinCScaledNormalModeDoubledLift,
      normalRootScaledMatterModeLift,
      normalRootScaledMatterModeValue]
  · change d9MatterGammaPositiveCoefficientLinearMap
        (0 : MatterFiber) = 0
    exact map_zero d9MatterGammaPositiveCoefficientLinearMap
  · change d9MatterGammaPositiveCoefficientLinearMap
        (0 : MatterFiber) = 0
    exact map_zero d9MatterGammaPositiveCoefficientLinearMap
  · simp [primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
      primitiveSpinCScaledNormalModeDoubledLift,
      normalRootScaledMatterModeLift,
      normalRootScaledMatterModeValue]

/-- Canonical embedding of one normal-root tower into the doubled zero-mode
label set. -/
def primitiveSpinCGeometricZeroModeSectorEmbedding
    (sector : NormalRootChoice) :
    Int ↪ PrimitiveSpinCGeometricZeroModeLabel where
  toFun mode := (sector, mode)
  inj' := by
    intro first second hEqual
    exact congrArg Prod.snd hEqual

/-- Restriction of a doubled finite packet to one normal-root tower. -/
def primitiveSpinCGeometricZeroModeSectorRestriction
    (sector : NormalRootChoice) :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real]
      (Int →₀ Complex) :=
  Finsupp.lcomapDomain
    (primitiveSpinCGeometricZeroModeSectorEmbedding sector)
    (primitiveSpinCGeometricZeroModeSectorEmbedding sector).injective

@[simp]
theorem primitiveSpinCGeometricZeroModeSectorRestriction_apply
    (sector : NormalRootChoice)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients)
    (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorRestriction
        sector coefficients mode =
      coefficients (sector, mode) :=
  rfl

theorem primitiveSpinCGeometricZeroModeSectorRestriction_single
    (target source : NormalRootChoice)
    (mode : Int) (coefficient : Complex) :
    primitiveSpinCGeometricZeroModeSectorRestriction target
        (Finsupp.single (source, mode) coefficient) =
      if source = target then
        Finsupp.single mode coefficient
      else 0 := by
  by_cases hSector : source = target
  · subst source
    rw [if_pos rfl]
    exact Finsupp.comapDomain_single
      (primitiveSpinCGeometricZeroModeSectorEmbedding target)
      mode coefficient _
  · rw [if_neg hSector]
    apply Finsupp.comapDomain_single_of_not_mem_range
    rintro ⟨candidate, hCandidate⟩
    exact hSector (congrArg Prod.fst hCandidate).symm

/-- Finitely supported scalar Fourier synthesis in one normal-root tower. -/
def normalRootSpinFrameFinsuppPacketLinearMap
    (sector : NormalRootChoice) (time : Real) :
    (Int →₀ Complex) →ₗ[Real] Complex :=
  Finsupp.lsum Real fun mode =>
    (normalModeComplexRightMulRealCLM
      (normalRootSpinFrameExponential
        period sector mode time)).toLinearMap

@[simp]
theorem normalRootSpinFrameFinsuppPacketLinearMap_single
    (sector : NormalRootChoice) (time : Real)
    (mode : Int) (coefficient : Complex) :
    normalRootSpinFrameFinsuppPacketLinearMap
        period sector time (Finsupp.single mode coefficient) =
      coefficient *
        normalRootSpinFrameExponential period sector mode time := by
  rw [normalRootSpinFrameFinsuppPacketLinearMap,
    Finsupp.lsum_single]
  rfl

theorem normalRootSpinFrameFinsuppPacketLinearMap_eq_finitePacket
    (sector : NormalRootChoice) (time : Real)
    (coefficients : Int →₀ Complex) :
    normalRootSpinFrameFinsuppPacketLinearMap
        period sector time coefficients =
      normalRootSpinFrameFinitePacket
        period sector coefficients.support coefficients time := by
  simp [normalRootSpinFrameFinsuppPacketLinearMap,
    Finsupp.lsum_apply, normalRootSpinFrameFinitePacket,
    Finsupp.sum]

/-- A finite coefficient packet viewed as its complete scalar function of
the cover time. -/
def normalRootSpinFrameFinsuppPacketFunctionLinearMap
    (sector : NormalRootChoice) :
    (Int →₀ Complex) →ₗ[Real] (Real → Complex) where
  toFun coefficients time :=
    normalRootSpinFrameFinsuppPacketLinearMap
      period sector time coefficients
  map_add' first second := by
    funext time
    exact map_add
      (normalRootSpinFrameFinsuppPacketLinearMap
        period sector time) first second
  map_smul' scalar coefficients := by
    funext time
    exact map_smul
      (normalRootSpinFrameFinsuppPacketLinearMap
        period sector time) scalar coefficients

/-- Exact Fourier coefficient extraction makes finite scalar synthesis
injective in either normal-root tower. -/
theorem normalRootSpinFrameFinsuppPacketFunctionLinearMap_injective
    (hPeriod : period ≠ 0) :
    ∀ sector : NormalRootChoice,
    Function.Injective
      (normalRootSpinFrameFinsuppPacketFunctionLinearMap
        period sector) := by
  intro sector
  intro first second hEqual
  have hDifference :
      normalRootSpinFrameFinsuppPacketFunctionLinearMap
          period sector (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hPointwise :
      ∀ time,
        normalRootSpinFrameFinitePacket
          period sector (first - second).support
            (first - second) time = 0 := by
    intro time
    have hTime := congrFun hDifference time
    change
      normalRootSpinFrameFinsuppPacketLinearMap
          period sector time (first - second) = 0 at hTime
    rw [normalRootSpinFrameFinsuppPacketLinearMap_eq_finitePacket]
      at hTime
    exact hTime
  have hCoefficients :=
    normalRootSpinFrameFinitePacket_eq_zero_coefficients
      period hPeriod sector (first - second).support
        (first - second) hPointwise
  apply sub_eq_zero.mp
  apply Finsupp.ext
  intro mode
  by_cases hMode : mode ∈ (first - second).support
  · exact hCoefficients mode hMode
  · exact Finsupp.notMem_support_iff.mp hMode

/-- Parseval identity for an arbitrary finitely supported coefficient
packet in one normal-root tower. -/
theorem normalRootSpinFrameFinsuppPacket_parseval
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (coefficients : Int →₀ Complex) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameFinsuppPacketLinearMap
                period sector time coefficients) *
            normalRootSpinFrameFinsuppPacketLinearMap
              period sector time coefficients) =
      ∑ mode ∈ coefficients.support,
        conj (coefficients mode) * coefficients mode := by
  simpa only [
    normalRootSpinFrameFinsuppPacketLinearMap_eq_finitePacket]
    using
      (normalRootSpinFrameFinitePacket_parseval
        period hPeriod sector coefficients.support coefficients)

/-- Pairing with one basis exponential recovers the corresponding
coefficient of an arbitrary finitely supported packet. -/
theorem normalRootSpinFrameFinsuppPacket_coefficient
    (hPeriod : period ≠ 0)
    (sector : NormalRootChoice)
    (coefficients : Int →₀ Complex)
    (mode : Int) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameExponential
                period sector mode time) *
            normalRootSpinFrameFinsuppPacketLinearMap
              period sector time coefficients) =
      coefficients mode := by
  simp_rw [
    normalRootSpinFrameFinsuppPacketLinearMap_eq_finitePacket]
  rw [normalRootSpinFrameFinitePacket_coefficient
    period hPeriod sector coefficients.support coefficients mode]
  by_cases hMode : mode ∈ coefficients.support
  · simp only [if_pos hMode]
  · rw [if_neg hMode, Finsupp.notMem_support_iff.mp hMode]

/-- One complex coefficient realized as a real-linear combination of the
two genuine smooth representatives of a zero-tower mode. -/
def primitiveSpinCGeometricZeroModeCoefficientLinearMap
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Real]
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter where
  toFun coefficient :=
    coefficient.re •
        primitiveSpinCGeometricZeroModeSection
          period hPeriod label.1 label.2 +
      coefficient.im •
        primitiveSpinCGeometricZeroModeImaginarySection
          period hPeriod label.1 label.2
  map_add' first second := by
    simp only [Complex.add_re, Complex.add_im]
    module
  map_smul' scalar coefficient := by
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero]
    change _ = scalar • (_ + _)
    rw [smul_add, smul_smul, smul_smul]

/-- Real-linear synthesis of every finite complex zero-tower packet as a
genuine global smooth section of the primitive SpinC bundle. -/
def primitiveSpinCGeometricFiniteZeroModeSynthesis :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter :=
  Finsupp.lsum Real
    (primitiveSpinCGeometricZeroModeCoefficientLinearMap
      period hPeriod)

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSynthesis_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod (Finsupp.single label coefficient) =
      primitiveSpinCGeometricZeroModeCoefficientLinearMap
        period hPeriod label coefficient :=
  Finsupp.lsum_single Real
    (primitiveSpinCGeometricZeroModeCoefficientLinearMap
      period hPeriod) label coefficient

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSynthesis_single_one
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod (Finsupp.single label 1) =
      primitiveSpinCGeometricZeroModeSection
        period hPeriod label.1 label.2 := by
  rw [primitiveSpinCGeometricFiniteZeroModeSynthesis_single]
  simp [primitiveSpinCGeometricZeroModeCoefficientLinearMap]

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSynthesis_single_I
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod (Finsupp.single label Complex.I) =
      primitiveSpinCGeometricZeroModeImaginarySection
        period hPeriod label.1 label.2 := by
  rw [primitiveSpinCGeometricFiniteZeroModeSynthesis_single]
  simp [primitiveSpinCGeometricZeroModeCoefficientLinearMap]

/-- Real-linear local-coordinate evaluation of a smooth primitive SpinC
section in one installed bundle chart. -/
def primitiveSpinCGeometricSectionLocalCoordinate
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter →ₗ[Real]
      D9DoubledMatterFiber :=
  ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter).localTriv index
    |>.linearMapAt Real base).comp
      (d9PrimitiveSpinCSectionEvaluation
        period hPeriod .positiveQuarter base)

theorem primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (state :
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base state =
      ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod .positiveQuarter).localTriv index
        ⟨base, state base⟩).2 := by
  change
    ((d9PrimitiveSpinCVectorBundleCore
        period hPeriod .positiveQuarter).localTriv index
      |>.linearMapAt Real base) (state base) = _
  rw [Bundle.Trivialization.linearMapAt_apply]
  have hBase' :
      base ∈
        ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod .positiveQuarter).localTriv index).baseSet :=
    hBase
  rw [if_pos hBase']

theorem primitiveSpinCGeometricSectionLocalCoordinate_zeroMode
    (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (primitiveSpinCGeometricZeroModeSection
          period hPeriod sector mode) =
      (primitiveSpinCGeometricZeroModeLocalGaugeFamily
        period hPeriod sector mode).localValue index base := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
    period hPeriod index base hBase]
  exact primitiveSpinCBundleSection_localTriv
    period hPeriod .positiveQuarter
    (primitiveSpinCGeometricZeroModeLocalGaugeFamily
      period hPeriod sector mode)
    index base hBase

theorem primitiveSpinCGeometricSectionLocalCoordinate_imaginaryZeroMode
    (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (primitiveSpinCGeometricZeroModeImaginarySection
          period hPeriod sector mode) =
      (primitiveSpinCTensorLocalGaugeFamily
        period hPeriod .positiveQuarter
        (primitiveSpinCScaledNormalModeDoubledLift
          period hPeriod Complex.I sector mode)
        primitiveMonopoleZeroLocalScalarFamily).localValue index base := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
    period hPeriod index base hBase]
  exact primitiveSpinCBundleSection_localTriv
    period hPeriod .positiveQuarter
    (primitiveSpinCTensorLocalGaugeFamily
      period hPeriod .positiveQuarter
      (primitiveSpinCScaledNormalModeDoubledLift
        period hPeriod Complex.I sector mode)
      primitiveMonopoleZeroLocalScalarFamily)
    index base hBase

/-- Equatorial cover point used to read all normal Fourier coefficients. -/
def primitiveSpinCGeometricZeroModeWitnessCover
    (time : Real) : ThroatCover period hPeriod :=
  ⟨equatorialTwoSphereHomeomorph.symm (monopoleEquator 0), time⟩

/-- Quotient class of the equatorial witness. -/
def primitiveSpinCGeometricZeroModeWitnessBase
    (time : Real) : ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCGeometricZeroModeWitnessCover
      period hPeriod time)

/-- Joint normal/monopole chart centered at the equatorial witness. -/
def primitiveSpinCGeometricZeroModeWitnessIndex
    (time : Real) : D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCGeometricZeroModeWitnessCover
      period hPeriod time, .north)

@[simp]
theorem primitiveSpinCGeometricZeroModeWitnessCover_time
    (time : Real) :
    (primitiveSpinCGeometricZeroModeWitnessCover
      period hPeriod time).time = time :=
  rfl

@[simp]
theorem primitiveSpinCGeometricZeroModeWitnessCover_sphere
    (time : Real) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time) =
      monopoleEquator 0 := by
  simp [primitiveSpinCGeometricZeroModeWitnessCover,
    d9MonopoleSphereCoverProjection]

@[simp]
theorem primitiveMonopoleZeroLocalValue_witness :
    primitiveMonopoleZeroLocalValue .north (monopoleEquator 0) = 1 := by
  simp [primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroNorthValue, monopoleEquator,
    monopoleSphereCoordinate]

theorem primitiveSpinCGeometricZeroModeWitnessBase_mem
    (time : Real) :
    primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time) := by
  constructor
  · exact (throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) ∈
        monopoleChartDomain .north
    rw [primitiveSpinCGeometricZeroModeWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCGeometricZeroModeWitnessCover_sphere]
    simp [monopoleChartDomain, monopoleEquator,
      monopoleSphereCoordinate]

theorem primitiveSpinCGeometricSectionLocalCoordinate_zeroMode_witness
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_zeroMode
    period hPeriod sector mode
    (primitiveSpinCGeometricZeroModeWitnessIndex
      period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase
      period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time)]
  change
    d9PrimitiveSpinCComplexActionCLM
        (primitiveMonopoleZeroLocalValue .north
          (d9ThroatMonopoleSphereProjection period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time)))
        (doubledSpinorLiftLocalValue
          period hPeriod .positiveQuarter
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode)
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) =
      _
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere,
    primitiveMonopoleZeroLocalValue_witness,
    doubledSpinorLiftLocalValue_mk]
  exact d9PrimitiveSpinCComplexAction_one _

theorem
    primitiveSpinCGeometricSectionLocalCoordinate_imaginaryZeroMode_witness
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeImaginarySection
          period hPeriod sector mode) =
      primitiveSpinCScaledNormalModeDoubledLift
        period hPeriod Complex.I sector mode
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_imaginaryZeroMode
    period hPeriod sector mode
    (primitiveSpinCGeometricZeroModeWitnessIndex
      period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase
      period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time)]
  change
    d9PrimitiveSpinCComplexActionCLM
        (primitiveMonopoleZeroLocalValue .north
          (d9ThroatMonopoleSphereProjection period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time)))
        (doubledSpinorLiftLocalValue
          period hPeriod .positiveQuarter
          (primitiveSpinCScaledNormalModeDoubledLift
            period hPeriod Complex.I sector mode)
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) =
      _
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere,
    primitiveMonopoleZeroLocalValue_witness,
    doubledSpinorLiftLocalValue_mk]
  exact d9PrimitiveSpinCComplexAction_one _

theorem primitiveSpinCGeometricSectionLocalCoordinate_coefficient_witness
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficient) =
      primitiveSpinCScaledNormalModeDoubledLift
        period hPeriod coefficient sector mode
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time) := by
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (coefficient.re •
            primitiveSpinCGeometricZeroModeSection
              period hPeriod sector mode +
          coefficient.im •
            primitiveSpinCGeometricZeroModeImaginarySection
              period hPeriod sector mode) =
      _
  rw [map_add, map_smul, map_smul,
    primitiveSpinCGeometricSectionLocalCoordinate_zeroMode_witness,
    primitiveSpinCGeometricSectionLocalCoordinate_imaginaryZeroMode_witness]
  cases sector
  · apply Prod.ext
    · exact normalRootScaledMatterModeValue_eq_re_im
        period hPeriod coefficient .positiveQuarter mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time)
    · change
        coefficient.re • (0 : MatterFiber) +
            coefficient.im • (0 : MatterFiber) = 0
      simp
  · apply Prod.ext
    · change
        coefficient.re • (0 : MatterFiber) +
            coefficient.im • (0 : MatterFiber) = 0
      simp
    · exact normalRootScaledMatterModeValue_eq_re_im
        period hPeriod coefficient .negativeQuarter mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time)

/-- Local-coordinate formula for an arbitrary finite global zero-mode
packet. -/
theorem primitiveSpinCGeometricFiniteZeroModeSynthesis_witness
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients)
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCGeometricFiniteZeroModeSynthesis
          period hPeriod coefficients) =
      coefficients.sum fun label coefficient =>
        primitiveSpinCScaledNormalModeDoubledLift
          period hPeriod coefficient label.1 label.2
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time) := by
  rw [primitiveSpinCGeometricFiniteZeroModeSynthesis,
    Finsupp.lsum_apply, map_finsuppSum]
  apply Finsupp.sum_congr
  intro label hLabel
  exact primitiveSpinCGeometricSectionLocalCoordinate_coefficient_witness
    period hPeriod _ label.1 label.2 time

/-- Fourier analysis of a finite global packet obtained by local
equatorial evaluation and projection onto one occupied eigenline. -/
def primitiveSpinCGeometricZeroModeWitnessAnalysis
    (sector : NormalRootChoice) (time : Real) :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real] Complex :=
  (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector).comp
    ((primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCGeometricZeroModeWitnessIndex
        period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time)).comp
      (primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod))

theorem primitiveSpinCGeometricZeroModeWitnessAnalysis_single
    (target source : NormalRootChoice)
    (mode : Int) (coefficient : Complex) (time : Real) :
    primitiveSpinCGeometricZeroModeWitnessAnalysis
        period hPeriod target time
        (Finsupp.single (source, mode) coefficient) =
      if source = target then
        coefficient *
          normalRootSpinFrameExponential period source mode time
      else 0 := by
  rw [primitiveSpinCGeometricZeroModeWitnessAnalysis,
    LinearMap.comp_apply, LinearMap.comp_apply,
    primitiveSpinCGeometricFiniteZeroModeSynthesis_single,
    primitiveSpinCGeometricSectionLocalCoordinate_coefficient_witness,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_scaledMode]
  by_cases hSector : source = target
  · simp only [if_pos hSector]
    rw [← normalRootSpinFrameExponential_eq_phase
      period hPeriod source mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time)]
    simp
  · simp only [if_neg hSector]

/-- The geometric witness analysis is exactly ordinary finite Fourier
synthesis after restriction to the selected normal-root tower. -/
theorem primitiveSpinCGeometricZeroModeWitnessAnalysis_eq :
    ∀ sector : NormalRootChoice, ∀ time : Real,
      primitiveSpinCGeometricZeroModeWitnessAnalysis
          period hPeriod sector time =
        (normalRootSpinFrameFinsuppPacketLinearMap
          period sector time).comp
          (primitiveSpinCGeometricZeroModeSectorRestriction sector) := by
  intro sector time
  apply Finsupp.lhom_ext
  intro label coefficient
  rcases label with ⟨source, mode⟩
  rw [LinearMap.comp_apply,
    primitiveSpinCGeometricZeroModeSectorRestriction_single,
    primitiveSpinCGeometricZeroModeWitnessAnalysis_single]
  by_cases hSector : source = sector
  · subst source
    simp only [if_pos rfl]
    exact
      (normalRootSpinFrameFinsuppPacketLinearMap_single
        period sector time mode coefficient).symm
  · simp [hSector]

theorem primitiveSpinCGeometricZeroModeWitnessAnalysis_apply
    (sector : NormalRootChoice) (time : Real)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCGeometricZeroModeWitnessAnalysis
        period hPeriod sector time coefficients =
      normalRootSpinFrameFinsuppPacketLinearMap
        period sector time
        (primitiveSpinCGeometricZeroModeSectorRestriction
          sector coefficients) :=
  LinearMap.congr_fun
    (primitiveSpinCGeometricZeroModeWitnessAnalysis_eq
      period hPeriod sector time) coefficients

/-- Local geometric analysis recovers every finite zero-mode coefficient
by the usual Fourier pairing. -/
theorem primitiveSpinCGeometricZeroModeWitnessAnalysis_coefficient
    (sector : NormalRootChoice)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients)
    (mode : Int) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameExponential
                period sector mode time) *
            primitiveSpinCGeometricZeroModeWitnessAnalysis
              period hPeriod sector time coefficients) =
      coefficients (sector, mode) := by
  simp only [
    primitiveSpinCGeometricZeroModeWitnessAnalysis_apply,
    normalRootSpinFrameFinsuppPacket_coefficient
      period hPeriod sector
      (primitiveSpinCGeometricZeroModeSectorRestriction
        sector coefficients) mode,
    primitiveSpinCGeometricZeroModeSectorRestriction_apply]

/-- Parseval identity read directly from a genuine global smooth
zero-mode packet through the geometric witness chart. -/
theorem primitiveSpinCGeometricZeroModeWitnessAnalysis_parseval
    (sector : NormalRootChoice)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (primitiveSpinCGeometricZeroModeWitnessAnalysis
                period hPeriod sector time coefficients) *
            primitiveSpinCGeometricZeroModeWitnessAnalysis
              period hPeriod sector time coefficients) =
      ∑ mode ∈
          (primitiveSpinCGeometricZeroModeSectorRestriction
            sector coefficients).support,
        conj
            (primitiveSpinCGeometricZeroModeSectorRestriction
              sector coefficients mode) *
          primitiveSpinCGeometricZeroModeSectorRestriction
            sector coefficients mode := by
  simp only [
    primitiveSpinCGeometricZeroModeWitnessAnalysis_apply,
    normalRootSpinFrameFinsuppPacket_parseval
      period hPeriod sector
      (primitiveSpinCGeometricZeroModeSectorRestriction
        sector coefficients)]

/-- The explicit global smooth zero-mode sections are linearly independent:
finite geometric synthesis loses no complex coefficient in either
normal-root sector. -/
theorem primitiveSpinCGeometricFiniteZeroModeSynthesis_injective :
    Function.Injective
      (primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod) := by
  intro first second hEqual
  have hSector (sector : NormalRootChoice) :
      primitiveSpinCGeometricZeroModeSectorRestriction sector first =
        primitiveSpinCGeometricZeroModeSectorRestriction sector second := by
    apply normalRootSpinFrameFinsuppPacketFunctionLinearMap_injective
      period hPeriod sector
    funext time
    change
      normalRootSpinFrameFinsuppPacketLinearMap
          period sector time
          (primitiveSpinCGeometricZeroModeSectorRestriction
            sector first) =
        normalRootSpinFrameFinsuppPacketLinearMap
          period sector time
          (primitiveSpinCGeometricZeroModeSectorRestriction
            sector second)
    have hLocal := congrArg
      (fun state :
          D9PrimitiveSpinCSmoothSection
            period hPeriod .positiveQuarter =>
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
          sector
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessIndex
              period hPeriod time)
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) state))
      hEqual
    have hWitness :
        primitiveSpinCGeometricZeroModeWitnessAnalysis
            period hPeriod sector time first =
          primitiveSpinCGeometricZeroModeWitnessAnalysis
            period hPeriod sector time second := by
      change
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
            sector
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCGeometricZeroModeWitnessIndex
                period hPeriod time)
              (primitiveSpinCGeometricZeroModeWitnessBase
                period hPeriod time)
              (primitiveSpinCGeometricFiniteZeroModeSynthesis
                period hPeriod first)) =
          primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
            sector
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCGeometricZeroModeWitnessIndex
                period hPeriod time)
              (primitiveSpinCGeometricZeroModeWitnessBase
                period hPeriod time)
              (primitiveSpinCGeometricFiniteZeroModeSynthesis
                period hPeriod second))
      exact hLocal
    rw [primitiveSpinCGeometricZeroModeWitnessAnalysis_apply,
      primitiveSpinCGeometricZeroModeWitnessAnalysis_apply]
      at hWitness
    exact hWitness
  apply Finsupp.ext
  intro label
  rcases label with ⟨sector, mode⟩
  have hMode := congrArg
    (fun coefficients : Int →₀ Complex => coefficients mode)
    (hSector sector)
  simpa only [
    primitiveSpinCGeometricZeroModeSectorRestriction_apply]
    using hMode

end
end P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
end JanusFormal
