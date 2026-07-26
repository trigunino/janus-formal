import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeDiagonalRealization4D

/-!
# Geometric spectral realization of the primitive SpinC Hopf zero modes

This gate supplies the second real representative of each complex Hopf
zero-mode coordinate and proves exact covariance of the geometric Dirac
operator under the global imaginary action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeDiagonalRealization4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

theorem d9PrimitiveSpinCCoordChange_imaginary
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCCoordChange period hPeriod choice first second base
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice first second base matter) := by
  unfold d9PrimitiveSpinCCoordChange
  simp only [ContinuousLinearMap.comp_apply,
    d9DoubledMatterSpinorMonodromyCLM_apply]
  rw [← d9PrimitiveSpinCImaginaryAction_monodromy]
  exact
    (d9PrimitiveSpinCImaginaryAction_commutes_phase
      (d9PrimitiveSpinCPhaseTransition
        period hPeriod first.2 second.2 base)
      (d9DoubledMatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first.1 second.1 base)
        matter)).symm

/-- Apply the global complex structure to every local representative. -/
def d9PrimitiveSpinCImaginaryLocalGaugeFamily
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base :=
    d9PrimitiveSpinCImaginaryAction (family.localValue index base)
  contMDiffOn_localValue index :=
    d9PrimitiveSpinCImaginaryAction.contDiff.contMDiff
      |>.comp_contMDiffOn (family.contMDiffOn_localValue index)
  coordChange_localValue first second base hBase := by
    rw [d9PrimitiveSpinCCoordChange_imaginary,
      family.coordChange_localValue first second base hBase]

@[simp]
theorem d9PrimitiveSpinCImaginaryLocalGaugeFamily_localValue
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod choice family).localValue index base =
      d9PrimitiveSpinCImaginaryAction
        (family.localValue index base) :=
  rfl

/-- The second real representative of one complex Hopf zero-mode
coordinate. -/
def primitiveSpinCHopfZeroModeImaginarySection
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (d9PrimitiveSpinCImaginaryLocalGaugeFamily
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode)).toSmoothSection
        period hPeriod .positiveQuarter

theorem d9PrimitiveSpinCLocalFlatFrameDerivative_imaginary
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCImaginaryLocalGaugeFamily
          period hPeriod choice family)
        index direction base =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family index direction base) := by
  let field := family.localValue index
  let tangent :=
    d9IntrinsicThroatFrame period hPeriod direction base
  have hField :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) field base :=
    ((family.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hOuter :
      MDifferentiableAt
        𝓘(Real, D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        d9PrimitiveSpinCImaginaryAction (field base) :=
    d9PrimitiveSpinCImaginaryAction.differentiableAt.mdifferentiableAt
  have hChain :=
    mfderiv_comp_apply base hOuter hField tangent
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (d9PrimitiveSpinCImaginaryAction ∘ field) base tangent =
      d9PrimitiveSpinCImaginaryAction
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) field base tangent)
  exact hChain

theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_imaginary
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCImaginaryLocalGaugeFamily
          period hPeriod choice family)
        index direction base =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family index direction base) := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_imaginary
      (hBase := hBase),
    d9PrimitiveSpinCImaginaryLocalGaugeFamily_localValue]
  have hCorrection :=
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_phase
      period hPeriod d9PrimitiveSpinCImaginaryPhase
      direction base (family.localValue index base)
  change
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9PrimitiveSpinCImaginaryAction
          (family.localValue index base)) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base
          (family.localValue index base)) at hCorrection
  rw [hCorrection]
  exact (map_add d9PrimitiveSpinCImaginaryAction _ _).symm

theorem d9PrimitiveSpinCLocalGeometricDirac_imaginary
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice
        (d9PrimitiveSpinCImaginaryLocalGaugeFamily
          period hPeriod choice family)
        index base =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family index base) := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  simp only
  rw [d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_imaginary
      (hBase := hBase),
    d9PrimitiveSpinCImaginaryLocalGaugeFamily_localValue]
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
  simp only [d9PrimitiveSpinCImaginaryAction_clifford,
    map_add, map_smul]

/-- The imaginary representative obeys the same first-order global
eigen-equation as the real Hopf representative. -/
theorem primitiveSpinCHopfZeroModeImaginaryGeometricDiracOperator_eigen
    (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod sector mode) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod sector mode := by
  let family :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let imaginaryFamily :=
    d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod .positiveQuarter family
  rw [show
      primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod sector mode =
        imaginaryFamily.toSmoothSection
          period hPeriod .positiveQuarter by rfl]
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  ext base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  let point :=
    normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    exact core.mem_baseSet_at base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    hBase.2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hLocal :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter imaginaryFamily
        (point, chart) base =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        imaginaryFamily.localValue (point, chart) base
  rw [d9PrimitiveSpinCLocalGeometricDirac_imaginary
      (hBase := hBase)]
  change
    d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter family
          (point, chart) base) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        d9PrimitiveSpinCImaginaryAction
          (family.localValue (point, chart) base)
  rw [← hProject, hLocal, map_smul]

theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      (primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod sector mode).localValue index base := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
    period hPeriod index base hBase]
  exact primitiveSpinCBundleSection_localTriv
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode)
    index base hBase

theorem
    primitiveSpinCGeometricSectionLocalCoordinate_hopfImaginaryZeroMode
    (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod sector mode) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue index base) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
    period hPeriod index base hBase]
  exact primitiveSpinCBundleSection_localTriv
    period hPeriod .positiveQuarter
    (d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod .positiveQuarter
      (primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod sector mode))
    index base hBase

@[simp]
theorem primitiveMonopoleZeroComplementLocalValue_witness :
    primitiveMonopoleZeroComplementLocalValue
        .north (monopoleEquator 0) = 1 := by
  simp [primitiveMonopoleZeroComplementLocalValue,
    primitiveMonopoleZeroComplementNorthValue, monopoleEquator,
    monopoleSphereCoordinate, monopoleSphereXY]
  change star (1 : Complex) = 1
  simp

/-- At the equatorial witness the two Hopf coordinates add the two
complementary radial projectors, giving exactly twice the normal mode. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      (2 : Real) •
        primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    period hPeriod sector mode
    (primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase period hPeriod time)
    (primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time)]
  change
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time, .north)
        (mappingTorusMk (ThroatData period hPeriod)
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time)) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere,
    primitiveMonopoleZeroLocalValue_witness,
    primitiveMonopoleZeroComplementLocalValue_witness,
    d9PrimitiveSpinCComplexAction_one,
    d9PrimitiveSpinCComplexAction_one]
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply]
  module

theorem
    primitiveSpinCGeometricSectionLocalCoordinate_hopfImaginaryZeroMode_witness
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod sector mode) =
      (2 : Real) •
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode
            (primitiveSpinCGeometricZeroModeWitnessCover
              period hPeriod time)) := by
  rw [
    primitiveSpinCGeometricSectionLocalCoordinate_hopfImaginaryZeroMode
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase_mem
        period hPeriod time)]
  have hHopf :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
      period hPeriod sector mode time
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase_mem
        period hPeriod time)] at hHopf
  rw [hHopf, map_smul]

theorem d9MatterComplexAction_normalRootMatterModeValue_I
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9MatterComplexAction Complex.I
        (normalRootMatterModeValue
          period hPeriod sector mode point) =
      normalRootScaledMatterModeValue
        period hPeriod Complex.I sector mode point := by
  simp only [normalRootMatterModeValue,
    normalRootScaledMatterModeValue,
    d9MatterGammaPositiveEigenlineCLM_apply]
  exact
    (d9MatterComplexAction_mul Complex.I
      (normalRootSpinFramePhase period hPeriod sector mode point)
      d9MatterGammaPositiveEigenvector).symm

theorem d9PrimitiveSpinCImaginaryAction_normalModeDoubledLift
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) =
      primitiveSpinCScaledNormalModeDoubledLift
        period hPeriod Complex.I sector mode point := by
  rw [d9PrimitiveSpinCImaginaryAction_eq_pair]
  cases sector
  · apply Prod.ext
    · exact d9MatterComplexAction_normalRootMatterModeValue_I
        period hPeriod .positiveQuarter mode point
    · change d9MatterComplexAction Complex.I (0 : MatterFiber) = 0
      apply matterFiberHalfSpinorLinearEquiv.injective
      simp
  · apply Prod.ext
    · change d9MatterComplexAction Complex.I (0 : MatterFiber) = 0
      apply matterFiberHalfSpinorLinearEquiv.injective
      simp
    · exact d9MatterComplexAction_normalRootMatterModeValue_I
        period hPeriod .negativeQuarter mode point

/-- A complex coefficient is represented by the real Hopf mode and its
global imaginary rotation. -/
def primitiveSpinCHopfZeroModeCoefficientLinearMap
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Real]
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter where
  toFun coefficient :=
    coefficient.re •
        primitiveSpinCHopfZeroModeSection
          period hPeriod label.1 label.2 +
      coefficient.im •
        primitiveSpinCHopfZeroModeImaginarySection
          period hPeriod label.1 label.2
  map_add' first second := by
    simp only [Complex.add_re, Complex.add_im]
    module
  map_smul' scalar coefficient := by
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero]
    change _ = scalar • (_ + _)
    rw [smul_add, smul_smul, smul_smul]

/-- Finite synthesis by the actual geometric Hopf eigenspinors. -/
def primitiveSpinCHopfFiniteZeroModeSynthesis :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter :=
  Finsupp.lsum Real
    (primitiveSpinCHopfZeroModeCoefficientLinearMap
      period hPeriod)

@[simp]
theorem primitiveSpinCHopfFiniteZeroModeSynthesis_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCHopfFiniteZeroModeSynthesis
        period hPeriod (Finsupp.single label coefficient) =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod label coefficient :=
  Finsupp.lsum_single Real
    (primitiveSpinCHopfZeroModeCoefficientLinearMap
      period hPeriod) label coefficient

theorem primitiveSpinCHopfZeroModeCoefficient_witness
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficient) =
      (2 : Real) •
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
            primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode +
          coefficient.im •
            primitiveSpinCHopfZeroModeImaginarySection
              period hPeriod sector mode) = _
  rw [map_add, map_smul, map_smul,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfImaginaryZeroMode_witness,
    d9PrimitiveSpinCImaginaryAction_normalModeDoubledLift]
  cases sector
  · apply Prod.ext
    · change
        coefficient.re •
              ((2 : Real) •
                normalRootMatterModeValue
                  period hPeriod .positiveQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) +
            coefficient.im •
              ((2 : Real) •
                normalRootScaledMatterModeValue
                  period hPeriod Complex.I .positiveQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) =
          (2 : Real) •
            normalRootScaledMatterModeValue
              period hPeriod coefficient .positiveQuarter mode
              (primitiveSpinCGeometricZeroModeWitnessCover
                period hPeriod time)
      calc
        _ = (2 : Real) •
            (coefficient.re •
                normalRootMatterModeValue
                  period hPeriod .positiveQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time) +
              coefficient.im •
                normalRootScaledMatterModeValue
                  period hPeriod Complex.I .positiveQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) := by module
        _ = _ := by
          rw [normalRootScaledMatterModeValue_eq_re_im]
    · change
        coefficient.re • ((2 : Real) • (0 : MatterFiber)) +
            coefficient.im • ((2 : Real) • (0 : MatterFiber)) =
          (2 : Real) • (0 : MatterFiber)
      simp
  · apply Prod.ext
    · change
        coefficient.re • ((2 : Real) • (0 : MatterFiber)) +
            coefficient.im • ((2 : Real) • (0 : MatterFiber)) =
          (2 : Real) • (0 : MatterFiber)
      simp
    · change
        coefficient.re •
              ((2 : Real) •
                normalRootMatterModeValue
                  period hPeriod .negativeQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) +
            coefficient.im •
              ((2 : Real) •
                normalRootScaledMatterModeValue
                  period hPeriod Complex.I .negativeQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) =
          (2 : Real) •
            normalRootScaledMatterModeValue
              period hPeriod coefficient .negativeQuarter mode
              (primitiveSpinCGeometricZeroModeWitnessCover
                period hPeriod time)
      calc
        _ = (2 : Real) •
            (coefficient.re •
                normalRootMatterModeValue
                  period hPeriod .negativeQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time) +
              coefficient.im •
                normalRootScaledMatterModeValue
                  period hPeriod Complex.I .negativeQuarter mode
                  (primitiveSpinCGeometricZeroModeWitnessCover
                    period hPeriod time)) := by module
        _ = _ := by
          rw [normalRootScaledMatterModeValue_eq_re_im]

/-- Equatorial Fourier analysis of a finite packet of actual Hopf
eigenspinors. -/
def primitiveSpinCHopfZeroModeWitnessAnalysis
    (sector : NormalRootChoice) (time : Real) :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real] Complex :=
  (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
    sector).comp
    ((primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCGeometricZeroModeWitnessIndex
        period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time)).comp
      (primitiveSpinCHopfFiniteZeroModeSynthesis
        period hPeriod))

theorem primitiveSpinCHopfZeroModeWitnessAnalysis_single
    (target source : NormalRootChoice)
    (mode : Int) (coefficient : Complex) (time : Real) :
    primitiveSpinCHopfZeroModeWitnessAnalysis
        period hPeriod target time
        (Finsupp.single (source, mode) coefficient) =
      if source = target then
        (2 : Real) •
          (coefficient *
            normalRootSpinFrameExponential period source mode time)
      else 0 := by
  rw [primitiveSpinCHopfZeroModeWitnessAnalysis,
    LinearMap.comp_apply, LinearMap.comp_apply,
    primitiveSpinCHopfFiniteZeroModeSynthesis_single,
    primitiveSpinCHopfZeroModeCoefficient_witness,
    map_smul,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_scaledMode]
  by_cases hSector : source = target
  · simp only [if_pos hSector]
    rw [← normalRootSpinFrameExponential_eq_phase
      period hPeriod source mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time)]
    simp
  · simp [hSector]

/-- Hopf witness analysis is ordinary finite Fourier synthesis multiplied
by the nonzero equatorial normalization `2`. -/
theorem primitiveSpinCHopfZeroModeWitnessAnalysis_eq
    (sector : NormalRootChoice) (time : Real) :
    primitiveSpinCHopfZeroModeWitnessAnalysis
        period hPeriod sector time =
      (2 : Real) •
        ((normalRootSpinFrameFinsuppPacketLinearMap
          period sector time).comp
          (primitiveSpinCGeometricZeroModeSectorRestriction sector)) := by
  apply Finsupp.lhom_ext
  intro label coefficient
  rcases label with ⟨source, mode⟩
  rw [primitiveSpinCHopfZeroModeWitnessAnalysis_single,
    LinearMap.smul_apply, LinearMap.comp_apply,
    primitiveSpinCGeometricZeroModeSectorRestriction_single]
  by_cases hSector : source = sector
  · subst source
    simp only [if_true]
    rw [normalRootSpinFrameFinsuppPacketLinearMap_single]
  · simp [hSector]

theorem primitiveSpinCHopfZeroModeWitnessAnalysis_apply
    (sector : NormalRootChoice) (time : Real)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCHopfZeroModeWitnessAnalysis
        period hPeriod sector time coefficients =
      (2 : Real) •
        normalRootSpinFrameFinsuppPacketLinearMap
          period sector time
          (primitiveSpinCGeometricZeroModeSectorRestriction
            sector coefficients) := by
  exact LinearMap.congr_fun
    (primitiveSpinCHopfZeroModeWitnessAnalysis_eq
      period hPeriod sector time) coefficients

/-- Finite synthesis by the actual Hopf eigenspinors is faithful. -/
theorem primitiveSpinCHopfFiniteZeroModeSynthesis_injective :
    Function.Injective
      (primitiveSpinCHopfFiniteZeroModeSynthesis
        period hPeriod) := by
  intro first second hEqual
  have hSector (sector : NormalRootChoice) :
      primitiveSpinCGeometricZeroModeSectorRestriction sector first =
        primitiveSpinCGeometricZeroModeSectorRestriction sector second := by
    apply normalRootSpinFrameFinsuppPacketFunctionLinearMap_injective
      period hPeriod sector
    funext time
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
    change
      primitiveSpinCHopfZeroModeWitnessAnalysis
          period hPeriod sector time first =
        primitiveSpinCHopfZeroModeWitnessAnalysis
          period hPeriod sector time second at hLocal
    rw [primitiveSpinCHopfZeroModeWitnessAnalysis_apply,
      primitiveSpinCHopfZeroModeWitnessAnalysis_apply] at hLocal
    calc
      normalRootSpinFrameFinsuppPacketLinearMap
          period sector time
          (primitiveSpinCGeometricZeroModeSectorRestriction sector first) =
        (1 / 2 : Real) •
          ((2 : Real) •
            normalRootSpinFrameFinsuppPacketLinearMap
              period sector time
              (primitiveSpinCGeometricZeroModeSectorRestriction
                sector first)) := by
          rw [smul_smul]
          norm_num
      _ = (1 / 2 : Real) •
          ((2 : Real) •
            normalRootSpinFrameFinsuppPacketLinearMap
              period sector time
              (primitiveSpinCGeometricZeroModeSectorRestriction
                sector second)) := by rw [hLocal]
      _ = normalRootSpinFrameFinsuppPacketLinearMap
          period sector time
          (primitiveSpinCGeometricZeroModeSectorRestriction
            sector second) := by
          rw [smul_smul]
          norm_num
  apply Finsupp.ext
  intro label
  rcases label with ⟨sector, mode⟩
  have hMode := congrArg
    (fun coefficients : Int →₀ Complex => coefficients mode)
    (hSector sector)
  simpa only [
    primitiveSpinCGeometricZeroModeSectorRestriction_apply]
    using hMode

theorem d9PrimitiveSpinCComplexAction_commutes_phase
    (scalar : Complex) (phase : Circle)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  change
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCComplexActionCLM (phase : Complex) matter) =
      d9PrimitiveSpinCComplexActionCLM (phase : Complex)
        (d9PrimitiveSpinCComplexActionCLM scalar matter)
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul, mul_comm]

theorem d9PrimitiveSpinCCoordChange_complexAction
    (choice : NormalRootChoice) (scalar : Complex)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCCoordChange period hPeriod choice first second base
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice first second base matter) := by
  unfold d9PrimitiveSpinCCoordChange
  simp only [ContinuousLinearMap.comp_apply,
    d9DoubledMatterSpinorMonodromyCLM_apply]
  rw [← d9PrimitiveSpinCComplexAction_monodromy]
  exact
    (d9PrimitiveSpinCComplexAction_commutes_phase
      scalar
      (d9PrimitiveSpinCPhaseTransition
        period hPeriod first.2 second.2 base)
      (d9DoubledMatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first.1 second.1 base)
        matter)).symm

/-- Constant complex multiplication of every local representative. -/
def d9PrimitiveSpinCComplexLocalGaugeFamily
    (choice : NormalRootChoice) (scalar : Complex)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base :=
    d9PrimitiveSpinCComplexActionCLM scalar
      (family.localValue index base)
  contMDiffOn_localValue index :=
    (d9PrimitiveSpinCComplexActionCLM scalar).contDiff.contMDiff
      |>.comp_contMDiffOn (family.contMDiffOn_localValue index)
  coordChange_localValue first second base hBase := by
    rw [d9PrimitiveSpinCCoordChange_complexAction,
      family.coordChange_localValue first second base hBase]

@[simp]
theorem d9PrimitiveSpinCComplexLocalGaugeFamily_localValue
    (choice : NormalRootChoice) (scalar : Complex)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCComplexLocalGaugeFamily
      period hPeriod choice scalar family).localValue index base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (family.localValue index base) :=
  rfl

theorem d9PrimitiveSpinCLocalFlatFrameDerivative_complexAction
    (choice : NormalRootChoice) (scalar : Complex)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCComplexLocalGaugeFamily
          period hPeriod choice scalar family)
        index direction base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family index direction base) := by
  let field := family.localValue index
  let tangent :=
    d9IntrinsicThroatFrame period hPeriod direction base
  have hField :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) field base :=
    ((family.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hOuter :
      MDifferentiableAt
        𝓘(Real, D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        (d9PrimitiveSpinCComplexActionCLM scalar) (field base) :=
    (d9PrimitiveSpinCComplexActionCLM scalar)
      |>.differentiableAt.mdifferentiableAt
  have hChain :=
    mfderiv_comp_apply base hOuter hField tangent
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (d9PrimitiveSpinCComplexActionCLM scalar ∘ field)
        base tangent =
      d9PrimitiveSpinCComplexActionCLM scalar
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) field base tangent)
  exact hChain

theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_complexAction
    (scalar : Complex) (direction : Fin 3)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base matter) := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte, map_smul]
    rw [d9PrimitiveSpinCComplexAction_clifford,
      d9PrimitiveSpinCComplexAction_clifford]

theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_complexAction
    (choice : NormalRootChoice) (scalar : Complex)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCComplexLocalGaugeFamily
          period hPeriod choice scalar family)
        index direction base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family index direction base) := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_complexAction
      (hBase := hBase),
    d9PrimitiveSpinCComplexLocalGaugeFamily_localValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_complexAction]
  exact
    (map_add (d9PrimitiveSpinCComplexActionCLM scalar) _ _).symm

theorem d9PrimitiveSpinCComplexAction_imaginary
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  change
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCComplexActionCLM Complex.I matter) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (d9PrimitiveSpinCComplexActionCLM scalar matter)
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul, mul_comm]

theorem d9PrimitiveSpinCLocalGeometricDirac_complexAction
    (choice : NormalRootChoice) (scalar : Complex)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice
        (d9PrimitiveSpinCComplexLocalGaugeFamily
          period hPeriod choice scalar family)
        index base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family index base) := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  simp only
  rw [d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_complexAction
      (hBase := hBase),
    d9PrimitiveSpinCComplexLocalGaugeFamily_localValue]
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
  simp only [d9PrimitiveSpinCComplexAction_clifford,
    map_add, map_smul, d9PrimitiveSpinCComplexAction_imaginary]

/-- Constant complex multiple of one actual global Hopf eigenspinor. -/
def primitiveSpinCHopfZeroModeComplexSection
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (d9PrimitiveSpinCComplexLocalGaugeFamily
    period hPeriod .positiveQuarter coefficient
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode)).toSmoothSection
        period hPeriod .positiveQuarter

theorem primitiveSpinCHopfZeroModeComplexGeometricDiracOperator_eigen
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeComplexSection
          period hPeriod coefficient sector mode) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        primitiveSpinCHopfZeroModeComplexSection
          period hPeriod coefficient sector mode := by
  let family :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let complexFamily :=
    d9PrimitiveSpinCComplexLocalGaugeFamily
      period hPeriod .positiveQuarter coefficient family
  rw [show
      primitiveSpinCHopfZeroModeComplexSection
          period hPeriod coefficient sector mode =
        complexFamily.toSmoothSection
          period hPeriod .positiveQuarter by rfl]
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  ext base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  let point :=
    normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    exact core.mem_baseSet_at base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    hBase.2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hLocal :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter complexFamily
        (point, chart) base =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        complexFamily.localValue (point, chart) base
  rw [d9PrimitiveSpinCLocalGeometricDirac_complexAction
      (hBase := hBase)]
  change
    d9PrimitiveSpinCComplexActionCLM coefficient
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter family
          (point, chart) base) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        d9PrimitiveSpinCComplexActionCLM coefficient
          (family.localValue (point, chart) base)
  rw [← hProject, hLocal, map_smul]

/-- Decomposition of transported complex multiplication into its two real
generators. -/
theorem d9PrimitiveSpinCComplexAction_eq_re_im
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar matter =
      scalar.re • matter +
        scalar.im • d9PrimitiveSpinCImaginaryAction matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_add, map_smul, map_smul]
  change
    scalar • d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
      scalar.re • d9DoubledMatterFiberHalfSpinorLinearEquiv matter +
        scalar.im •
          d9DoubledMatterFiberHalfSpinorLinearEquiv
            (d9PrimitiveSpinCPhaseActionCLM
              d9PrimitiveSpinCImaginaryPhase matter)
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe]
  apply Prod.ext
  · funext index
    change
      scalar *
          (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).1 index =
        (scalar.re : Complex) *
              (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).1 index +
          (scalar.im : Complex) *
            (Complex.I *
              (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).1 index)
    apply Complex.ext <;> simp <;> ring
  · funext index
    change
      scalar *
          (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).2 index =
        (scalar.re : Complex) *
              (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).2 index +
          (scalar.im : Complex) *
            (Complex.I *
              (d9DoubledMatterFiberHalfSpinorLinearEquiv matter).2 index)
    apply Complex.ext <;> simp <;> ring

theorem primitiveSpinCHopfZeroModeCoefficientLinearMap_eq_complexSection
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod label coefficient =
      primitiveSpinCHopfZeroModeComplexSection
        period hPeriod coefficient label.1 label.2 := by
  ext base
  change
    coefficient.re •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod label.1 label.2).localValue
            ((d9PrimitiveSpinCVectorBundleCore
              period hPeriod .positiveQuarter).indexAt base) base +
        coefficient.im •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod label.1 label.2).localValue
              ((d9PrimitiveSpinCVectorBundleCore
                period hPeriod .positiveQuarter).indexAt base) base) =
      d9PrimitiveSpinCComplexActionCLM coefficient
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod label.1 label.2).localValue
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod .positiveQuarter).indexAt base) base)
  exact
    (d9PrimitiveSpinCComplexAction_eq_re_im coefficient _).symm

/-- Every complex coefficient on one Hopf mode satisfies the actual
first-order geometric Dirac eigen-equation. -/
theorem primitiveSpinCHopfZeroModeCoefficientGeometricDiracOperator_eigen
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod label coefficient) =
      -normalRootLeviCivitaCorrectedFrequency
          period label.1 label.2 •
        primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod label coefficient := by
  rw [
    primitiveSpinCHopfZeroModeCoefficientLinearMap_eq_complexSection]
  exact
    primitiveSpinCHopfZeroModeComplexGeometricDiracOperator_eigen
      period hPeriod coefficient label.1 label.2

@[simp]
theorem d9PrimitiveSpinCAddLocalGaugeFamily_localValue
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCAddLocalGaugeFamily
      period hPeriod first second).localValue index base =
      first.localValue index base + second.localValue index base :=
  rfl

theorem d9PrimitiveSpinCLocalFlatFrameDerivative_add
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCAddLocalGaugeFamily
          period hPeriod first second)
        index direction base =
      d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod .positiveQuarter first index direction base +
        d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod .positiveQuarter second index direction base := by
  have hFirst :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (first.localValue index) base :=
    ((first.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hSecond :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (second.localValue index) base :=
    ((second.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  have hFunction :
      (d9PrimitiveSpinCAddLocalGaugeFamily
        period hPeriod first second).localValue index =
        first.localValue index + second.localValue index := by
    funext current
    rfl
  rw [hFunction, mfderiv_add hFirst hSecond]
  rfl

theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_add
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base (first + second) =
      d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base first +
        d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base second := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte, map_add, smul_add]

theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_add
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCAddLocalGaugeFamily
          period hPeriod first second)
        index direction base =
      d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter first index direction base +
        d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter second index direction base := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_add
      (hBase := hBase),
    d9PrimitiveSpinCAddLocalGaugeFamily_localValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_add]
  abel

theorem d9PrimitiveSpinCLocalGeometricDirac_add
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCAddLocalGaugeFamily
          period hPeriod first second)
        index base =
      d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter first index base +
        d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter second index base := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  calc
    _ = ∑ direction : Fin 3,
        (d9DoubledMatterFiberCliffordGammaCLM direction
            (d9PrimitiveSpinCLocalDirectionalDerivative
              (d9PrimitiveSpinCTotalConnectionFrameCoefficient
                period hPeriod index.2 direction base)
              (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
                period hPeriod .positiveQuarter first
                index direction base)
              (first.localValue index base)) +
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9PrimitiveSpinCLocalDirectionalDerivative
              (d9PrimitiveSpinCTotalConnectionFrameCoefficient
                period hPeriod index.2 direction base)
              (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
                period hPeriod .positiveQuarter second
                index direction base)
              (second.localValue index base))) := by
        apply Finset.sum_congr rfl
        intro direction _
        simp only
        rw [d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_add
          (hBase := hBase)]
        simp only [d9PrimitiveSpinCAddLocalGaugeFamily_localValue,
          d9PrimitiveSpinCLocalDirectionalDerivative,
          map_add, smul_add]
        abel
    _ = _ := Finset.sum_add_distrib

theorem d9PrimitiveSpinCGeometricDiracSection_add
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter) :
    d9PrimitiveSpinCGeometricDiracSection
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCAddLocalGaugeFamily
          period hPeriod first second) =
      d9PrimitiveSpinCGeometricDiracSection
          period hPeriod .positiveQuarter first +
        d9PrimitiveSpinCGeometricDiracSection
          period hPeriod .positiveQuarter second := by
  ext base
  change
    d9PrimitiveSpinCGeometricDiracSection
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCAddLocalGaugeFamily
          period hPeriod first second) base =
      d9PrimitiveSpinCGeometricDiracSection
          period hPeriod .positiveQuarter first base +
        d9PrimitiveSpinCGeometricDiracSection
          period hPeriod .positiveQuarter second base
  rw [d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCGeometricDiracSection_apply]
  exact d9PrimitiveSpinCLocalGeometricDirac_add
    period hPeriod first second
    ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter).indexAt base)
    base
    ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter).mem_baseSet_at base)

/-- The genuine descended geometric Dirac operator is additive on the
whole smooth primitive SpinC core. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_add
    (first second :
      D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter (first + second) =
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter first +
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter second := by
  let firstFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod .positiveQuarter first
  let secondFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod .positiveQuarter second
  let sumFamily :=
    d9PrimitiveSpinCAddLocalGaugeFamily
      period hPeriod firstFamily secondFamily
  have hSumSection :
      sumFamily.toSmoothSection period hPeriod .positiveQuarter =
        first + second := by
    calc
      _ =
          firstFamily.toSmoothSection
              period hPeriod .positiveQuarter +
            secondFamily.toSmoothSection
              period hPeriod .positiveQuarter := by
          ext base
          rfl
      _ = first + second := by
        rw [
          d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection,
          d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection]
  rw [← hSumSection,
    d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection,
    d9PrimitiveSpinCGeometricDiracSection_add]
  rfl

theorem d9PrimitiveSpinCGeometricDiracOperator_zero :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter 0 = 0 := by
  have hAdd :=
    d9PrimitiveSpinCGeometricDiracOperator_add
      period hPeriod
      (0 :
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)
      0
  simp only [zero_add] at hAdd
  have hCancel := congrArg
    (fun state :
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter =>
      state -
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter 0)
    hAdd
  simpa only [sub_self, add_sub_cancel_left] using hCancel.symm

/-- One first-order Dirac eigenvalue block on finite Hopf coefficients. -/
def primitiveSpinCHopfFiniteZeroModeDiracCoefficientBlock
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Real]
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  (Finsupp.lsingle label).comp
    ((-normalRootLeviCivitaCorrectedFrequency
        period label.1 label.2) •
      (LinearMap.id : Complex →ₗ[Real] Complex))

/-- First-order diagonal Dirac operator on finite Hopf coefficients. -/
def primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real]
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  Finsupp.lsum Real fun label =>
    primitiveSpinCHopfFiniteZeroModeDiracCoefficientBlock
      period label

@[simp]
theorem primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
        period (Finsupp.single label coefficient) =
      -normalRootLeviCivitaCorrectedFrequency
          period label.1 label.2 •
        Finsupp.single label coefficient := by
  simp [primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator,
    primitiveSpinCHopfFiniteZeroModeDiracCoefficientBlock]

/-- The actual geometric Dirac operator intertwines finite Hopf synthesis
with the explicit first-order diagonal coefficient operator. -/
theorem primitiveSpinCHopfFiniteZeroModeSynthesis_intertwines_dirac
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFiniteZeroModeSynthesis
          period hPeriod coefficients) =
      primitiveSpinCHopfFiniteZeroModeSynthesis
        period hPeriod
        (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
          period coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp only [map_zero]
      exact d9PrimitiveSpinCGeometricDiracOperator_zero
        period hPeriod
  | single_add label coefficient rest hCoefficient hLabel ih =>
      calc
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfFiniteZeroModeSynthesis
              period hPeriod
              (Finsupp.single label coefficient + rest)) =
          d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfFiniteZeroModeSynthesis
                period hPeriod (Finsupp.single label coefficient) +
              primitiveSpinCHopfFiniteZeroModeSynthesis
                period hPeriod rest) := by rw [map_add]
        _ =
            d9PrimitiveSpinCGeometricDiracOperator
                period hPeriod .positiveQuarter
                (primitiveSpinCHopfFiniteZeroModeSynthesis
                  period hPeriod (Finsupp.single label coefficient)) +
              d9PrimitiveSpinCGeometricDiracOperator
                period hPeriod .positiveQuarter
                (primitiveSpinCHopfFiniteZeroModeSynthesis
                  period hPeriod rest) :=
          d9PrimitiveSpinCGeometricDiracOperator_add
            period hPeriod _ _
        _ =
            -normalRootLeviCivitaCorrectedFrequency
                  period label.1 label.2 •
                primitiveSpinCHopfZeroModeCoefficientLinearMap
                  period hPeriod label coefficient +
              primitiveSpinCHopfFiniteZeroModeSynthesis
                period hPeriod
                (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
                  period rest) := by
          rw [primitiveSpinCHopfFiniteZeroModeSynthesis_single,
            primitiveSpinCHopfZeroModeCoefficientGeometricDiracOperator_eigen,
            ih]
        _ =
            primitiveSpinCHopfFiniteZeroModeSynthesis
                period hPeriod
                (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
                  period (Finsupp.single label coefficient)) +
              primitiveSpinCHopfFiniteZeroModeSynthesis
                period hPeriod
                (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
                  period rest) := by
          rw [
            primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_single,
            map_smul,
            primitiveSpinCHopfFiniteZeroModeSynthesis_single]
        _ =
            primitiveSpinCHopfFiniteZeroModeSynthesis
              period hPeriod
              (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
                period (Finsupp.single label coefficient + rest)) := by
          rw [map_add, map_add]

/-- Consolidated first-order closure of the complete geometric Hopf
zero-mode tower. -/
theorem primitiveSpinCHopfZeroModeSpectralRealization_closed :
    Function.Injective
        (primitiveSpinCHopfFiniteZeroModeSynthesis
          period hPeriod) ∧
      (∀ label : PrimitiveSpinCGeometricZeroModeLabel,
        ∀ coefficient : Complex,
          d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter
              (primitiveSpinCHopfZeroModeCoefficientLinearMap
                period hPeriod label coefficient) =
            -normalRootLeviCivitaCorrectedFrequency
                period label.1 label.2 •
              primitiveSpinCHopfZeroModeCoefficientLinearMap
                period hPeriod label coefficient) ∧
      (∀ coefficients :
          PrimitiveSpinCGeometricFiniteZeroModeCoefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfFiniteZeroModeSynthesis
              period hPeriod coefficients) =
          primitiveSpinCHopfFiniteZeroModeSynthesis
            period hPeriod
            (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
              period coefficients)) :=
  ⟨primitiveSpinCHopfFiniteZeroModeSynthesis_injective
      period hPeriod,
    primitiveSpinCHopfZeroModeCoefficientGeometricDiracOperator_eigen
      period hPeriod,
    primitiveSpinCHopfFiniteZeroModeSynthesis_intertwines_dirac
      period hPeriod⟩

/-- Squaring the first-order coefficient diagonal gives exactly the
pre-existing geometric/Hilbert squared diagonal. -/
theorem primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_sq
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator period
        (primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator
          period coefficients) =
      primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
        period hPeriod coefficients := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add label coefficient rest hCoefficient hLabel ih =>
      rw [map_add, map_add, map_add, ih]
      congr 1
      rw [
        primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_single,
        map_smul,
        primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_single,
        primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator_single,
        smul_smul,
        primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue_eq,
        ← normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
          period hPeriod label.1 label.2]
      ring

/-- On every finite Hopf packet, the square of the actual differential
Dirac operator is the canonical squared spectral operator already used by
the Hilbert completion. -/
theorem primitiveSpinCHopfFiniteZeroModeSynthesis_intertwines_dirac_sq
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFiniteZeroModeSynthesis
            period hPeriod coefficients)) =
      primitiveSpinCHopfFiniteZeroModeSynthesis
        period hPeriod
        (primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
          period hPeriod coefficients) := by
  rw [
    primitiveSpinCHopfFiniteZeroModeSynthesis_intertwines_dirac,
    primitiveSpinCHopfFiniteZeroModeSynthesis_intertwines_dirac,
    primitiveSpinCHopfFiniteZeroModeDiracCoefficientOperator_sq]

end
end P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
end JanusFormal
