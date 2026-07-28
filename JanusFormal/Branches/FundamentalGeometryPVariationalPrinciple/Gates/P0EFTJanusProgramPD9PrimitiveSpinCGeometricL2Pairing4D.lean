import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorRealDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

/-!
# Intrinsic geometric L2 pairing on primitive SpinC sections

The standard positive Hermitian pairing on the doubled half-spinor fiber is
preserved by both factors of every primitive SpinC transition: normal-root
monodromy and primitive monopole phase.  It therefore gives a smooth,
trivialization-independent pointwise pairing on genuine smooth sections.

Integrating against the already constructed canonical throat volume defines
an independent geometric `L2` pairing.  Positivity and nondegeneracy use full
support of that measure, not spectral coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D

set_option autoImplicit false
noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Bundle BigOperators ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9MatterSpinorRealDensity4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseCompactSpace :
    CompactSpace (ThroatBase period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) :=
  borel _

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatFiniteMeasure :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatOpenPosMeasure :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Positive Hermitian pairing on the doubled real matter fiber. -/
def d9DoubledMatterSpinorHermitianPairing
    (first second : D9DoubledMatterFiber) : Complex :=
  d9MatterSpinorHermitianPairing first.1 second.1 +
    d9MatterSpinorHermitianPairing first.2 second.2

private theorem ambientHalfSpinorHermitianPairing_circle_smul
    (phase : _root_.Circle) (first second : AmbientHalfSpinor2) :
    ambientHalfSpinorHermitianPairing
        ((phase : Complex) • first)
        ((phase : Complex) • second) =
      ambientHalfSpinorHermitianPairing first second := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing,
    ambientHalfSpinorEmbed, Fin.sum_univ_succ]
  have hPhase :
      (starRingEnd Complex) (phase : Complex) *
          (phase : Complex) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
    simp
  rw [show
      (starRingEnd Complex) (phase : Complex) *
            (starRingEnd Complex) (first 0) *
            ((phase : Complex) * second 0) =
        ((starRingEnd Complex) (phase : Complex) *
            (phase : Complex)) *
          ((starRingEnd Complex) (first 0) * second 0) by ring,
    show
      (starRingEnd Complex) (phase : Complex) *
            (starRingEnd Complex) (first 1) *
            ((phase : Complex) * second 1) =
        ((starRingEnd Complex) (phase : Complex) *
            (phase : Complex)) *
          ((starRingEnd Complex) (first 1) * second 1) by ring,
    hPhase]
  simp

private theorem ambientHalfSpinorHermitianPairing_smul_left
    (scalar : Complex) (first second : AmbientHalfSpinor2) :
    ambientHalfSpinorHermitianPairing
        (scalar • first) second =
      (starRingEnd Complex) scalar *
        ambientHalfSpinorHermitianPairing first second := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing,
    ambientHalfSpinorEmbed, Fin.sum_univ_succ]
  ring

private theorem ambientHalfSpinorHermitianPairing_smul_right
    (scalar : Complex) (first second : AmbientHalfSpinor2) :
    ambientHalfSpinorHermitianPairing
        first (scalar • second) =
      scalar * ambientHalfSpinorHermitianPairing first second := by
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing,
    ambientHalfSpinorEmbed, Fin.sum_univ_succ]
  ring

theorem d9DoubledMatterSpinorHermitianPairing_phaseAction
    (phase : _root_.Circle) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCPhaseActionCLM phase left)
        (d9PrimitiveSpinCPhaseActionCLM phase right) =
      d9DoubledMatterSpinorHermitianPairing left right := by
  have hLeft :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction
      phase left
  have hRight :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction
      phase right
  have hLeftFirst :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCPhaseActionCLM phase left).1 =
        (phase : Complex) •
          matterFiberHalfSpinorLinearEquiv left.1 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hLeft
  have hLeftSecond :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCPhaseActionCLM phase left).2 =
        (phase : Complex) •
          matterFiberHalfSpinorLinearEquiv left.2 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hLeft
  have hRightFirst :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCPhaseActionCLM phase right).1 =
        (phase : Complex) •
          matterFiberHalfSpinorLinearEquiv right.1 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hRight
  have hRightSecond :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCPhaseActionCLM phase right).2 =
        (phase : Complex) •
          matterFiberHalfSpinorLinearEquiv right.2 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hRight
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  rw [hLeftFirst, hRightFirst, hLeftSecond, hRightSecond,
    ambientHalfSpinorHermitianPairing_circle_smul,
    ambientHalfSpinorHermitianPairing_circle_smul]

theorem d9DoubledMatterSpinorHermitianPairing_complexAction_left
    (scalar : Complex) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCComplexActionCLM scalar left) right =
      (starRingEnd Complex) scalar *
        d9DoubledMatterSpinorHermitianPairing left right := by
  have hLeft :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction
      scalar left
  have hLeftFirst :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCComplexActionCLM scalar left).1 =
        scalar • matterFiberHalfSpinorLinearEquiv left.1 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hLeft
  have hLeftSecond :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCComplexActionCLM scalar left).2 =
        scalar • matterFiberHalfSpinorLinearEquiv left.2 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hLeft
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  rw [hLeftFirst, hLeftSecond,
    ambientHalfSpinorHermitianPairing_smul_left,
    ambientHalfSpinorHermitianPairing_smul_left]
  ring

theorem d9DoubledMatterSpinorHermitianPairing_complexAction_right
    (scalar : Complex) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        left (d9PrimitiveSpinCComplexActionCLM scalar right) =
      scalar * d9DoubledMatterSpinorHermitianPairing left right := by
  have hRight :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction
      scalar right
  have hRightFirst :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCComplexActionCLM scalar right).1 =
        scalar • matterFiberHalfSpinorLinearEquiv right.1 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hRight
  have hRightSecond :
      matterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCComplexActionCLM scalar right).2 =
        scalar • matterFiberHalfSpinorLinearEquiv right.2 := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hRight
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  rw [hRightFirst, hRightSecond,
    ambientHalfSpinorHermitianPairing_smul_right,
    ambientHalfSpinorHermitianPairing_smul_right]
  ring

theorem d9PrimitiveSpinCComplexActionCLM_eq_re_add_im
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar matter =
      scalar.re • matter +
        scalar.im • d9PrimitiveSpinCImaginaryAction matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp only [map_add, map_smul]
  have hImaginary :
      d9DoubledMatterFiberHalfSpinorLinearEquiv
          (d9PrimitiveSpinCImaginaryAction matter) =
        Complex.I •
          d9DoubledMatterFiberHalfSpinorLinearEquiv matter := by
    unfold d9PrimitiveSpinCImaginaryAction
    rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
      d9PrimitiveSpinCImaginaryPhase_coe]
  rw [hImaginary,
    RCLike.real_smul_eq_coe_smul (K := Complex),
    RCLike.real_smul_eq_coe_smul (K := Complex),
    smul_smul, ← add_smul]
  exact congrArg
    (fun coefficient : Complex =>
      coefficient •
        d9DoubledMatterFiberHalfSpinorLinearEquiv matter)
    (Complex.re_add_im scalar).symm

theorem d9DoubledMatterSpinorHermitianPairing_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (anchor : MappingTorusCover (ThroatData period hPeriod))
    (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterSpinorMonodromy choice winding left)
        (d9DoubledMatterSpinorMonodromy choice winding right) =
      d9DoubledMatterSpinorHermitianPairing left right := by
  unfold d9DoubledMatterSpinorHermitianPairing
    d9DoubledMatterSpinorMonodromy
  rw [d9MatterSpinorMonodromy_preserves_pairing
      period hPeriod choice winding anchor,
    d9MatterSpinorMonodromy_preserves_pairing
      period hPeriod (oppositeRoot choice) winding anchor]

theorem d9DoubledMatterSpinorHermitianPairing_self_re_nonnegative
    (matter : D9DoubledMatterFiber) :
    0 ≤
      (d9DoubledMatterSpinorHermitianPairing
        matter matter).re := by
  unfold d9DoubledMatterSpinorHermitianPairing
  rw [Complex.add_re]
  exact add_nonneg
    (d9MatterSpinorHermitianPairing_self_re_nonnegative matter.1)
    (d9MatterSpinorHermitianPairing_self_re_nonnegative matter.2)

private theorem d9MatterSpinorHermitianPairing_self_re_eq_zero_iff
    (matter : MatterFiber) :
    (d9MatterSpinorHermitianPairing matter matter).re = 0 ↔
      matter = 0 := by
  let first :=
    matterFiberHalfSpinorLinearEquiv matter 0
  let second :=
    matterFiberHalfSpinorLinearEquiv matter 1
  have hFormula :
      (d9MatterSpinorHermitianPairing matter matter).re =
        Complex.normSq first + Complex.normSq second := by
    rw [d9MatterSpinorHermitianPairing_eq_two_coordinates,
      ← Complex.normSq_eq_conj_mul_self,
      ← Complex.normSq_eq_conj_mul_self]
    rfl
  constructor
  · intro hZero
    have hSum :
        Complex.normSq first + Complex.normSq second = 0 := by
      rw [← hFormula]
      exact hZero
    have hFirst : first = 0 := by
      apply Complex.normSq_eq_zero.mp
      nlinarith [Complex.normSq_nonneg first,
        Complex.normSq_nonneg second]
    have hSecond : second = 0 := by
      apply Complex.normSq_eq_zero.mp
      nlinarith [Complex.normSq_nonneg first,
        Complex.normSq_nonneg second]
    apply matterFiberHalfSpinorLinearEquiv.injective
    funext index
    fin_cases index
    · exact hFirst
    · exact hSecond
  · rintro rfl
    rw [d9MatterSpinorHermitianPairing_eq_two_coordinates]
    simp

theorem d9DoubledMatterSpinorHermitianPairing_self_re_eq_zero_iff
    (matter : D9DoubledMatterFiber) :
    (d9DoubledMatterSpinorHermitianPairing
      matter matter).re = 0 ↔ matter = 0 := by
  constructor
  · intro hZero
    have hFirstNonnegative :=
      d9MatterSpinorHermitianPairing_self_re_nonnegative matter.1
    have hSecondNonnegative :=
      d9MatterSpinorHermitianPairing_self_re_nonnegative matter.2
    have hSum :
        (d9MatterSpinorHermitianPairing
              matter.1 matter.1).re +
            (d9MatterSpinorHermitianPairing
              matter.2 matter.2).re = 0 := by
      simpa [d9DoubledMatterSpinorHermitianPairing]
        using hZero
    have hFirst :
        (d9MatterSpinorHermitianPairing
          matter.1 matter.1).re = 0 := by
      nlinarith
    have hSecond :
        (d9MatterSpinorHermitianPairing
          matter.2 matter.2).re = 0 := by
      nlinarith
    exact Prod.ext
      (d9MatterSpinorHermitianPairing_self_re_eq_zero_iff
        matter.1 |>.mp hFirst)
      (d9MatterSpinorHermitianPairing_self_re_eq_zero_iff
        matter.2 |>.mp hSecond)
  · rintro rfl
    simp [d9DoubledMatterSpinorHermitianPairing,
      d9MatterSpinorHermitianPairing_eq_two_coordinates]

private theorem d9MatterSpinorHermitianPairing_add_left
    (first second third : MatterFiber) :
    d9MatterSpinorHermitianPairing
        (first + second) third =
      d9MatterSpinorHermitianPairing first third +
        d9MatterSpinorHermitianPairing second third := by
  simp [d9MatterSpinorHermitianPairing_eq_two_coordinates,
    map_add]
  ring

private theorem d9MatterSpinorHermitianPairing_add_right
    (first second third : MatterFiber) :
    d9MatterSpinorHermitianPairing
        first (second + third) =
      d9MatterSpinorHermitianPairing first second +
        d9MatterSpinorHermitianPairing first third := by
  simp [d9MatterSpinorHermitianPairing_eq_two_coordinates,
    map_add]
  ring

private theorem d9MatterSpinorHermitianPairing_conj_symm
    (first second : MatterFiber) :
    (starRingEnd Complex)
        (d9MatterSpinorHermitianPairing first second) =
      d9MatterSpinorHermitianPairing second first := by
  rw [d9MatterSpinorHermitianPairing_eq_two_coordinates,
    d9MatterSpinorHermitianPairing_eq_two_coordinates]
  simp only [map_add, map_mul]
  simp
  ring

theorem d9DoubledMatterSpinorHermitianPairing_add_left
    (first second third : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (first + second) third =
      d9DoubledMatterSpinorHermitianPairing first third +
        d9DoubledMatterSpinorHermitianPairing second third := by
  simp only [d9DoubledMatterSpinorHermitianPairing,
    Prod.fst_add, Prod.snd_add,
    d9MatterSpinorHermitianPairing_add_left]
  abel

theorem d9DoubledMatterSpinorHermitianPairing_add_right
    (first second third : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        first (second + third) =
      d9DoubledMatterSpinorHermitianPairing first second +
        d9DoubledMatterSpinorHermitianPairing first third := by
  simp only [d9DoubledMatterSpinorHermitianPairing,
    Prod.fst_add, Prod.snd_add,
    d9MatterSpinorHermitianPairing_add_right]
  abel

theorem d9DoubledMatterSpinorHermitianPairing_conj_symm
    (first second : D9DoubledMatterFiber) :
    (starRingEnd Complex)
        (d9DoubledMatterSpinorHermitianPairing first second) =
      d9DoubledMatterSpinorHermitianPairing second first := by
  simp only [d9DoubledMatterSpinorHermitianPairing,
    map_add, d9MatterSpinorHermitianPairing_conj_symm]

theorem d9DoubledMatterSpinorHermitianPairing_coordChange
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice first second base left)
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice first second base right) =
      d9DoubledMatterSpinorHermitianPairing left right := by
  change
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod first.2 second.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              first.1 second.1 base) left))
        (d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod first.2 second.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              first.1 second.1 base) right)) =
      d9DoubledMatterSpinorHermitianPairing left right
  rw [d9DoubledMatterSpinorHermitianPairing_phaseAction]
  exact
    d9DoubledMatterSpinorHermitianPairing_monodromy
      period hPeriod choice
        (localTransitionWinding period hPeriod
          first.1 second.1 base)
        first.1 left right

private def matterToHalfSpinorCLM :
    MatterFiber →L[Real] AmbientHalfSpinor2 :=
  LinearMap.toContinuousLinearMap
    matterFiberHalfSpinorLinearEquiv.toLinearMap

private def halfSpinorCoordinateCLM (index : Fin 2) :
    AmbientHalfSpinor2 →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun spinor => spinor index
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem d9MatterSpinorHermitianPairing_comp_contMDiffAt
    (first second : ThroatBase period hPeriod → MatterFiber)
    (base : ThroatBase period hPeriod)
    (hFirst :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞ first base)
    (hSecond :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞ second base) :
    ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, Complex) ∞
      (fun point =>
        d9MatterSpinorHermitianPairing
          (first point) (second point)) base := by
  have hFirstHalf :=
    matterToHalfSpinorCLM.contMDiffAt.comp base hFirst
  have hSecondHalf :=
    matterToHalfSpinorCLM.contMDiffAt.comp base hSecond
  have hCoordinate (index : Fin 2) :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, Complex) ∞
        (fun point =>
          (starRingEnd Complex)
              (matterFiberHalfSpinorLinearEquiv
                (first point) index) *
            matterFiberHalfSpinorLinearEquiv
              (second point) index) base := by
    have hFirstCoordinate :=
      (halfSpinorCoordinateCLM index).contMDiffAt.comp
        base hFirstHalf
    have hSecondCoordinate :=
      (halfSpinorCoordinateCLM index).contMDiffAt.comp
        base hSecondHalf
    have hConj :=
      Complex.conjCLE.toContinuousLinearMap.contMDiffAt.comp
        base hFirstCoordinate
    have hMul :
        ContMDiffAt throatCoverModelWithCorners
          𝓘(Real, Complex →L[Real] Complex) ∞
          (fun point =>
            ContinuousLinearMap.mul Real Complex
              ((starRingEnd Complex)
                (matterFiberHalfSpinorLinearEquiv
                  (first point) index))) base :=
      (ContinuousLinearMap.mul Real Complex).contMDiffAt.comp
        base hConj
    exact hMul.clm_apply hSecondCoordinate
  convert (hCoordinate 0).add (hCoordinate 1) using 1
  funext point
  exact
    (d9MatterSpinorHermitianPairing_eq_two_coordinates
      (first point) (second point))

/-- Intrinsic pointwise pairing of two genuine smooth SpinC sections. -/
def d9PrimitiveSpinCPointwiseHermitianPairing
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) : Complex :=
  d9DoubledMatterSpinorHermitianPairing
    (show D9DoubledMatterFiber from first base)
    (show D9DoubledMatterFiber from second base)

/-- The intrinsic pairing may be computed in any common bundle
trivialization. -/
theorem d9PrimitiveSpinCPointwiseHermitianPairing_eq_coordChange
    (choice : NormalRootChoice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first second base =
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod choice).indexAt base)
          index base
          (show D9DoubledMatterFiber from first base))
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod choice).indexAt base)
          index base
          (show D9DoubledMatterFiber from second base)) := by
  exact
    (d9DoubledMatterSpinorHermitianPairing_coordChange
      period hPeriod choice
      ((d9PrimitiveSpinCVectorBundleCore
        period hPeriod choice).indexAt base)
      index base
      (show D9DoubledMatterFiber from first base)
      (show D9DoubledMatterFiber from second base)).symm

theorem d9PrimitiveSpinCComplexScalarSection_apply_complexAction
    (choice : NormalRootChoice) (scalar : Complex)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (show D9DoubledMatterFiber from state base) := by
  rw [d9PrimitiveSpinCComplexScalarSection_apply]
  exact
    (d9PrimitiveSpinCComplexActionCLM_eq_re_add_im
      scalar
      (show D9DoubledMatterFiber from state base)).symm

theorem d9PrimitiveSpinCPointwiseHermitianPairing_add_left
    (choice : NormalRootChoice)
    (first second third :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice (first + second) third base =
      d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first third base +
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice second third base :=
  d9DoubledMatterSpinorHermitianPairing_add_left
    (show D9DoubledMatterFiber from first base)
    (show D9DoubledMatterFiber from second base)
    (show D9DoubledMatterFiber from third base)

theorem d9PrimitiveSpinCPointwiseHermitianPairing_add_right
    (choice : NormalRootChoice)
    (first second third :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first (second + third) base =
      d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second base +
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first third base :=
  d9DoubledMatterSpinorHermitianPairing_add_right
    (show D9DoubledMatterFiber from first base)
    (show D9DoubledMatterFiber from second base)
    (show D9DoubledMatterFiber from third base)

theorem d9PrimitiveSpinCPointwiseHermitianPairing_conj_symm
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    (starRingEnd Complex)
        (d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second base) =
      d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice second first base :=
  d9DoubledMatterSpinorHermitianPairing_conj_symm
    (show D9DoubledMatterFiber from first base)
    (show D9DoubledMatterFiber from second base)

theorem d9PrimitiveSpinCPointwiseHermitianPairing_complexScalar_left
    (choice : NormalRootChoice) (scalar : Complex)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar first) second base =
      (starRingEnd Complex) scalar *
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second base := by
  rw [d9PrimitiveSpinCPointwiseHermitianPairing,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]
  exact
    d9DoubledMatterSpinorHermitianPairing_complexAction_left
      scalar
      (show D9DoubledMatterFiber from first base)
      (show D9DoubledMatterFiber from second base)

theorem d9PrimitiveSpinCPointwiseHermitianPairing_complexScalar_right
    (choice : NormalRootChoice) (scalar : Complex)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar second) base =
      scalar *
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second base := by
  rw [d9PrimitiveSpinCPointwiseHermitianPairing,
    d9PrimitiveSpinCComplexScalarSection_apply_complexAction]
  exact
    d9DoubledMatterSpinorHermitianPairing_complexAction_right
      scalar
      (show D9DoubledMatterFiber from first base)
      (show D9DoubledMatterFiber from second base)

theorem d9PrimitiveSpinCPointwiseHermitianPairing_contMDiff
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first second) := by
  intro base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice
  let localFirst :
      ThroatBase period hPeriod → D9DoubledMatterFiber :=
    fun point =>
      ((trivializationAt D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice) base)
          ⟨point, first point⟩).2
  let localSecond :
      ThroatBase period hPeriod → D9DoubledMatterFiber :=
    fun point =>
      ((trivializationAt D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice) base)
          ⟨point, second point⟩).2
  have hFirstLocal :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        localFirst base := by
    rw [show localFirst =
        fun point =>
          ((trivializationAt D9DoubledMatterFiber
            (D9PrimitiveSpinCFiber period hPeriod choice) base)
              ⟨point, first point⟩).2 by rfl]
    exact
      (contMDiffAt_section base).mp
        (first.contMDiff base)
  have hSecondLocal :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        localSecond base := by
    rw [show localSecond =
        fun point =>
          ((trivializationAt D9DoubledMatterFiber
            (D9PrimitiveSpinCFiber period hPeriod choice) base)
              ⟨point, second point⟩).2 by rfl]
    exact
      (contMDiffAt_section base).mp
        (second.contMDiff base)
  have hFirstFirst :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞
        (fun point => (localFirst point).1) base :=
    (ContinuousLinearMap.fst Real
      MatterFiber MatterFiber).contMDiffAt.comp
        base hFirstLocal
  have hSecondFirst :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞
        (fun point => (localSecond point).1) base :=
    (ContinuousLinearMap.fst Real
      MatterFiber MatterFiber).contMDiffAt.comp
        base hSecondLocal
  have hFirstSecond :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞
        (fun point => (localFirst point).2) base :=
    (ContinuousLinearMap.snd Real
      MatterFiber MatterFiber).contMDiffAt.comp
        base hFirstLocal
  have hSecondSecond :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) ∞
        (fun point => (localSecond point).2) base :=
    (ContinuousLinearMap.snd Real
      MatterFiber MatterFiber).contMDiffAt.comp
        base hSecondLocal
  have hLocal :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, Complex) ∞
        (fun point =>
          d9DoubledMatterSpinorHermitianPairing
            (localFirst point) (localSecond point)) base := by
    exact
      (d9MatterSpinorHermitianPairing_comp_contMDiffAt
        period hPeriod
        (fun point => (localFirst point).1)
        (fun point => (localSecond point).1)
        base hFirstFirst hSecondFirst).add
      (d9MatterSpinorHermitianPairing_comp_contMDiffAt
        period hPeriod
        (fun point => (localFirst point).2)
        (fun point => (localSecond point).2)
        base hFirstSecond hSecondSecond)
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [] with point
  have hLocalFirst :
      localFirst point =
        core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from first point) := by
    change
      core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from first point) =
        core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from first point)
    rfl
  have hLocalSecond :
      localSecond point =
        core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from second point) := by
    change
      core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from second point) =
        core.coordChange
          (core.indexAt point) (core.indexAt base) point
            (show D9DoubledMatterFiber from second point)
    rfl
  rw [d9PrimitiveSpinCPointwiseHermitianPairing,
    hLocalFirst, hLocalSecond]
  exact
    (d9DoubledMatterSpinorHermitianPairing_coordChange
      period hPeriod choice
      (core.indexAt point) (core.indexAt base) point
      (show D9DoubledMatterFiber from first point)
      (show D9DoubledMatterFiber from second point)).symm

theorem d9PrimitiveSpinCPointwiseHermitianPairing_continuous
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Continuous
      (d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first second) :=
  (d9PrimitiveSpinCPointwiseHermitianPairing_contMDiff
    period hPeriod choice first second).continuous

theorem d9PrimitiveSpinCPointwiseHermitianPairing_integrable
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Integrable
      (d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod choice first second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  exact
    (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
      period hPeriod choice first second).integrable_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset
          (isClosed_tsupport
            (d9PrimitiveSpinCPointwiseHermitianPairing
              period hPeriod choice first second))
          (subset_univ _))

/-- Canonical geometric `L2` pairing, defined independently of spectral
coordinates. -/
def d9PrimitiveSpinCGeometricL2Pairing
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) : Complex :=
  ∫ base,
    d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod choice first second base
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Exact reduction of the intrinsic quotient pairing to the canonical
round-sphere/time fundamental domain. -/
theorem d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice first second =
      ∫ base : CanonicalLatitudeBase,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second
          (canonicalLatitudeThroatMap period hPeriod base)
        ∂(canonicalLatitudeBaseMeasure period) := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
  exact MeasureTheory.integral_map
    (canonicalLatitudeThroatMap_continuous
      period hPeriod).measurable.aemeasurable
    (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
      period hPeriod choice first second).aestronglyMeasurable

theorem d9PrimitiveSpinCGeometricL2Pairing_add_left
    (choice : NormalRootChoice)
    (first second third :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice (first + second) third =
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first third +
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice second third := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [show
      (fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice (first + second) third base) =
      fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first third base +
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice second third base by
    funext base
    exact
      d9PrimitiveSpinCPointwiseHermitianPairing_add_left
        period hPeriod choice first second third base]
  exact integral_add
    (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod choice first third)
    (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod choice second third)

theorem d9PrimitiveSpinCGeometricL2Pairing_add_right
    (choice : NormalRootChoice)
    (first second third :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice first (second + third) =
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first second +
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first third := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [show
      (fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first (second + third) base) =
      fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first second base +
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first third base by
    funext base
    exact
      d9PrimitiveSpinCPointwiseHermitianPairing_add_right
        period hPeriod choice first second third base]
  exact integral_add
    (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod choice first second)
    (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod choice first third)

theorem d9PrimitiveSpinCGeometricL2Pairing_conj_symm
    (choice : NormalRootChoice)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    (starRingEnd Complex)
        (d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first second) =
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice second first := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with base
  exact
    d9PrimitiveSpinCPointwiseHermitianPairing_conj_symm
      period hPeriod choice first second base

theorem d9PrimitiveSpinCGeometricL2Pairing_complexScalar_left
    (choice : NormalRootChoice) (scalar : Complex)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar first) second =
      (starRingEnd Complex) scalar *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first second := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [show
      (fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice scalar first) second base) =
      fun base =>
        (starRingEnd Complex) scalar *
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first second base by
    funext base
    exact
      d9PrimitiveSpinCPointwiseHermitianPairing_complexScalar_left
        period hPeriod choice scalar first second base]
  exact integral_const_mul
    ((starRingEnd Complex) scalar)
    (d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod choice first second)

theorem d9PrimitiveSpinCGeometricL2Pairing_complexScalar_right
    (choice : NormalRootChoice) (scalar : Complex)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice first
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar second) =
      scalar *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first second := by
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [show
      (fun base =>
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice scalar second) base) =
      fun base =>
        scalar *
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first second base by
    funext base
    exact
      d9PrimitiveSpinCPointwiseHermitianPairing_complexScalar_right
        period hPeriod choice scalar first second base]
  exact integral_const_mul scalar
    (d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod choice first second)

/-- Real pointwise norm-square density of a smooth primitive SpinC
section. -/
def d9PrimitiveSpinCGeometricL2Density
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) : Real :=
  (d9PrimitiveSpinCPointwiseHermitianPairing
    period hPeriod choice state state base).re

theorem d9PrimitiveSpinCGeometricL2Density_continuous
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Continuous
      (d9PrimitiveSpinCGeometricL2Density
        period hPeriod choice state) :=
  Complex.reCLM.continuous.comp
    (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
      period hPeriod choice state state)

theorem d9PrimitiveSpinCGeometricL2Density_integrable
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Integrable
      (d9PrimitiveSpinCGeometricL2Density
        period hPeriod choice state)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
    period hPeriod choice state state).re

theorem d9PrimitiveSpinCGeometricL2Density_nonnegative
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    0 ≤
      d9PrimitiveSpinCGeometricL2Density
        period hPeriod choice state base :=
  d9DoubledMatterSpinorHermitianPairing_self_re_nonnegative
    (show D9DoubledMatterFiber from state base)

theorem d9PrimitiveSpinCGeometricL2Density_eq_zero_iff
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGeometricL2Density
        period hPeriod choice state base = 0 ↔
      state base = 0 :=
  d9DoubledMatterSpinorHermitianPairing_self_re_eq_zero_iff
    (show D9DoubledMatterFiber from state base)

theorem d9PrimitiveSpinCGeometricL2Pairing_self_re
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice state state).re =
      ∫ base,
        d9PrimitiveSpinCGeometricL2Density
          period hPeriod choice state base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  exact
    (integral_re
      (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
        period hPeriod choice state state)).symm

theorem d9PrimitiveSpinCGeometricL2Pairing_self_re_nonnegative
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    0 ≤
      (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice state state).re := by
  rw [d9PrimitiveSpinCGeometricL2Pairing_self_re]
  exact integral_nonneg
    (d9PrimitiveSpinCGeometricL2Density_nonnegative
      period hPeriod choice state)

/-- Positive definiteness of the independently integrated geometric
pairing.  Full support of the canonical measure upgrades almost-everywhere
vanishing to pointwise vanishing for smooth sections. -/
theorem d9PrimitiveSpinCGeometricL2Pairing_self_re_eq_zero_iff
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice state state).re = 0 ↔
      state = 0 := by
  constructor
  · intro hZero
    apply ContMDiffSection.ext
    intro base
    by_contra hValue
    have hDensity :
        d9PrimitiveSpinCGeometricL2Density
            period hPeriod choice state base ≠ 0 :=
      (d9PrimitiveSpinCGeometricL2Density_eq_zero_iff
        period hPeriod choice state base).not.mpr hValue
    have hPositive :
        0 <
          ∫ point,
            d9PrimitiveSpinCGeometricL2Density
              period hPeriod choice state point
            ∂(intrinsicCanonicalThroatVolumeMeasure
              period hPeriod) :=
      integral_pos_of_integrable_nonneg_nonzero
        (d9PrimitiveSpinCGeometricL2Density_continuous
          period hPeriod choice state)
        (d9PrimitiveSpinCGeometricL2Density_integrable
          period hPeriod choice state)
        (d9PrimitiveSpinCGeometricL2Density_nonnegative
          period hPeriod choice state)
        hDensity
    rw [← d9PrimitiveSpinCGeometricL2Pairing_self_re] at hPositive
    exact (lt_irrefl 0) (hZero ▸ hPositive)
  · rintro rfl
    rw [d9PrimitiveSpinCGeometricL2Pairing_self_re]
    rw [show
      d9PrimitiveSpinCGeometricL2Density
          period hPeriod choice
          (0 : D9PrimitiveSpinCSmoothSection
            period hPeriod choice) =
        0 by
      funext base
      exact
        (d9PrimitiveSpinCGeometricL2Density_eq_zero_iff
          period hPeriod choice 0 base).mpr rfl]
    simp

/-- The actual descended complex scalar action used by the geometric
pairing. -/
noncomputable instance d9PrimitiveSpinCGeometricL2ComplexSMul
    (choice : NormalRootChoice) :
    SMul Complex
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) where
  smul scalar state :=
    d9PrimitiveSpinCComplexScalarSection
      period hPeriod choice scalar state

/-- Complex module laws inherited from the already proved global scalar
representation. -/
noncomputable instance d9PrimitiveSpinCGeometricL2ComplexModule
    (choice : NormalRootChoice) :
    Module Complex
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) :=
  Module.ofMinimalAxioms
    (fun scalar first second =>
      map_add
        (d9PrimitiveSpinCComplexScalarSectionLinearMap
          period hPeriod choice scalar) first second)
    (fun first second state =>
      d9PrimitiveSpinCComplexScalarSection_add_scalar
        period hPeriod choice first second state)
    (fun first second state =>
      d9PrimitiveSpinCComplexScalarSection_mul
        period hPeriod choice first second state)
    (fun state =>
      d9PrimitiveSpinCComplexScalarSection_one
        period hPeriod choice state)

@[simp]
theorem d9PrimitiveSpinCGeometricL2_complex_smul
    (choice : NormalRootChoice) (scalar : Complex)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    scalar • state =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state :=
  rfl

@[implicit_reducible]
noncomputable def d9PrimitiveSpinCGeometricL2PreCore
    (choice : NormalRootChoice) :
    PreInnerProductSpace.Core Complex
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) where
  inner :=
    d9PrimitiveSpinCGeometricL2Pairing
      period hPeriod choice
  conj_inner_symm first second :=
    d9PrimitiveSpinCGeometricL2Pairing_conj_symm
      period hPeriod choice second first
  re_inner_nonneg state :=
    d9PrimitiveSpinCGeometricL2Pairing_self_re_nonnegative
      period hPeriod choice state
  add_left first second third :=
    d9PrimitiveSpinCGeometricL2Pairing_add_left
      period hPeriod choice first second third
  smul_left first second scalar := by
    change
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice scalar first) second =
        (starRingEnd Complex) scalar *
          d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod choice first second
    exact
      d9PrimitiveSpinCGeometricL2Pairing_complexScalar_left
        period hPeriod choice scalar first second

@[implicit_reducible]
noncomputable def d9PrimitiveSpinCGeometricL2Core
    (choice : NormalRootChoice) :
    InnerProductSpace.Core Complex
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) :=
  { __ := d9PrimitiveSpinCGeometricL2PreCore
      period hPeriod choice
    definite := by
      intro state hZero
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod choice state state = 0 at hZero
      apply
        (d9PrimitiveSpinCGeometricL2Pairing_self_re_eq_zero_iff
          period hPeriod choice state).mp
      simpa using congrArg Complex.re hZero }

noncomputable instance d9PrimitiveSpinCGeometricL2NormedAddCommGroup
    (choice : NormalRootChoice) :
    NormedAddCommGroup
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := d9PrimitiveSpinCGeometricL2Core
      period hPeriod choice)

noncomputable instance d9PrimitiveSpinCGeometricL2InnerProductSpace
    (choice : NormalRootChoice) :
    InnerProductSpace Complex
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) :=
  InnerProductSpace.ofCore
    (d9PrimitiveSpinCGeometricL2PreCore
      period hPeriod choice)

theorem d9PrimitiveSpinCGeometricL2_norm_sq
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    ‖state‖ ^ 2 =
      (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod choice state state).re :=
  norm_sq_eq_re_inner (𝕜 := Complex) state

/-- Hilbert completion of the complete smooth geometric SpinC core in the
independently integrated norm. -/
abbrev D9PrimitiveSpinCGeometricL2Completion
    (choice : NormalRootChoice) :=
  UniformSpace.Completion
    (D9PrimitiveSpinCSmoothSection period hPeriod choice)

/-- Canonical isometric inclusion of smooth sections into geometric
`L2`. -/
def d9PrimitiveSpinCGeometricL2Embedding
    (choice : NormalRootChoice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →L[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod choice :=
  UniformSpace.Completion.toComplL

theorem d9PrimitiveSpinCGeometricL2Embedding_denseRange
    (choice : NormalRootChoice) :
    DenseRange
      (d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod choice) := by
  change DenseRange
    ((↑) :
      D9PrimitiveSpinCSmoothSection period hPeriod choice →
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod choice)
  exact UniformSpace.Completion.denseRange_coe

/-- Assumption-free closure certificate for the independent geometric
Hilbert structure. -/
structure ProgramPD9PrimitiveSpinCGeometricL2PairingCertificate4D where
  choice : NormalRootChoice
  pointwiseSmooth :
    ∀ first second,
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
        (d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second)
  pairingIntegrable :
    ∀ first second,
      Integrable
        (d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod choice first second)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  hermitian :
    ∀ first second,
      (starRingEnd Complex)
          (d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod choice first second) =
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice second first
  positiveDefinite :
    ∀ state,
      (d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice state state).re = 0 ↔
        state = 0
  smoothCoreDense :
    DenseRange
      (d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod choice)

def programPD9PrimitiveSpinCGeometricL2PairingCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2PairingCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  pointwiseSmooth :=
    d9PrimitiveSpinCPointwiseHermitianPairing_contMDiff
      period hPeriod .positiveQuarter
  pairingIntegrable :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter
  hermitian :=
    d9PrimitiveSpinCGeometricL2Pairing_conj_symm
      period hPeriod .positiveQuarter
  positiveDefinite :=
    d9PrimitiveSpinCGeometricL2Pairing_self_re_eq_zero_iff
      period hPeriod .positiveQuarter
  smoothCoreDense :=
    d9PrimitiveSpinCGeometricL2Embedding_denseRange
      period hPeriod .positiveQuarter

theorem primitiveSpinCGeometricL2Pairing_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2PairingCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2PairingCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
end JanusFormal
