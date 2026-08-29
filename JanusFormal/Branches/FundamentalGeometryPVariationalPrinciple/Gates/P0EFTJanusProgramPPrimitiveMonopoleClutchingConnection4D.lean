import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusThroatMonopoleEmergence
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusNormalRootMonopoleSeparation

/-!
# Primitive monopole clutching bundle and Dirac connection

This file constructs the two-chart principal `U(1)` bundle on the unit
two-sphere.  Its overlap transition is the normalized equatorial phase to the
signed charge.  The north/south Dirac potentials differ by the corresponding
Maurer--Cartan form and have the same curvature.  For charge `±1` the flux is
primitive.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

set_option autoImplicit false
noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff
open P0EFTJanusThroatMonopoleEmergence
open P0EFTJanusNormalRootMonopoleSeparation

abbrev MonopoleSphere :=
  Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1

/-- The two standard monopole gauges. -/
inductive MonopoleChart
  | north
  | south
  deriving DecidableEq

/-- Ambient coordinate of a sphere point. -/
def monopoleSphereCoordinate (point : MonopoleSphere) (index : Fin 3) : Real :=
  point.1 index

/-- Equatorial complex coordinate `x + i y`. -/
def monopoleSphereXY (point : MonopoleSphere) : Complex :=
  ⟨monopoleSphereCoordinate point 0, monopoleSphereCoordinate point 1⟩

/-- North and south stereographic domains, described intrinsically by the
excluded pole. -/
def monopoleChartDomain : MonopoleChart → Set MonopoleSphere
  | .north =>
      {point | monopoleSphereCoordinate point 2 ≠ -1}
  | .south =>
      {point | monopoleSphereCoordinate point 2 ≠ 1}

theorem monopoleSphereCoordinate_continuous (index : Fin 3) :
    Continuous (fun point : MonopoleSphere =>
      monopoleSphereCoordinate point index) := by
  exact
    (PiLp.continuous_apply
      (p := 2) (β := fun _ : Fin 3 => Real) index).comp
        continuous_subtype_val

theorem monopoleChartDomain_isOpen (chart : MonopoleChart) :
    IsOpen (monopoleChartDomain chart) := by
  cases chart with
  | north =>
      exact isOpen_ne_fun
        (monopoleSphereCoordinate_continuous 2) continuous_const
  | south =>
      exact isOpen_ne_fun
        (monopoleSphereCoordinate_continuous 2) continuous_const

theorem monopoleChartDomain_cover (point : MonopoleSphere) :
    ∃ chart, point ∈ monopoleChartDomain chart := by
  by_cases hNorth :
      monopoleSphereCoordinate point 2 ≠ -1
  · exact ⟨.north, hNorth⟩
  · have hSouth : monopoleSphereCoordinate point 2 ≠ 1 := by
      intro hOne
      apply hNorth
      linarith
    exact ⟨.south, hSouth⟩

/-- On the double overlap the equatorial complex coordinate is nonzero. -/
theorem monopoleSphereXY_ne_zero_of_mem_overlap
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hSouth : point ∈ monopoleChartDomain .south) :
    monopoleSphereXY point ≠ 0 := by
  intro hZero
  have hx : monopoleSphereCoordinate point 0 = 0 :=
    congrArg Complex.re hZero
  have hy : monopoleSphereCoordinate point 1 = 0 :=
    congrArg Complex.im hZero
  have hNorm : ‖(point.1 : EuclideanSpace Real (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using point.2
  have hNormSq := congrArg (fun value : Real => value ^ 2) hNorm
  rw [EuclideanSpace.real_norm_sq_eq] at hNormSq
  simp [Fin.sum_univ_succ] at hNormSq
  change
    monopoleSphereCoordinate point 0 ^ 2 +
        (monopoleSphereCoordinate point 1 ^ 2 +
          monopoleSphereCoordinate point 2 ^ 2) = 1 at hNormSq
  rw [hx, hy] at hNormSq
  have hz :
      monopoleSphereCoordinate point 2 = 1 ∨
        monopoleSphereCoordinate point 2 = -1 := by
    norm_num at hNormSq
    exact hNormSq
  exact hz.elim hSouth hNorth

/-- Unit equatorial phase, with an irrelevant fallback at the two poles. -/
def monopoleSphereXYPhase (point : MonopoleSphere) : Circle := by
  by_cases hXY : monopoleSphereXY point = 0
  · exact 1
  · exact
      ⟨NormedSpace.normalize (monopoleSphereXY point), by
        simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using
          NormedSpace.norm_normalize hXY⟩

theorem monopoleSphereXY_continuous :
    Continuous (monopoleSphereXY : MonopoleSphere → Complex) := by
  change
    Continuous (fun point : MonopoleSphere =>
      Complex.equivRealProdCLM.symm
        (monopoleSphereCoordinate point 0,
          monopoleSphereCoordinate point 1))
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((monopoleSphereCoordinate_continuous 0).prodMk
      (monopoleSphereCoordinate_continuous 1))

theorem monopoleSphereXYPhase_coe_of_ne_zero
    (point : MonopoleSphere) (hXY : monopoleSphereXY point ≠ 0) :
    (monopoleSphereXYPhase point : Complex) =
      ‖monopoleSphereXY point‖⁻¹ • monopoleSphereXY point := by
  simp [monopoleSphereXYPhase, hXY, NormedSpace.normalize]

theorem monopoleSphereXYPhase_continuousOn_overlap :
    ContinuousOn monopoleSphereXYPhase
      (monopoleChartDomain .north ∩ monopoleChartDomain .south) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_induced_rng.mpr
  have hXY :
      ∀ point :
          (monopoleChartDomain .north ∩
            monopoleChartDomain .south : Set MonopoleSphere),
        monopoleSphereXY point.1 ≠ 0 := by
    intro point
    exact monopoleSphereXY_ne_zero_of_mem_overlap point.1 point.2.1 point.2.2
  have hBase :
      Continuous
        (fun point :
          (monopoleChartDomain .north ∩
            monopoleChartDomain .south : Set MonopoleSphere) =>
          monopoleSphereXY point.1) :=
    monopoleSphereXY_continuous.comp continuous_subtype_val
  have hNormalized :
      Continuous
        (fun point :
          (monopoleChartDomain .north ∩
            monopoleChartDomain .south : Set MonopoleSphere) =>
          ‖monopoleSphereXY point.1‖⁻¹ • monopoleSphereXY point.1) :=
    hBase.norm.inv₀ (fun point => norm_ne_zero_iff.mpr (hXY point))
      |>.smul hBase
  exact hNormalized.congr fun point =>
    (monopoleSphereXYPhase_coe_of_ne_zero point.1 (hXY point)).symm

/-- Signed clutching transition. -/
def primitiveMonopoleTransition
    (charge : Int) (first second : MonopoleChart)
    (point : MonopoleSphere) : Circle :=
  match first, second with
  | .north, .north => 1
  | .south, .south => 1
  | .north, .south => monopoleSphereXYPhase point ^ charge
  | .south, .north => (monopoleSphereXYPhase point ^ charge)⁻¹

@[simp]
theorem primitiveMonopoleTransition_self
    (charge : Int) (chart : MonopoleChart) (point : MonopoleSphere) :
    primitiveMonopoleTransition charge chart chart point = 1 := by
  cases chart <;> rfl

theorem primitiveMonopoleTransition_inverse
    (charge : Int) (first second : MonopoleChart)
    (point : MonopoleSphere) :
    primitiveMonopoleTransition charge first second point *
        primitiveMonopoleTransition charge second first point = 1 := by
  cases first <;> cases second <;>
    simp [primitiveMonopoleTransition]

theorem primitiveMonopoleTransition_cocycle
    (charge : Int) (first second third : MonopoleChart)
    (point : MonopoleSphere) :
    primitiveMonopoleTransition charge second third point *
        (primitiveMonopoleTransition charge first second point) =
      primitiveMonopoleTransition charge first third point := by
  cases first <;> cases second <;> cases third <;>
    simp [primitiveMonopoleTransition]

theorem primitiveMonopoleTransition_continuousOn
    (charge : Int) (first second : MonopoleChart) :
    ContinuousOn
      (fun pair : MonopoleSphere × Circle =>
        primitiveMonopoleTransition charge first second pair.1 * pair.2)
      ((monopoleChartDomain first ∩ monopoleChartDomain second) ×ˢ
        Set.univ) := by
  cases first <;> cases second
  · simpa [primitiveMonopoleTransition] using
      continuous_snd.continuousOn
  · exact
      ((monopoleSphereXYPhase_continuousOn_overlap.zpow charge).comp
        continuous_fst.continuousOn (by
          intro pair hPair
          exact hPair.1)).mul continuous_snd.continuousOn
  · have hPhase :
        ContinuousOn
          (fun point => (monopoleSphereXYPhase point ^ charge)⁻¹)
          (monopoleChartDomain .south ∩
            monopoleChartDomain .north) := by
      simpa [inter_comm] using
        monopoleSphereXYPhase_continuousOn_overlap.zpow charge |>.inv
    exact
      (hPhase.comp continuous_fst.continuousOn (by
        intro pair hPair
        exact hPair.1)).mul continuous_snd.continuousOn
  · simpa [primitiveMonopoleTransition] using
      continuous_snd.continuousOn

/-- Genuine topological principal-circle bundle core of charge `charge`. -/
def primitiveMonopolePrincipalBundleCore (charge : Int) :
    FiberBundleCore MonopoleChart MonopoleSphere Circle := by
  classical
  exact
    { baseSet := monopoleChartDomain
      isOpen_baseSet := monopoleChartDomain_isOpen
      indexAt point :=
        if monopoleSphereCoordinate point 2 = -1 then .south else .north
      mem_baseSet_at point := by
        split_ifs with hPole
        · change monopoleSphereCoordinate point 2 ≠ 1
          linarith
        · exact hPole
      coordChange first second point phase :=
        primitiveMonopoleTransition charge first second point * phase
      coordChange_self chart point _ phase := by
        simp
      continuousOn_coordChange :=
        primitiveMonopoleTransition_continuousOn charge
      coordChange_comp first second third point _ phase := by
        rw [← mul_assoc,
          primitiveMonopoleTransition_cocycle charge first second third point] }

/-- Equatorial parametrization used to read the clutching character. -/
def monopoleEquator (angle : Real) : MonopoleSphere := by
  refine
    ⟨WithLp.toLp 2 ![Real.cos angle, Real.sin angle, 0], ?_⟩
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ, Real.sq_sqrt, Real.sin_sq_add_cos_sq]

@[simp]
theorem monopoleSphereXY_equator (angle : Real) :
    monopoleSphereXY (monopoleEquator angle) =
      Complex.exp (angle * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp [monopoleSphereXY, monopoleEquator,
      monopoleSphereCoordinate]
    exact (Complex.cos_ofReal_re angle).symm
  · simp [monopoleSphereXY, monopoleEquator,
      monopoleSphereCoordinate]
    exact (Complex.sin_ofReal_re angle).symm

@[simp]
theorem monopoleSphereXYPhase_equator (angle : Real) :
    monopoleSphereXYPhase (monopoleEquator angle) =
      Circle.exp angle := by
  apply Circle.ext
  rw [monopoleSphereXYPhase_coe_of_ne_zero]
  · simp [monopoleSphereXY_equator, Circle.coe_exp]
  · simp [monopoleSphereXY_equator]

/-- The overlap character has exactly the signed integer winding. -/
theorem primitiveMonopoleTransition_equator
    (charge : Int) (angle : Real) :
    primitiveMonopoleTransition charge .north .south
        (monopoleEquator angle) =
      Circle.exp angle ^ charge := by
  simp [primitiveMonopoleTransition]

/-- Local north/south connection coefficients in spherical coordinates. -/
def primitiveMonopoleNorthPotential (charge : Int) (polarAngle : Real) : Real :=
  (charge : Real) / 2 * (1 - Real.cos polarAngle)

def primitiveMonopoleSouthPotential (charge : Int) (polarAngle : Real) : Real :=
  -(charge : Real) / 2 * (1 + Real.cos polarAngle)

/-- Gauge compatibility on the overlap:
`A_N - A_S = q dφ`. -/
theorem primitiveMonopolePotential_gauge_difference
    (charge : Int) (polarAngle : Real) :
    primitiveMonopoleNorthPotential charge polarAngle -
        primitiveMonopoleSouthPotential charge polarAngle =
      (charge : Real) := by
  simp [primitiveMonopoleNorthPotential,
    primitiveMonopoleSouthPotential]
  ring

/-- Common curvature coefficient `q/2 sin θ`. -/
def primitiveMonopoleCurvatureCoefficient
    (charge : Int) (polarAngle : Real) : Real :=
  (charge : Real) / 2 * Real.sin polarAngle

/-- Scalar derivative with the canonical normed-algebra module, made explicit
to avoid the irrelevant `Real` module-instance diamond. -/
def HasCanonicalRealDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  @HasDerivAt Real _ Real Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace Real).toModule _ _
      function derivative point

theorem primitiveMonopoleNorthPotential_hasDerivAt
    (charge : Int) (polarAngle : Real) :
    HasCanonicalRealDerivAt (primitiveMonopoleNorthPotential charge)
      (primitiveMonopoleCurvatureCoefficient charge polarAngle)
      polarAngle := by
  unfold HasCanonicalRealDerivAt
  unfold primitiveMonopoleNorthPotential
    primitiveMonopoleCurvatureCoefficient
  convert
    ((Real.hasDerivAt_cos polarAngle).const_sub 1).const_mul
      ((charge : Real) / 2) using 1 <;> ring

theorem primitiveMonopoleSouthPotential_hasDerivAt
    (charge : Int) (polarAngle : Real) :
    HasCanonicalRealDerivAt (primitiveMonopoleSouthPotential charge)
      (primitiveMonopoleCurvatureCoefficient charge polarAngle)
      polarAngle := by
  unfold HasCanonicalRealDerivAt
  unfold primitiveMonopoleSouthPotential
    primitiveMonopoleCurvatureCoefficient
  convert
    ((Real.hasDerivAt_cos polarAngle).const_add 1).const_mul
      (-(charge : Real) / 2) using 1 <;> ring

/-- The curvature integrates over the polar coordinate to the charge. -/
theorem primitiveMonopoleCurvature_polarIntegral
    (charge : Int) :
    (∫ polarAngle in (0 : Real)..Real.pi,
      primitiveMonopoleCurvatureCoefficient charge polarAngle) =
        (charge : Real) := by
  rw [show (fun polarAngle =>
      primitiveMonopoleCurvatureCoefficient charge polarAngle) =
      fun polarAngle => ((charge : Real) / 2) * Real.sin polarAngle by
        rfl,
    intervalIntegral.integral_const_mul, integral_sin]
  simp
  ring

/-- Full flux is `2πq`; hence `flux/(2π)=q`. -/
theorem primitiveMonopoleFlux_quantized
    (charge : Int) :
    2 * Real.pi *
        (∫ polarAngle in (0 : Real)..Real.pi,
          primitiveMonopoleCurvatureCoefficient charge polarAngle) =
      2 * Real.pi * (charge : Real) := by
  rw [primitiveMonopoleCurvature_polarIntegral]

/-- Primitive charge package attached to the explicit clutching bundle. -/
def primitiveMonopoleChernData
    (charge : Int) (hPrimitive : charge.natAbs = 1) :
    PrimitiveMonopoleLineChernData where
  firstChernNumber := charge
  primitive := hPrimitive

structure ProgramPPrimitiveMonopoleClutchingConnectionCertificate4D where
  charge : Int
  primitive : charge.natAbs = 1
  principalCore :
    FiberBundleCore MonopoleChart MonopoleSphere Circle
  principalCoreCanonical :
    principalCore = primitiveMonopolePrincipalBundleCore charge
  chernData : PrimitiveMonopoleLineChernData
  chernDataCanonical :
    chernData = primitiveMonopoleChernData charge primitive
  transitionWinding :
    ∀ angle,
      primitiveMonopoleTransition charge .north .south
          (monopoleEquator angle) =
        Circle.exp angle ^ charge
  gaugeCompatibility :
    ∀ polarAngle,
      primitiveMonopoleNorthPotential charge polarAngle -
          primitiveMonopoleSouthPotential charge polarAngle =
        (charge : Real)
  northCurvature :
    ∀ polarAngle,
      HasCanonicalRealDerivAt (primitiveMonopoleNorthPotential charge)
        (primitiveMonopoleCurvatureCoefficient charge polarAngle)
        polarAngle
  southCurvature :
    ∀ polarAngle,
      HasCanonicalRealDerivAt (primitiveMonopoleSouthPotential charge)
        (primitiveMonopoleCurvatureCoefficient charge polarAngle)
        polarAngle
  fluxQuantized :
    2 * Real.pi *
        (∫ polarAngle in (0 : Real)..Real.pi,
          primitiveMonopoleCurvatureCoefficient charge polarAngle) =
      2 * Real.pi * (charge : Real)

def programPPrimitiveMonopoleClutchingConnectionCertificate4D :
    ProgramPPrimitiveMonopoleClutchingConnectionCertificate4D where
  charge := 1
  primitive := by norm_num
  principalCore := primitiveMonopolePrincipalBundleCore 1
  principalCoreCanonical := rfl
  chernData := primitiveMonopoleChernData 1 (by norm_num)
  chernDataCanonical := rfl
  transitionWinding :=
    primitiveMonopoleTransition_equator 1
  gaugeCompatibility :=
    primitiveMonopolePotential_gauge_difference 1
  northCurvature :=
    primitiveMonopoleNorthPotential_hasDerivAt 1
  southCurvature :=
    primitiveMonopoleSouthPotential_hasDerivAt 1
  fluxQuantized :=
    primitiveMonopoleFlux_quantized 1

theorem
    programPPrimitiveMonopoleClutchingConnectionCertificate4D_nonempty :
    Nonempty ProgramPPrimitiveMonopoleClutchingConnectionCertificate4D :=
  ⟨programPPrimitiveMonopoleClutchingConnectionCertificate4D⟩

end
end P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
end JanusFormal
