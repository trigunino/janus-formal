import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D

/-!
# Affine flux extension and fiberwise Stokes identity

This gate gives an explicit choice-free right inverse to the warped-null flux
restriction.  In collar coordinates it is the current
`(0,(r-1)ρ(q))`; after transport to ambient coordinates this equals
`(1-r)ρ(q)(-e₃)`.  It has boundary flux `ρ`, vanishes at `r=1`, and its
coordinate divergence is `ρ(q)` whenever `ρ` is differentiable at `q`.

Integrating only the transverse coordinate yields the corresponding one-fiber
Stokes identity.  There is no integration over the null source, metric-volume
comparison, compact support, or mapping-torus incidence in this statement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Module
open scoped Interval
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
open P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D

/-- Affine normal profile `(r-1)ρ(q)` in collar coordinates. -/
def programPT06WarpedNullCollarAffineProfile
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) : Real :=
  (coordinate.2 - 1) * density coordinate.1

/-- Collar-coordinate current with zero tangential component. -/
def programPT06WarpedNullCollarAffineProductCurrent
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    ProgramPT06WarpedNullCollarCoordinate4 :=
  (0, programPT06WarpedNullCollarAffineProfile density coordinate)

/-- Explicit linear extension of a chart density to an ambient current. -/
def programPT06WarpedNullCollarAffineFluxExtension :
    ProgramPT06WarpedNullHyperplaneDensity →ₗ[Real]
      ProgramPT06AmbientCurrent4D where
  toFun density point :=
    programPT06WarpedNullCollarEquiv
      (programPT06WarpedNullCollarAffineProductCurrent density
        (programPT06WarpedNullCollarEquiv.symm point))
  map_add' first second := by
    funext point
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    simp [programPT06WarpedNullCollarAffineProductCurrent,
      programPT06WarpedNullCollarAffineProfile, mul_add]
  map_smul' scalar density := by
    funext point
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    simp [programPT06WarpedNullCollarAffineProductCurrent,
      programPT06WarpedNullCollarAffineProfile]
    ring

/-- Formula for the extension on collar coordinates. -/
@[simp] theorem programPT06WarpedNullCollarAffineFluxExtension_on_collar
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    programPT06WarpedNullCollarAffineFluxExtension density
        (programPT06WarpedNullCollarEquiv coordinate) =
      programPT06WarpedNullCollarEquiv
        (0, (coordinate.2 - 1) * density coordinate.1) := by
  change programPT06WarpedNullCollarEquiv
      (programPT06WarpedNullCollarAffineProductCurrent density
        (programPT06WarpedNullCollarEquiv.symm
          (programPT06WarpedNullCollarEquiv coordinate))) = _
  rw [programPT06WarpedNullCollarEquiv.symm_apply_apply]
  rfl

/-- At `r=0`, the extension is the prescribed density times the lower outward
coordinate vector. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_zeroSlice
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCollarAffineFluxExtension density
        (programPT06WarpedNullHyperplaneEmbedding source) =
      density source • programPT06WarpedNullCollarZeroBoundaryOutward := by
  rw [← programPT06WarpedNullCollar_zeroSlice source,
    programPT06WarpedNullCollarAffineFluxExtension_on_collar]
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext direction
  fin_cases direction <;>
    simp [programPT06WarpedNullCollarEquiv,
      programPT06WarpedNullCollarLinearEquiv,
      programPT06WarpedNullCollarZeroBoundaryOutward,
      programPT06AmbientCoordinateBasis]

/-- The artificial outer slice `r=1` carries zero current. -/
@[simp] theorem programPT06WarpedNullCollarAffineFluxExtension_outer_zero
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCollarAffineFluxExtension density
        (programPT06WarpedNullCollarEquiv (source, 1)) = 0 := by
  rw [programPT06WarpedNullCollarAffineFluxExtension_on_collar]
  simp

/-- The explicit affine extension is a right inverse to coordinate-flux
restriction, with no use of `Function.invFun`. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_rightInverse :
    Function.RightInverse
      programPT06WarpedNullCollarAffineFluxExtension
      programPT06WarpedNullHyperplaneFluxRestriction := by
  intro density
  funext source
  rw [programPT06WarpedNullHyperplaneFluxRestriction_apply]
  change programPT06NullFaceFluxPullback
      ((programPT06ExplicitWarpedNullHyperplaneGeometry Unit).embedding 0 ())
      (programPT06WarpedNullCollarAffineFluxExtension density) source
        programPT06NullFaceSourceFrame = density source
  rw [programPT06FiniteNullFaceFluxPullback_tangent_formula
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit) 0
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit).zero_mem_domain
    () (programPT06WarpedNullCollarAffineFluxExtension density) source]
  change programPT06AmbientSignedVolume.curryLeft
      (programPT06WarpedNullCollarAffineFluxExtension density
        (programPT06WarpedNullHyperplaneEmbedding source))
      (programPT06FiniteNullFaceGeometricTangentFrame
        (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
        0 () source) = density source
  rw [programPT06WarpedNullCollarAffineFluxExtension_zeroSlice]
  simp only [map_smul, ContinuousAlternatingMap.smul_apply]
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one]
  simp

/-- The affine construction gives a choice-free proof of surjectivity. -/
theorem programPT06WarpedNullHyperplaneFluxRestriction_surjective_affine :
    Function.Surjective programPT06WarpedNullHyperplaneFluxRestriction :=
  programPT06WarpedNullCollarAffineFluxExtension_rightInverse.surjective

/-- Derivative of the affine scalar profile. -/
def programPT06WarpedNullCollarAffineProfileDerivative
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    ProgramPT06WarpedNullCollarCoordinate4 →L[Real] Real :=
  (coordinate.2 - 1) •
      ((fderiv Real density coordinate.1).comp
        (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real)) +
    density coordinate.1 •
      (ContinuousLinearMap.snd Real ProgramPT06NullFaceSource3 Real)

theorem programPT06WarpedNullCollarAffineProfile_hasFDerivAt
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {coordinate : ProgramPT06WarpedNullCollarCoordinate4}
    (hDensity : DifferentiableAt Real density coordinate.1) :
    HasFDerivAt (programPT06WarpedNullCollarAffineProfile density)
      (programPT06WarpedNullCollarAffineProfileDerivative density coordinate)
      coordinate := by
  have hRadius : HasFDerivAt
      (fun point : ProgramPT06WarpedNullCollarCoordinate4 => point.2 - 1)
      (ContinuousLinearMap.snd Real ProgramPT06NullFaceSource3 Real)
      coordinate :=
    (hasFDerivAt_snd (𝕜 := Real)).sub_const 1
  have hPulled : HasFDerivAt
      (fun point : ProgramPT06WarpedNullCollarCoordinate4 => density point.1)
      ((fderiv Real density coordinate.1).comp
        (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real))
      coordinate :=
    hDensity.hasFDerivAt.comp coordinate (hasFDerivAt_fst (𝕜 := Real))
  exact hRadius.mul hPulled

/-- Derivative of the collar-coordinate current. -/
def programPT06WarpedNullCollarAffineProductDerivative
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    ProgramPT06WarpedNullCollarCoordinate4 →L[Real]
      ProgramPT06WarpedNullCollarCoordinate4 :=
  (0 : ProgramPT06WarpedNullCollarCoordinate4 →L[Real]
      ProgramPT06NullFaceSource3).prod
    (programPT06WarpedNullCollarAffineProfileDerivative density coordinate)

theorem programPT06WarpedNullCollarAffineProductCurrent_hasFDerivAt
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {coordinate : ProgramPT06WarpedNullCollarCoordinate4}
    (hDensity : DifferentiableAt Real density coordinate.1) :
    HasFDerivAt (programPT06WarpedNullCollarAffineProductCurrent density)
      (programPT06WarpedNullCollarAffineProductDerivative density coordinate)
      coordinate := by
  have hZero : HasFDerivAt
      (fun _ : ProgramPT06WarpedNullCollarCoordinate4 =>
        (0 : ProgramPT06NullFaceSource3))
      (0 : ProgramPT06WarpedNullCollarCoordinate4 →L[Real]
        ProgramPT06NullFaceSource3) coordinate :=
    hasFDerivAt_const (x := coordinate) (c := (0 : ProgramPT06NullFaceSource3))
  exact hZero.prodMk
    (programPT06WarpedNullCollarAffineProfile_hasFDerivAt hDensity)

/-- Exact ambient derivative after conjugating by the collar equivalence. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_hasFDerivAt
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {coordinate : ProgramPT06WarpedNullCollarCoordinate4}
    (hDensity : DifferentiableAt Real density coordinate.1) :
    HasFDerivAt (programPT06WarpedNullCollarAffineFluxExtension density)
      (programPT06WarpedNullCollarEquiv.toContinuousLinearMap.comp
        ((programPT06WarpedNullCollarAffineProductDerivative density coordinate).comp
          programPT06WarpedNullCollarEquiv.symm.toContinuousLinearMap))
      (programPT06WarpedNullCollarEquiv coordinate) := by
  have hProduct :=
    programPT06WarpedNullCollarAffineProductCurrent_hasFDerivAt hDensity
  have hProductAt : HasFDerivAt
      (programPT06WarpedNullCollarAffineProductCurrent density)
      (programPT06WarpedNullCollarAffineProductDerivative density coordinate)
      (programPT06WarpedNullCollarEquiv.symm
        (programPT06WarpedNullCollarEquiv coordinate)) := by
    rw [programPT06WarpedNullCollarEquiv.symm_apply_apply]
    exact hProduct
  change HasFDerivAt
    (fun point => programPT06WarpedNullCollarEquiv
      (programPT06WarpedNullCollarAffineProductCurrent density
        (programPT06WarpedNullCollarEquiv.symm point))) _ _
  exact programPT06WarpedNullCollarEquiv.hasFDerivAt.comp
      (programPT06WarpedNullCollarEquiv coordinate)
      (hProductAt.comp (programPT06WarpedNullCollarEquiv coordinate)
        programPT06WarpedNullCollarEquiv.symm.hasFDerivAt)

/-- A derivative with only an off-diagonal base term and a scalar normal block
has trace equal to that scalar block. -/
theorem programPT06Trace_zeroAffineCollarDerivative
    (normalDerivative : ProgramPT06NullFaceSource3 →L[Real] Real)
    (normalSlope : Real) :
    LinearMap.trace Real ProgramPT06WarpedNullCollarCoordinate4
        (((0 : ProgramPT06WarpedNullCollarCoordinate4 →L[Real]
              ProgramPT06NullFaceSource3).prod
          ((normalDerivative.comp
              (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real)) +
            normalSlope •
              (ContinuousLinearMap.snd Real ProgramPT06NullFaceSource3 Real))).toLinearMap) =
      normalSlope := by
  let offDiagonal : ProgramPT06WarpedNullCollarCoordinate4 →ₗ[Real]
      ProgramPT06WarpedNullCollarCoordinate4 :=
    (ContinuousLinearMap.inr Real ProgramPT06NullFaceSource3 Real).toLinearMap.comp
      (normalDerivative.toLinearMap.comp
        (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real).toLinearMap)
  let diagonal : ProgramPT06WarpedNullCollarCoordinate4 →ₗ[Real]
      ProgramPT06WarpedNullCollarCoordinate4 :=
    LinearMap.prodMap
      (0 : ProgramPT06NullFaceSource3 →ₗ[Real] ProgramPT06NullFaceSource3)
      (normalSlope • LinearMap.id)
  have hSplit :
      ((0 : ProgramPT06WarpedNullCollarCoordinate4 →L[Real]
            ProgramPT06NullFaceSource3).prod
        ((normalDerivative.comp
            (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real)) +
          normalSlope •
            (ContinuousLinearMap.snd Real ProgramPT06NullFaceSource3 Real))).toLinearMap =
        offDiagonal + diagonal := by
    apply LinearMap.ext
    intro vector
    simp [offDiagonal, diagonal]
  rw [hSplit, map_add]
  have hOffDiagonal :
      LinearMap.trace Real ProgramPT06WarpedNullCollarCoordinate4 offDiagonal = 0 := by
    let projection : ProgramPT06WarpedNullCollarCoordinate4 →ₗ[Real]
        ProgramPT06NullFaceSource3 :=
      (ContinuousLinearMap.fst Real ProgramPT06NullFaceSource3 Real).toLinearMap
    let insertion : ProgramPT06NullFaceSource3 →ₗ[Real]
        ProgramPT06WarpedNullCollarCoordinate4 :=
      (ContinuousLinearMap.inr Real ProgramPT06NullFaceSource3 Real).toLinearMap.comp
        normalDerivative.toLinearMap
    have hOff : offDiagonal = insertion.comp projection := by rfl
    rw [hOff, LinearMap.trace_comp_comm' projection insertion]
    have hZero : projection.comp insertion = 0 := by
      apply LinearMap.ext
      intro vector
      rfl
    rw [hZero]
    simp
  rw [hOffDiagonal, zero_add]
  simp [diagonal, LinearMap.trace_prodMap', LinearMap.trace_id]

/-- The collar-coordinate derivative has trace `ρ(q)`. -/
theorem programPT06WarpedNullCollarAffineProductDerivative_trace
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    LinearMap.trace Real ProgramPT06WarpedNullCollarCoordinate4
        (programPT06WarpedNullCollarAffineProductDerivative density coordinate).toLinearMap =
      density coordinate.1 := by
  exact programPT06Trace_zeroAffineCollarDerivative
    ((coordinate.2 - 1) • fderiv Real density coordinate.1) (density coordinate.1)

/-- The ambient coordinate divergence is the prescribed face density and is
constant along the transverse collar fiber. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_divergence
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {source : ProgramPT06NullFaceSource3} (radius : Real)
    (hDensity : DifferentiableAt Real density source) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarAffineFluxExtension density)
        (programPT06WarpedNullCollarEquiv (source, radius)) = density source := by
  rw [programPT06AmbientCoordinateDivergence_eq_trace]
  rw [(programPT06WarpedNullCollarAffineFluxExtension_hasFDerivAt
    (coordinate := (source, radius)) hDensity).fderiv]
  let derivative :=
    programPT06WarpedNullCollarAffineProductDerivative density (source, radius)
  have hConjugate :
      (programPT06WarpedNullCollarEquiv.toContinuousLinearMap.comp
        (derivative.comp
          programPT06WarpedNullCollarEquiv.symm.toContinuousLinearMap)).toLinearMap =
        programPT06WarpedNullCollarEquiv.toLinearEquiv.conj derivative.toLinearMap := by
    rfl
  rw [hConjugate, LinearMap.trace_conj']
  exact programPT06WarpedNullCollarAffineProductDerivative_trace density
    (source, radius)

/-- One-fiber Stokes identity on `0 ≤ r ≤ 1`: the affine current vanishes on
the outer slice, so the integrated divergence is its lower null-face flux. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_fiberwise_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (source : ProgramPT06NullFaceSource3)
    (hDensity : DifferentiableAt Real density source) :
    ∫ radius in (0 : Real)..1,
        programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullCollarAffineFluxExtension density)
          (programPT06WarpedNullCollarEquiv (source, radius)) =
      programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarAffineFluxExtension density) source := by
  simp_rw [programPT06WarpedNullCollarAffineFluxExtension_divergence
    (density := density) (source := source) _ hDensity]
  rw [programPT06WarpedNullCollarAffineFluxExtension_rightInverse density]
  simp

end
end P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
end JanusFormal
