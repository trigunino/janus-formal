import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D

/-!
# Flux restriction on the explicit warped null hyperplane

This gate restricts ambient four-currents to coordinate scalar fluxes on the
explicit warped null hyperplane.  The fixed coordinate volume and source frame,
rather than the warped metric volume or screen area, set the convention.  The
coordinate vector `e₀` is a concrete nondegenerate transverse rigging, so the
set-theoretic extension realizes every function when the face index is `Unit`.

No regularity is asserted anywhere; only pointwise equality on the embedded
face is obtained.  No mapping-torus incidence, integration, or Stokes theorem
is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D

set_option autoImplicit false

noncomputable section

open Module
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D

/-- Scalar coordinate fluxes on the explicit null-source chart. -/
abbrev ProgramPT06WarpedNullHyperplaneDensity :=
  ProgramPT06NullFaceSource3 → Real

/-- Linear restriction to the scalar coefficient defined by the fixed
coordinate volume and source frame. -/
def programPT06WarpedNullHyperplaneFluxRestriction :
    ProgramPT06AmbientCurrent4D →ₗ[Real]
      ProgramPT06WarpedNullHyperplaneDensity where
  toFun current source :=
    programPT06NullFaceFluxPullback
      programPT06WarpedNullHyperplaneEmbedding current source
        programPT06NullFaceSourceFrame
  map_add' first second := by
    funext source
    simp only [programPT06NullFaceFluxPullback,
      programPT06ThreeFormPullback, programPT06AmbientFluxThreeForm,
      Pi.add_apply, map_add, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
  map_smul' scalar current := by
    funext source
    simp only [programPT06NullFaceFluxPullback,
      programPT06ThreeFormPullback, programPT06AmbientFluxThreeForm,
      Pi.smul_apply, map_smul, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      RingHom.id_apply]

@[simp] theorem programPT06WarpedNullHyperplaneFluxRestriction_apply
    (current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullHyperplaneFluxRestriction current source =
      programPT06NullFaceFluxPullback
        programPT06WarpedNullHyperplaneEmbedding current source
          programPT06NullFaceSourceFrame := by
  rfl

/-- The fixed coordinate vector `e₀`, used as a transverse rigging. -/
def programPT06WarpedNullHyperplaneRawTransverse
    (_source : ProgramPT06NullFaceSource3) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientCoordinateBasis 0

/-- Coordinate change sending the standard basis to
`(e₀, e₀ + e₃, e₁, e₂)`. -/
private def programPT06WarpedNullHyperplaneAdaptedLinearEquiv :
    ProgramPT06AmbientCoordinate4 ≃ₗ[Real]
      ProgramPT06AmbientCoordinate4 where
  toFun point :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      ![point 0 + point 1, point 2, point 3, point 1]
  invFun point :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      ![point 0 - point 3, point 3, point 1, point 2]
  left_inv point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp
  right_inv point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp
  map_add' first second := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp [add_assoc, add_left_comm]
  map_smul' scalar point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp [mul_add]

private def programPT06WarpedNullHyperplaneAdaptedBasis :
    Basis (Fin 4) Real ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientCoordinateBasis.map
    programPT06WarpedNullHyperplaneAdaptedLinearEquiv

private theorem programPT06WarpedNullHyperplaneFrame_eq_adaptedBasis
    (source : ProgramPT06NullFaceSource3) :
    Matrix.vecCons
        (programPT06WarpedNullHyperplaneRawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) =
      programPT06WarpedNullHyperplaneAdaptedBasis := by
  funext direction
  refine Fin.cases ?_
      (fun direction3 =>
        Fin.cases ?_
          (fun direction2 =>
            Fin.cases ?_
              (fun direction1 =>
                Fin.cases ?_
                  (fun impossible => Fin.elim0 impossible)
                  direction1)
              direction2)
          direction3)
      direction <;>
    apply (EuclideanSpace.equiv (Fin 4) Real).injective <;>
    funext coordinate <;>
    fin_cases coordinate <;>
    simp [programPT06WarpedNullHyperplaneRawTransverse,
      programPT06FiniteNullFaceGeometricTangentFrame,
      programPT06ExplicitWarpedNullHyperplaneGeometry,
      programPT06WarpedNullHyperplaneAdaptedBasis,
      programPT06WarpedNullHyperplaneAdaptedLinearEquiv,
      programPT06AmbientCoordinateBasis, Module.Basis.map_apply]
  all_goals
    first
    | rw [show (1 : Fin 3) = Fin.succ 0 by decide, Fin.cases_succ]
      simp
    | rw [show (2 : Fin 3) = Fin.succ 1 by decide, Fin.cases_succ]
      simp

/-- The explicit `e₀` rigging has nonzero coordinate flux through the
generator/screen frame. -/
theorem programPT06WarpedNullHyperplaneRawTransverse_flux_ne_zero
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullHyperplaneRawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) ≠ 0 := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply,
    programPT06WarpedNullHyperplaneFrame_eq_adaptedBasis source]
  change programPT06AmbientCoordinateBasis.det
      programPT06WarpedNullHyperplaneAdaptedBasis ≠ 0
  exact (programPT06AmbientCoordinateBasis.isUnit_det
    programPT06WarpedNullHyperplaneAdaptedBasis).ne_zero

/-- Concrete set-theoretic ambient extension datum with zero tangential radial
part and prescribed scalar flux. -/
def programPT06WarpedNullHyperplaneRadialAmbientExtension
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06RadialAmbientExtensionDatum
      (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
      0 () (fun _ => 0) density :=
  ProgramPT06RadialAmbientExtensionDatum.setTheoreticOfRawTransverse
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
    0 (programPT06ExplicitWarpedNullHyperplaneGeometry Unit).zero_mem_domain
    () (fun _ => 0) density
    programPT06WarpedNullHyperplaneRawTransverse
    programPT06WarpedNullHyperplaneRawTransverse_flux_ne_zero

/-- A noncomputable set-theoretic right inverse, using an arbitrary choice away
from the embedded face. -/
def programPT06WarpedNullHyperplaneFluxRightInverse
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06AmbientCurrent4D :=
  (programPT06WarpedNullHyperplaneRadialAmbientExtension density).current

/-- Restricting the concrete extension recovers the prescribed density. -/
theorem programPT06WarpedNullHyperplaneFluxRestriction_rightInverse :
    Function.RightInverse
      programPT06WarpedNullHyperplaneFluxRightInverse
      programPT06WarpedNullHyperplaneFluxRestriction := by
  intro density
  funext source
  exact programPT06RadialAmbientExtensionDatum_flux_eq_density
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
    0 (programPT06ExplicitWarpedNullHyperplaneGeometry Unit).zero_mem_domain
    () (fun _ => 0) density
    (programPT06WarpedNullHyperplaneRadialAmbientExtension density) source

/-- Set-theoretic surjectivity on all scalar functions: every chart function is
the coordinate-flux restriction of an ambient function. -/
theorem programPT06WarpedNullHyperplaneFluxRestriction_surjective :
    Function.Surjective programPT06WarpedNullHyperplaneFluxRestriction :=
  programPT06WarpedNullHyperplaneFluxRestriction_rightInverse.surjective

end
end P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
end JanusFormal
