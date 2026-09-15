import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D

/-!
# Coordinate orientation of the explicit warped null collar

This gate fixes the sign left open by Gate 1040.  Relative to the fixed ambient
coordinate volume and the ordered null tangent frame `(k,e₁,e₂)`, the future
lower-half-collar outward convention `-e₃` has flux exactly `+1`.

This is a coordinate orientation statement.  It does not identify the fixed
coordinate volume with the warped metric volume or construct an integrated
Stokes theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarOrientation4D

set_option autoImplicit false

noncomputable section

open Module
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D

/-- The fixed coordinate orientation gives the lower-half-collar outward
vector unit flux through the ordered null tangent frame. -/
theorem programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        programPT06WarpedNullCollarZeroBoundaryOutward
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) = 1 := by
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_rigging source]
  let basis := programPT06AmbientCoordinateBasis
  let form := programPT06AmbientSignedVolume.curryLeft (basis 0)
  let tail : Fin 3 → ProgramPT06AmbientCoordinate4 :=
    fun direction => basis direction.succ
  let swapLast : Fin 3 → ProgramPT06AmbientCoordinate4 :=
    tail ∘ Equiv.swap (1 : Fin 3) 2
  let outwardTail : Fin 3 → ProgramPT06AmbientCoordinate4 :=
    swapLast ∘ Equiv.swap (0 : Fin 3) 1
  let frame := programPT06FiniteNullFaceGeometricTangentFrame
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit) 0 () source
  have hBasis : form tail = 1 := by
    change programPT06AmbientSignedVolume
      (Matrix.vecCons (basis 0) tail) = 1
    have hFrame : Matrix.vecCons (basis 0) tail = basis := by
      funext direction
      exact Fin.cases rfl (fun _ => rfl) direction
    rw [hFrame]
    exact programPT06AmbientSignedVolume_apply_basis
  have hSwapLast : form swapLast = -form tail := by
    simpa [swapLast] using
      form.toAlternatingMap.map_swap tail
        (show (1 : Fin 3) ≠ 2 by decide)
  have hOutwardTail : form outwardTail = form tail := by
    have hSwapFirst : form outwardTail = -form swapLast := by
      simpa [outwardTail] using
        form.toAlternatingMap.map_swap swapLast
          (show (0 : Fin 3) ≠ 1 by decide)
    rw [hSwapFirst, hSwapLast]
    simp
  have hFrame :
      frame = Function.update outwardTail 0 (basis 0 + basis 3) := by
    funext direction
    refine Fin.cases ?_
        (fun direction2 =>
          Fin.cases ?_
            (fun direction1 =>
              Fin.cases ?_ (fun impossible => Fin.elim0 impossible) direction1)
            direction2)
        direction <;>
      apply (EuclideanSpace.equiv (Fin 4) Real).injective <;>
      funext coordinate <;>
      fin_cases coordinate <;>
      simp [frame, outwardTail, swapLast, tail, basis,
        programPT06FiniteNullFaceGeometricTangentFrame,
        programPT06ExplicitWarpedNullHyperplaneGeometry,
        programPT06AmbientCoordinateBasis, Equiv.swap_apply_def]
    all_goals
      first
      | rw [show (1 : Fin 3) = Fin.succ 0 by decide, Fin.cases_succ]
        simp
      | rw [show (2 : Fin 3) = Fin.succ 1 by decide, Fin.cases_succ]
        simp
  have hRepeated :
      form (Function.update outwardTail 0 (basis 0)) = 0 := by
    change programPT06AmbientSignedVolume
      (Matrix.vecCons (basis 0)
        (Function.update outwardTail 0 (basis 0))) = 0
    exact programPT06AmbientSignedVolume.map_eq_zero_of_eq
      (Matrix.vecCons (basis 0)
        (Function.update outwardTail 0 (basis 0)))
      (i := (0 : Fin 4)) (j := (0 : Fin 3).succ) (by simp)
      (Fin.succ_ne_zero 0).symm
  have hRestore :
      Function.update outwardTail 0 (basis 3) = outwardTail := by
    funext direction
    by_cases hDirection : direction = 0
    · subst direction
      simp [outwardTail, swapLast, tail, basis]
    · simp [hDirection]
  change form frame = 1
  rw [hFrame]
  calc
    form (Function.update outwardTail 0 (basis 0 + basis 3)) =
        form (Function.update outwardTail 0 (basis 0)) +
          form (Function.update outwardTail 0 (basis 3)) := by
      exact form.toAlternatingMap.map_update_add outwardTail 0 (basis 0) (basis 3)
    _ = form tail := by rw [hRepeated, hRestore, zero_add, hOutwardTail]
    _ = 1 := hBasis

/-- Gate 1039's `e₀` rigging has the same exact positive unit flux. -/
theorem programPT06WarpedNullHyperplaneRawTransverse_flux_eq_one
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullHyperplaneRawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) = 1 := by
  rw [← programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_rigging source]
  exact programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one source

end
end P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
end JanusFormal
