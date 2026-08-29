import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D

/-!
# Global deck-compatible Clifford action on the doubled D9 bundle

The doubled rank-four matter fiber carries three Clifford generators.  This
gate proves that they commute with every integer deck monodromy, hence descend
through every coordinate change of the actual smooth D9 vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- The doubled complex Clifford generator transported to the real matter
fiber used by the smooth vector bundle. -/
def d9DoubledMatterFiberCliffordGamma
    (direction : Fin 3) :
    D9DoubledMatterFiber →ₗ[Real] D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorLinearEquiv.symm.toLinearMap.comp
    ((d9DoubledMatterSpinorCliffordGamma direction).restrictScalars Real
      |>.comp d9DoubledMatterFiberHalfSpinorLinearEquiv.toLinearMap)

@[simp] theorem d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma
    (direction : Fin 3) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGamma direction matter) =
      d9DoubledMatterSpinorCliffordGamma direction
        (d9DoubledMatterFiberHalfSpinorLinearEquiv matter) := by
  simp [d9DoubledMatterFiberCliffordGamma]

theorem d9DoubledMatterFiberCliffordGamma_sq
    (direction : Fin 3) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterFiberCliffordGamma direction matter) =
      -matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma, map_neg]
  exact d9DoubledMatterSpinorCliffordGamma_sq direction
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

theorem d9DoubledMatterFiberCliffordGamma_anticommute
    (first second : Fin 3) (hDistinct : first ≠ second)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma first
        (d9DoubledMatterFiberCliffordGamma second matter) =
      -d9DoubledMatterFiberCliffordGamma second
        (d9DoubledMatterFiberCliffordGamma first matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma, map_neg]
  exact d9DoubledMatterSpinorCliffordGamma_anticommute
    first second hDistinct
      (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

private theorem d9DoubledMatterFiberCliffordGamma_monodromy_one
    (choice : NormalRootChoice) (direction : Fin 3)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterSpinorMonodromy choice 1 matter) =
      d9DoubledMatterSpinorMonodromy choice 1
        (d9DoubledMatterFiberCliffordGamma direction matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
    d9DoubledMatterSpinorMonodromy_one_eq_deckGenerator,
    d9DoubledMatterSpinorMonodromy_one_eq_deckGenerator]
  rw [map_smul]
  exact congrArg (fun spinor =>
    normalRootMultiplier choice • spinor)
      (d9DoubledMatterSpinorCliffordGamma_deck_compatible
        direction (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)).symm

private theorem d9DoubledMatterSpinorMonodromy_injective
    (choice : NormalRootChoice) (winding : Int) :
    Function.Injective
      (d9DoubledMatterSpinorMonodromy choice winding) := by
  intro first second hEqual
  have hInverse := congrArg
    (d9DoubledMatterSpinorMonodromy choice (-winding)) hEqual
  simpa [← d9DoubledMatterSpinorMonodromy_add] using hInverse

private theorem d9DoubledMatterFiberCliffordGamma_monodromy_neg_one
    (choice : NormalRootChoice) (direction : Fin 3)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterSpinorMonodromy choice (-1) matter) =
      d9DoubledMatterSpinorMonodromy choice (-1)
        (d9DoubledMatterFiberCliffordGamma direction matter) := by
  apply d9DoubledMatterSpinorMonodromy_injective choice 1
  calc
    d9DoubledMatterSpinorMonodromy choice 1
        (d9DoubledMatterFiberCliffordGamma direction
          (d9DoubledMatterSpinorMonodromy choice (-1) matter)) =
      d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterSpinorMonodromy choice 1
          (d9DoubledMatterSpinorMonodromy choice (-1) matter)) := by
        rw [d9DoubledMatterFiberCliffordGamma_monodromy_one]
    _ = d9DoubledMatterFiberCliffordGamma direction matter := by
      rw [← d9DoubledMatterSpinorMonodromy_add]
      simp
    _ =
      d9DoubledMatterSpinorMonodromy choice 1
        (d9DoubledMatterSpinorMonodromy choice (-1)
          (d9DoubledMatterFiberCliffordGamma direction matter)) := by
      rw [← d9DoubledMatterSpinorMonodromy_add]
      simp

/-- Every doubled Clifford generator commutes with every integer deck
monodromy. -/
theorem d9DoubledMatterFiberCliffordGamma_monodromy
    (choice : NormalRootChoice) (direction : Fin 3)
    (winding : Int) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9DoubledMatterFiberCliffordGamma direction matter) := by
  induction winding using Int.induction_on generalizing matter with
  | zero => simp
  | succ winding ih =>
      rw [d9DoubledMatterSpinorMonodromy_add]
      rw [ih]
      rw [d9DoubledMatterFiberCliffordGamma_monodromy_one]
      rw [← d9DoubledMatterSpinorMonodromy_add]
  | pred winding ih =>
      rw [show -(winding : Int) - 1 =
        -(winding : Int) + (-1) by ring]
      rw [d9DoubledMatterSpinorMonodromy_add]
      rw [ih]
      rw [d9DoubledMatterFiberCliffordGamma_monodromy_neg_one]
      rw [← d9DoubledMatterSpinorMonodromy_add]

/-- The same compatibility stated directly for every bundle coordinate
change. -/
theorem d9DoubledMatterFiberCliffordGamma_coordChange
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        ((smoothThroatDoubledMatterSpinorVectorBundleCore
          period hPeriod choice).coordChange first second base matter) =
      (smoothThroatDoubledMatterSpinorVectorBundleCore
          period hPeriod choice).coordChange first second base
        (d9DoubledMatterFiberCliffordGamma direction matter) := by
  exact d9DoubledMatterFiberCliffordGamma_monodromy choice direction
    (localTransitionWinding period hPeriod first second base) matter

structure ProgramPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D
    where
  choice : NormalRootChoice
  gamma : Fin 3 → D9DoubledMatterFiber →ₗ[Real] D9DoubledMatterFiber
  square : ∀ direction matter,
    gamma direction (gamma direction matter) = -matter
  anticommute : ∀ first second, first ≠ second → ∀ matter,
    gamma first (gamma second matter) =
      -gamma second (gamma first matter)
  coordinateCompatible : ∀ direction first second base matter,
    gamma direction
        ((smoothThroatDoubledMatterSpinorVectorBundleCore
          period hPeriod choice).coordChange first second base matter) =
      (smoothThroatDoubledMatterSpinorVectorBundleCore
          period hPeriod choice).coordChange first second base
        (gamma direction matter)

def programPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D :
    ProgramPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  gamma := d9DoubledMatterFiberCliffordGamma
  square := d9DoubledMatterFiberCliffordGamma_sq
  anticommute := d9DoubledMatterFiberCliffordGamma_anticommute
  coordinateCompatible :=
    d9DoubledMatterFiberCliffordGamma_coordChange period hPeriod
      .positiveQuarter

theorem programPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledGlobalDeckCliffordActionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
end JanusFormal
