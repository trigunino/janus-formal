import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle

/-!
# PT conjugation of the global normal `Z4` root lines

Complex conjugation exchanges the two global quarter-root descent data.  The
map is a real-linear isometric involution and intertwines every deck transition,
not only the generator.  This is the bundle-level cocycle compatibility needed
by PT; it does not construct an ambient SpinC or Pin principal bundle.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusNormalRootPTConjugation

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusNormalPinLiftBoundaryConditions
open scoped ComplexConjugate

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Conjugation sends either selected quarter multiplier to the other one. -/
@[simp] theorem conj_normalRootMultiplier (choice : NormalRootChoice) :
    conj (normalRootMultiplier choice) =
      normalRootMultiplier (oppositeRoot choice) := by
  cases choice <;>
    simp [normalRootMultiplier, oppositeRoot]

/-- PT conjugation exchanges the two winding representations for every
integer winding, including negative windings. -/
@[simp] theorem conj_quarterRootRepresentation
    (choice : NormalRootChoice) (winding : ℤ) :
    conj (quarterRootRepresentation choice winding) =
      quarterRootRepresentation (oppositeRoot choice) winding := by
  simp only [quarterRootRepresentation]
  change Complex.conjAe (normalRootMultiplier choice ^ winding) = _
  rw [map_zpow₀ Complex.conjAe]
  simp

/-- Fiberwise PT on the real underlier of either complex root line. -/
def rootPTConjugation : ℂ ≃L[ℝ] ℂ :=
  Complex.conjCLE

@[simp] theorem rootPTConjugation_apply (root : ℂ) :
    rootPTConjugation root = conj root := by
  rfl

@[simp] theorem rootPTConjugation_involutive (root : ℂ) :
    rootPTConjugation (rootPTConjugation root) = root := by
  simp

/-- Conjugation intertwines the real-linear transition maps for every deck
winding. -/
theorem rootPTConjugation_intertwines
    (choice : NormalRootChoice) (winding : ℤ) (root : ℂ) :
    rootPTConjugation
        (quarterRootRealCLM choice winding root) =
      quarterRootRealCLM (oppositeRoot choice) winding
        (rootPTConjugation root) := by
  simp [quarterRootRealCLM_apply, map_mul]

/-- The intertwining identity holds on every overlap of the actual smooth
root-bundle cores.  Hence conjugation is compatible with their full descent
cocycles, rather than just with one chosen loop. -/
theorem rootPTConjugation_coordChange
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) (root : ℂ) :
    rootPTConjugation
        ((fixedThroatNormalZ4RootRealBundleCore period hPeriod choice).coordChange
          first second base root) =
      (fixedThroatNormalZ4RootRealBundleCore period hPeriod
          (oppositeRoot choice)).coordChange first second base
        (rootPTConjugation root) := by
  exact rootPTConjugation_intertwines choice
    (localTransitionWinding period hPeriod first second base) root

/-- Applying the descent-compatible PT map twice returns the original root
choice and fiber coordinate. -/
theorem rootPTConjugation_double
    (choice : NormalRootChoice) (root : ℂ) :
    (oppositeRoot (oppositeRoot choice),
        rootPTConjugation (rootPTConjugation root)) = (choice, root) := by
  simp

end

end P0EFTJanusMappingTorusNormalRootPTConjugation
end JanusFormal
