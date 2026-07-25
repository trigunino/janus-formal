import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalOperatorClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientSpinCNonorientabilityNoGo4D

/-!
# Exact scope of “Janus as a consequence”

The present Program-P domain is already built on the reflected mapping torus.
To formulate a topology-selection theorem one must first compare it with at
least the untwisted clutching branch.

Both branches have the same local sector/symbol fingerprint, so local natural
operators cannot select between them.  In the two-clutching sector, the
determinant-line Pin-minus requirement does select the reflected Janus branch
uniquely: the untwisted branch has a periodic nowhere-zero determinant, while
the reflected branch would require the impossible anti-periodic determinant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPJanusBranchSelection4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusNaturalOperatorBlueprint
open P0EFTJanusMappingTorusLocalFrameNoGo4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle

/-- The two clutching classes actually compared by this theorem. -/
inductive TwoClutchingBranch where
  | untwisted
  | reflectedJanus
  deriving DecidableEq, Fintype, Repr

/-- A determinant lift for identity monodromy. -/
structure PeriodicFrameDeterminant (period : ℝ) where
  determinant : ℝ → ℝ
  continuous : Continuous determinant
  nowhereZero : ∀ time, determinant time ≠ 0
  periodic : ∀ time, determinant (time + period) = determinant time

/-- The constant determinant gives an orientation lift on the untwisted
branch. -/
def constantPeriodicFrameDeterminant
    (period : ℝ) : PeriodicFrameDeterminant period where
  determinant := fun _ => 1
  continuous := continuous_const
  nowhereZero := by intro; norm_num
  periodic := by intro; rfl

/-- Determinant-line descent type for each clutching class. -/
def DeterminantOrientationDescent
    (period : ℝ) : TwoClutchingBranch → Type
  | .untwisted => PeriodicFrameDeterminant period
  | .reflectedJanus => AntiPeriodicFrameDeterminant period

/-- Determinant-line nonorientability predicate. -/
def DeterminantLineNonorientable
    (period : ℝ) (branch : TwoClutchingBranch) : Prop :=
  IsEmpty (DeterminantOrientationDescent period branch)

/-- The untwisted branch is not nonorientable in this exact model. -/
theorem untwisted_not_determinantLineNonorientable
    (period : ℝ) :
    ¬ DeterminantLineNonorientable period .untwisted := by
  intro hEmpty
  exact hEmpty.false (constantPeriodicFrameDeterminant period)

/-- The reflected Janus branch is nonorientable in the determinant-line
model, by the existing intermediate-value theorem. -/
theorem reflectedJanus_determinantLineNonorientable
    (period : ℝ) :
    DeterminantLineNonorientable period .reflectedJanus := by
  exact no_antiPeriodicFrameDeterminant period

/-- Exact two-branch classification by determinant-line parity. -/
theorem determinantLineNonorientable_iff_reflectedJanus
    (period : ℝ) (branch : TwoClutchingBranch) :
    DeterminantLineNonorientable period branch ↔
      branch = .reflectedJanus := by
  cases branch with
  | untwisted =>
      constructor
      · intro h
        exact (untwisted_not_determinantLineNonorientable period h).elim
      · intro h
        contradiction
  | reflectedJanus =>
      simp [reflectedJanus_determinantLineNonorientable]

/-- Consequently determinant-line nonorientability selects one and only one
clutching branch. -/
theorem existsUnique_determinantLineNonorientable_branch
    (period : ℝ) :
    ∃! branch : TwoClutchingBranch,
      DeterminantLineNonorientable period branch := by
  refine ⟨.reflectedJanus,
    reflectedJanus_determinantLineNonorientable period, ?_⟩
  intro branch hBranch
  exact (determinantLineNonorientable_iff_reflectedJanus
    period branch).1 hBranch

/-- Orientation character of one clutching circuit. -/
def oneLoopOrientationParity : TwoClutchingBranch → ZMod 2
  | .untwisted => 0
  | .reflectedJanus => 1

/-- Compatibility with the already-derived Program-P normal `Pin⁻(1)`
generator means matching its orientation reduction after one circuit. -/
def CompatibleWithProgramPNormalPinMinus
    (branch : TwoClutchingBranch) : Prop :=
  oneLoopOrientationParity branch =
    normalPinMinusOrientationReduction (1 : NormalPinMinusOne)

/-- The existing normal `Pin⁻(1)` principal bundle has nontrivial one-loop
orientation reduction. -/
theorem programPNormalPinMinus_oneLoopOrientation_nontrivial :
    normalPinMinusOrientationReduction (1 : NormalPinMinusOne) = 1 := by
  norm_num [normalPinMinusOrientationReduction]

/-- Matching the Program-P normal root monodromy is exactly the reflected
clutching condition. -/
theorem compatibleWithProgramPNormalPinMinus_iff_reflectedJanus
    (branch : TwoClutchingBranch) :
    CompatibleWithProgramPNormalPinMinus branch ↔
      branch = .reflectedJanus := by
  cases branch <;>
    simp [CompatibleWithProgramPNormalPinMinus, oneLoopOrientationParity,
      programPNormalPinMinus_oneLoopOrientation_nontrivial]

/-- Thus the normal `Z₄`/`Pin⁻(1)` monodromy already present in Program P
selects one and only one branch in the two-clutching comparison. -/
theorem existsUnique_programPNormalPinMinus_compatible_branch :
    ∃! branch : TwoClutchingBranch,
      CompatibleWithProgramPNormalPinMinus branch := by
  refine ⟨.reflectedJanus, ?_, ?_⟩
  · exact
      (compatibleWithProgramPNormalPinMinus_iff_reflectedJanus
        .reflectedJanus).2 rfl
  · intro branch hBranch
    exact
      (compatibleWithProgramPNormalPinMinus_iff_reflectedJanus branch).1
        hBranch

/-- No new axiom is needed for the branch implication: retaining the
already-constructed nontrivial Program-P normal root monodromy forces Janus. -/
theorem janus_of_programPNormalPinMinus_compatibility
    (branch : TwoClutchingBranch)
    (hCompatible : CompatibleWithProgramPNormalPinMinus branch) :
    branch = .reflectedJanus :=
  (compatibleWithProgramPNormalPinMinus_iff_reflectedJanus branch).1
    hCompatible

/-- Local natural-operator data visible at the principal-symbol level. -/
def localNaturalSymbolFingerprint
    (_branch : TwoClutchingBranch)
    (sector : NaturalOperatorSector) : ℕ × ℕ :=
  (sectorDifferentialOrder sector, sectorRealRank sector)

/-- Identity and reflected clutchings have the same complete displayed local
sector/symbol fingerprint. -/
theorem localNaturalSymbolFingerprint_untwisted_eq_reflectedJanus :
    localNaturalSymbolFingerprint .untwisted =
      localNaturalSymbolFingerprint .reflectedJanus := by
  rfl

/-- Local-symbol admissibility deliberately contains no global clutching
datum. -/
def LocallySymbolAdmissible (branch : TwoClutchingBranch) : Prop :=
  localNaturalSymbolFingerprint branch =
    localNaturalSymbolFingerprint .reflectedJanus

theorem everyBranch_locallySymbolAdmissible
    (branch : TwoClutchingBranch) :
    LocallySymbolAdmissible branch := by
  cases branch <;> rfl

/-- No-go: even the full displayed principal-symbol fingerprint cannot select
the Janus clutching. -/
theorem localNaturalSymbols_do_not_select_unique_clutching :
    ¬ ∃! branch : TwoClutchingBranch,
      LocallySymbolAdmissible branch := by
  rintro ⟨selected, hSelected, hUnique⟩
  have hUntwisted :=
    hUnique .untwisted (everyBranch_locallySymbolAdmissible .untwisted)
  have hReflected :=
    hUnique .reflectedJanus
      (everyBranch_locallySymbolAdmissible .reflectedJanus)
  have hEqual : TwoClutchingBranch.untwisted =
      TwoClutchingBranch.reflectedJanus :=
    hUntwisted.trans hReflected.symm
  contradiction

/-- The current common domain has no topology variable: every inhabitant is
indexed by the reflected mapping-torus carrier from its type definition. -/
def currentProgramPClutchingBranch
    {period : ℝ} {hPeriod : period ≠ 0}
    (_domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    TwoClutchingBranch :=
  .reflectedJanus

@[simp]
theorem currentProgramPClutchingBranch_eq_reflectedJanus
    {period : ℝ} {hPeriod : period ≠ 0}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    currentProgramPClutchingBranch domain = .reflectedJanus := by
  rfl

/-- Strongest valid “Janus consequence” statement at present: once the
configuration category is broadened to the two clutching branches and
determinant-line nonorientability is derived, the selected branch is Janus. -/
theorem janus_of_derived_determinantLineNonorientability
    (period : ℝ)
    (branch : TwoClutchingBranch)
    (hNonorientable : DeterminantLineNonorientable period branch) :
    branch = .reflectedJanus :=
  (determinantLineNonorientable_iff_reflectedJanus period branch).1
    hNonorientable

end

end P0EFTJanusProgramPJanusBranchSelection4D
end JanusFormal
