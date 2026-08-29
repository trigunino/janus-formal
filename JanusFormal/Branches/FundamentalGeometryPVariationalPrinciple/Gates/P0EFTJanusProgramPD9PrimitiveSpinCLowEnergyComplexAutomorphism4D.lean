import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeComplexAutomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D

/-!
# Geometric low-energy complex Dirac automorphism

The genuine Hopf zero-mode complex line and the genuine signed complex first
sphere packet have squared Dirac eigenvalues `k²` and `k² + 2`.  Their exact
spectral separation proves that the two smooth-section subspaces are
disjoint, without requiring joint injectivity of the abstract first-sphere
coefficient synthesis.

The direct product of the two geometric ranges therefore embeds faithfully by
addition into the actual primitive SpinC smooth-section core.  On its range,
the genuine differential Dirac operator is conjugate to the product of the
two previously constructed geometric automorphisms.  In particular the full
zero-plus-first-level complex block has zero kernel and an explicit linear
automorphism structure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Product of the genuine geometric zero-mode line and genuine geometric
signed first-sphere range at one common root/circle label. -/
abbrev PrimitiveSpinCLowEnergyComplexBlocks
    (sector : NormalRootChoice) (mode : Int) :=
  PrimitiveSpinCHopfZeroModeComplexSpan period hPeriod sector mode ×
    PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode

/-- The zero-mode geometric complex line has squared Dirac eigenvalue `k²`. -/
theorem primitiveSpinCHopfZeroModeComplexSpan_dirac_sq
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfZeroModeComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state.1) =
      normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 •
        state.1 := by
  have hDirac := congrArg
    (fun current : PrimitiveSpinCHopfZeroModeComplexSpan
        period hPeriod sector mode => current.1)
    (primitiveSpinCHopfZeroModeComplexActualDirac_eq_smul
      period hPeriod sector mode state)
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 =
      (-normalRootLeviCivitaCorrectedFrequency
        period sector mode) • state.1 at hDirac
  calc
    d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state.1) =
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector mode) • state.1) := by
          rw [hDirac]
    _ = (-normalRootLeviCivitaCorrectedFrequency
          period sector mode) •
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state.1 := by
          rw [d9PrimitiveSpinCGeometricDiracOperator_real_smul]
    _ = (-normalRootLeviCivitaCorrectedFrequency
          period sector mode) •
        ((-normalRootLeviCivitaCorrectedFrequency
          period sector mode) • state.1) := by
          rw [hDirac]
    _ = normalRootLeviCivitaCorrectedFrequency
          period sector mode ^ 2 • state.1 := by
          module

/-- The zero Hopf complex line and signed first-sphere complex range are
geometrically disjoint because their squared eigenvalues differ by exactly
`2`. -/
theorem primitiveSpinCHopfZeroModeComplexSpan_disjoint_firstSphere
    (sector : NormalRootChoice) (mode : Int) :
    Disjoint
      (PrimitiveSpinCHopfZeroModeComplexSpan
        period hPeriod sector mode)
      (PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode) := by
  apply Submodule.disjoint_def.mpr
  intro state hZero hFirst
  let zeroState : PrimitiveSpinCHopfZeroModeComplexSpan
      period hPeriod sector mode :=
    ⟨state, hZero⟩
  let firstState : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode :=
    ⟨state, hFirst⟩
  have hZeroSq :=
    primitiveSpinCHopfZeroModeComplexSpan_dirac_sq
      period hPeriod sector mode zeroState
  have hFirstSq := congrArg
    (fun current : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode => current.1)
    (primitiveSpinCHopfFirstSphereSignedComplexActualDirac_sq
      period hPeriod sector mode firstState)
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state) =
      normalRootLeviCivitaCorrectedFrequency
        period sector mode ^ 2 • state at hZeroSq
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state) =
      (normalRootLeviCivitaCorrectedFrequency
        period sector mode ^ 2 + 2) • state at hFirstSq
  have hTwo : (2 : Real) • state = 0 := by
    calc
      (2 : Real) • state =
          (normalRootLeviCivitaCorrectedFrequency
              period sector mode ^ 2 + 2) • state -
            normalRootLeviCivitaCorrectedFrequency
              period sector mode ^ 2 • state := by
                module
      _ =
          d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter
              (d9PrimitiveSpinCGeometricDiracOperator
                period hPeriod .positiveQuarter state) -
            d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter
              (d9PrimitiveSpinCGeometricDiracOperator
                period hPeriod .positiveQuarter state) := by
                rw [← hFirstSq, ← hZeroSq]
      _ = 0 := sub_self _
  exact (smul_eq_zero.mp hTwo).resolve_left (by norm_num)

/-- Add the two genuine geometric blocks as actual primitive SpinC smooth
sections. -/
def primitiveSpinCHopfLowEnergyComplexAddition
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyComplexBlocks period hPeriod sector mode →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun blocks := blocks.1.1 + blocks.2.1
  map_add' first second := by
    change
      (first.1.1 + second.1.1) + (first.2.1 + second.2.1) =
        (first.1.1 + first.2.1) + (second.1.1 + second.2.1)
    module
  map_smul' scalar blocks := by
    change
      scalar • blocks.1.1 + scalar • blocks.2.1 =
        scalar • (blocks.1.1 + blocks.2.1)
    rw [smul_add]

@[simp]
theorem primitiveSpinCHopfLowEnergyComplexAddition_apply
    (sector : NormalRootChoice) (mode : Int)
    (blocks : PrimitiveSpinCLowEnergyComplexBlocks
      period hPeriod sector mode) :
    primitiveSpinCHopfLowEnergyComplexAddition
        period hPeriod sector mode blocks =
      blocks.1.1 + blocks.2.1 :=
  rfl

/-- Spectral separation makes addition of the two actual geometric ranges
faithful. -/
theorem primitiveSpinCHopfLowEnergyComplexAddition_injective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfLowEnergyComplexAddition
        period hPeriod sector mode) := by
  intro first second hEqual
  have hDifference :
      (first.1.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - second.1.1 =
        (second.2.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - first.2.1 := by
    change first.1.1 + first.2.1 = second.1.1 + second.2.1 at hEqual
    calc
      first.1.1 - second.1.1 =
          (first.1.1 + first.2.1) -
            (second.1.1 + first.2.1) := by abel
      _ = (second.1.1 + second.2.1) -
            (second.1.1 + first.2.1) := by rw [hEqual]
      _ = second.2.1 - first.2.1 := by abel
  have hZeroMem :
      (first.1.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - second.1.1 ∈
        PrimitiveSpinCHopfZeroModeComplexSpan
          period hPeriod sector mode :=
    Submodule.sub_mem _ first.1.property second.1.property
  have hFirstMem :
      (first.1.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - second.1.1 ∈
        PrimitiveSpinCHopfFirstSphereSignedComplexSpan
          period hPeriod sector mode := by
    rw [hDifference]
    exact Submodule.sub_mem _ second.2.property first.2.property
  have hZeroDifference :
      (first.1.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - second.1.1 = 0 :=
    (Submodule.disjoint_def.mp
      (primitiveSpinCHopfZeroModeComplexSpan_disjoint_firstSphere
        period hPeriod sector mode))
      ((first.1.1 : D9PrimitiveSpinCSmoothSection
        period hPeriod .positiveQuarter) - second.1.1)
      hZeroMem hFirstMem
  have hFirstDifference :
      (second.2.1 : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - first.2.1 = 0 := by
    rw [← hDifference]
    exact hZeroDifference
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hZeroDifference
  · apply Subtype.ext
    exact (sub_eq_zero.mp hFirstDifference).symm

/-- The actual smooth-section low-energy range. -/
abbrev PrimitiveSpinCHopfLowEnergyComplexSpan
    (sector : NormalRootChoice) (mode : Int) :=
  LinearMap.range
    (primitiveSpinCHopfLowEnergyComplexAddition
      period hPeriod sector mode)

/-- Exact coordinates on the actual low-energy geometric smooth-section
range. -/
def primitiveSpinCHopfLowEnergyComplexAdditionEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyComplexBlocks period hPeriod sector mode ≃ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfLowEnergyComplexAddition
      period hPeriod sector mode)
    (primitiveSpinCHopfLowEnergyComplexAddition_injective
      period hPeriod sector mode)

/-- Product of the genuine zero-mode and first-sphere geometric Dirac
automorphisms. -/
def primitiveSpinCHopfLowEnergyComplexBlockDiracLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyComplexBlocks period hPeriod sector mode ≃ₗ[Real]
      PrimitiveSpinCLowEnergyComplexBlocks period hPeriod sector mode :=
  (primitiveSpinCHopfZeroModeComplexActualDiracLinearEquiv
      period hPeriod sector mode).prodCongr
    (primitiveSpinCHopfFirstSphereSignedComplexActualDiracLinearEquiv
      period hPeriod sector mode)

/-- The ambient differential Dirac operator intertwines geometric addition
with the product block automorphism. -/
theorem primitiveSpinCHopfLowEnergyComplexAddition_intertwines_dirac
    (sector : NormalRootChoice) (mode : Int)
    (blocks : PrimitiveSpinCLowEnergyComplexBlocks
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfLowEnergyComplexAddition
          period hPeriod sector mode blocks) =
      primitiveSpinCHopfLowEnergyComplexAddition
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexBlockDiracLinearEquiv
          period hPeriod sector mode blocks) := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (blocks.1.1 + blocks.2.1) =
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter blocks.1.1 +
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter blocks.2.1
  exact d9PrimitiveSpinCGeometricDiracOperator_add
    period hPeriod blocks.1.1 blocks.2.1

/-- The genuine differential Dirac operator preserves the combined actual
low-energy geometric span. -/
theorem primitiveSpinCHopfLowEnergyComplexSpan_dirac_mem
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfLowEnergyComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 ∈
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode := by
  rcases state.property with ⟨blocks, hBlocks⟩
  refine ⟨primitiveSpinCHopfLowEnergyComplexBlockDiracLinearEquiv
    period hPeriod sector mode blocks, ?_⟩
  rw [← hBlocks]
  exact
    (primitiveSpinCHopfLowEnergyComplexAddition_intertwines_dirac
      period hPeriod sector mode blocks).symm

/-- Restriction of the genuine differential Dirac operator to the actual
zero-plus-first-level complex smooth-section span. -/
def primitiveSpinCHopfLowEnergyComplexActualDirac
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode →ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode where
  toFun state :=
    ⟨d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1,
      primitiveSpinCHopfLowEnergyComplexSpan_dirac_mem
        period hPeriod sector mode state⟩
  map_add' first second := by
    apply Subtype.ext
    exact d9PrimitiveSpinCGeometricDiracOperator_add
      period hPeriod first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    exact d9PrimitiveSpinCGeometricDiracOperator_real_smul
      period hPeriod .positiveQuarter scalar state.1

/-- In exact low-energy geometric coordinates, the actual differential Dirac
operator is the product block automorphism. -/
@[simp]
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_additionEquiv
    (sector : NormalRootChoice) (mode : Int)
    (blocks : PrimitiveSpinCLowEnergyComplexBlocks
      period hPeriod sector mode) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexAdditionEquiv
          period hPeriod sector mode blocks) =
      primitiveSpinCHopfLowEnergyComplexAdditionEquiv
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexBlockDiracLinearEquiv
          period hPeriod sector mode blocks) := by
  apply Subtype.ext
  exact primitiveSpinCHopfLowEnergyComplexAddition_intertwines_dirac
    period hPeriod sector mode blocks

/-- Linear equivalence obtained by conjugating the product block Dirac with
exact geometric addition coordinates. -/
def primitiveSpinCHopfLowEnergyComplexActualDiracLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode ≃ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode :=
  ((primitiveSpinCHopfLowEnergyComplexAdditionEquiv
      period hPeriod sector mode).symm.trans
    (primitiveSpinCHopfLowEnergyComplexBlockDiracLinearEquiv
      period hPeriod sector mode)).trans
    (primitiveSpinCHopfLowEnergyComplexAdditionEquiv
      period hPeriod sector mode)

/-- The conjugated equivalence has exactly the genuine differential Dirac
operator as its underlying linear map. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_eq_linearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfLowEnergyComplexActualDiracLinearEquiv
        period hPeriod sector mode).toLinearMap := by
  apply LinearMap.ext
  intro state
  rcases (primitiveSpinCHopfLowEnergyComplexAdditionEquiv
    period hPeriod sector mode).surjective state with ⟨blocks, rfl⟩
  rw [primitiveSpinCHopfLowEnergyComplexActualDirac_additionEquiv]
  simp [primitiveSpinCHopfLowEnergyComplexActualDiracLinearEquiv]

/-- The genuine differential Dirac restriction on the combined low-energy
complex span is bijective. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_bijective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Bijective
      (primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode) := by
  rw [primitiveSpinCHopfLowEnergyComplexActualDirac_eq_linearEquiv]
  exact
    (primitiveSpinCHopfLowEnergyComplexActualDiracLinearEquiv
      period hPeriod sector mode).bijective

/-- The combined actual low-energy geometric block has no Dirac zero mode. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_ker_eq_bot
    (sector : NormalRootChoice) (mode : Int) :
    LinearMap.ker
        (primitiveSpinCHopfLowEnergyComplexActualDirac
          period hPeriod sector mode) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (primitiveSpinCHopfLowEnergyComplexActualDirac_bijective
      period hPeriod sector mode).1

/-- Consolidated zero-plus-first-level geometric complex closure. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDiracAutomorphism_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfLowEnergyComplexAddition
          period hPeriod sector mode) ∧
      Function.Bijective
        (primitiveSpinCHopfLowEnergyComplexActualDirac
          period hPeriod sector mode) ∧
      LinearMap.ker
          (primitiveSpinCHopfLowEnergyComplexActualDirac
            period hPeriod sector mode) = ⊥ ∧
      primitiveSpinCHopfLowEnergyComplexActualDirac
          period hPeriod sector mode =
        (primitiveSpinCHopfLowEnergyComplexActualDiracLinearEquiv
          period hPeriod sector mode).toLinearMap :=
  ⟨primitiveSpinCHopfLowEnergyComplexAddition_injective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_bijective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_ker_eq_bot
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_eq_linearEquiv
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
end JanusFormal
