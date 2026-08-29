import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D

/-!
# Geometric unitary in the signed Hessian labels

The global Fourier--monopole unitary is regrouped by finite spectral blocks.
This file refines it to the individual signed labels used by the physical
Hessian.  Each label is represented by one vector of the corresponding
geometric orthonormal branch basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Module
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev GeometricL2 :=
  D9PrimitiveSpinCGeometricL2Completion
    period hPeriod .positiveQuarter

private def signedBranchBasisIndex
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    Fin
      (finrank Complex
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode)) :=
  Fin.cast
    (primitiveSpinCGeometricL2SignedBranchBlock_finrank
      period hPeriod positiveLevel branch sector circleMode).symm
    multiplicity

/-- One normalized smooth geometric eigensection for each exact signed
coefficient label of the Hessian. -/
def primitiveSpinCGeometricSignedModeSmoothVector :
    PrimitiveSpinCGeometricSignedMode → SmoothSection period hPeriod
  | (sector, .inl (multiplicity, circleMode)) =>
      primitiveSpinCGeometricL2OrthonormalBlockFamily
        period hPeriod 0 sector circleMode multiplicity
  | (sector, .inr mode) =>
      primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
        period hPeriod mode.level mode.branch sector mode.circleMode
        (signedBranchBasisIndex period hPeriod mode.level mode.branch
          sector mode.circleMode mode.multiplicity)

/-- The same signed mode in the independent geometric completion. -/
def primitiveSpinCGeometricSignedModeVector
    (mode : PrimitiveSpinCGeometricSignedMode) :
    GeometricL2 period hPeriod :=
  (primitiveSpinCGeometricSignedModeSmoothVector
    period hPeriod mode : GeometricL2 period hPeriod)

theorem primitiveSpinCGeometricSignedModeVector_norm
    (mode : PrimitiveSpinCGeometricSignedMode) :
    ‖primitiveSpinCGeometricSignedModeVector
        period hPeriod mode‖ = 1 := by
  rcases mode with ⟨sector, mode⟩
  cases mode with
  | inl zeroMode =>
      rcases zeroMode with ⟨multiplicity, circleMode⟩
      rw [primitiveSpinCGeometricSignedModeVector,
        UniformSpace.Completion.norm_coe]
      exact
        (primitiveSpinCGeometricL2OrthonormalBlockFamily_orthonormal
          period hPeriod 0 sector circleMode).1 multiplicity
  | inr positiveMode =>
      rcases positiveMode with
        ⟨branch, positiveLevel, multiplicity, circleMode⟩
      rw [primitiveSpinCGeometricSignedModeVector,
        UniformSpace.Completion.norm_coe]
      exact
        (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_orthonormal
          period hPeriod positiveLevel branch sector circleMode).1
          (signedBranchBasisIndex period hPeriod positiveLevel branch
            sector circleMode multiplicity)

@[simp]
theorem primitiveSpinCGeometricL2CompletedBlockIsometry_single_one
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel)) :
    primitiveSpinCGeometricL2CompletedBlockIsometry
        period hPeriod ⟨sphereLevel, sector, circleMode⟩
        (EuclideanSpace.single multiplicity (1 : Complex)) =
      (primitiveSpinCGeometricL2OrthonormalBlockFamily
        period hPeriod sphereLevel sector circleMode multiplicity :
          GeometricL2 period hPeriod) := by
  rw [primitiveSpinCGeometricL2CompletedBlockIsometry_apply]
  have hSmooth :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode
          (EuclideanSpace.single multiplicity (1 : Complex)) =
        primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity := by
    change
      (∑ index,
        (EuclideanSpace.single multiplicity (1 : Complex)) index •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod sphereLevel sector circleMode index) =
        primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity
    classical
    rw [Finset.sum_eq_single multiplicity]
    · simp
    · intro index _ hIndex
      simp [hIndex]
    · simp
  exact congrArg
    (fun state : SmoothSection period hPeriod =>
      (state : GeometricL2 period hPeriod)) hSmooth

@[simp]
theorem primitiveSpinCGeometricL2CompletedSignedBranchIsometry_single_one
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (index :
      Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBranchBlock
            period hPeriod positiveLevel branch sector circleMode))) :
    primitiveSpinCGeometricL2CompletedSignedBranchIsometry
        period hPeriod positiveLevel branch sector circleMode
        (EuclideanSpace.single index (1 : Complex)) =
      (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
        period hPeriod positiveLevel branch sector circleMode index :
          GeometricL2 period hPeriod) := by
  have hSmooth :
      primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode
          (EuclideanSpace.single index (1 : Complex)) =
        primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode index := by
    change
      (∑ other,
        (EuclideanSpace.single index (1 : Complex)) other •
          primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
            period hPeriod positiveLevel branch sector circleMode other) =
        primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode index
    classical
    rw [Finset.sum_eq_single index]
    · simp
    · intro other _ hOther
      simp [hOther]
    · simp
  have hCompleted :
      primitiveSpinCGeometricL2CompletedSignedBranchIsometry
          period hPeriod positiveLevel branch sector circleMode
          (EuclideanSpace.single index (1 : Complex)) =
        (primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode
          (EuclideanSpace.single index (1 : Complex)) :
            GeometricL2 period hPeriod) :=
    rfl
  rw [hCompleted]
  exact congrArg
    (fun state : SmoothSection period hPeriod =>
      (state : GeometricL2 period hPeriod)) hSmooth

/-- The normalized geometric representatives are orthogonal for distinct
signed Hessian labels. -/
theorem primitiveSpinCGeometricSignedModeVector_inner_eq_zero
    (first second : PrimitiveSpinCGeometricSignedMode)
    (hModes : first ≠ second) :
    inner Complex
        (primitiveSpinCGeometricSignedModeVector
          period hPeriod first)
        (primitiveSpinCGeometricSignedModeVector
          period hPeriod second) = 0 := by
  rcases first with ⟨firstSector, firstMode⟩
  rcases second with ⟨secondSector, secondMode⟩
  cases firstMode with
  | inl firstZero =>
      rcases firstZero with ⟨firstMultiplicity, firstCircleMode⟩
      cases secondMode with
      | inl secondZero =>
          rcases secondZero with
            ⟨secondMultiplicity, secondCircleMode⟩
          by_cases hSector : firstSector = secondSector
          · subst secondSector
            by_cases hCircle : firstCircleMode = secondCircleMode
            · subst secondCircleMode
              rw [primitiveSpinCGeometricSignedModeVector,
                primitiveSpinCGeometricSignedModeVector,
                UniformSpace.Completion.inner_coe]
              apply
                (primitiveSpinCGeometricL2OrthonormalBlockFamily_orthonormal
                  period hPeriod 0 firstSector firstCircleMode).2
              intro hMultiplicity
              subst secondMultiplicity
              exact hModes rfl
            · rw [
                primitiveSpinCGeometricSignedModeVector,
                primitiveSpinCGeometricSignedModeVector,
                primitiveSpinCGeometricSignedModeSmoothVector,
                primitiveSpinCGeometricSignedModeSmoothVector,
                ← primitiveSpinCGeometricL2CompletedBlockIsometry_single_one
                  period hPeriod 0 firstSector firstCircleMode
                    firstMultiplicity,
                ← primitiveSpinCGeometricL2CompletedBlockIsometry_single_one
                  period hPeriod 0 firstSector secondCircleMode
                    secondMultiplicity]
              exact
                primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
                  period hPeriod (by
                    intro hBlocks
                    exact hCircle
                      (congrArg
                        PrimitiveSpinCGeometricL2BlockIndex.circleMode
                        hBlocks))
                  _ _
          · rw [
              primitiveSpinCGeometricSignedModeVector,
              primitiveSpinCGeometricSignedModeVector,
              primitiveSpinCGeometricSignedModeSmoothVector,
              primitiveSpinCGeometricSignedModeSmoothVector,
              ← primitiveSpinCGeometricL2CompletedBlockIsometry_single_one
                period hPeriod 0 firstSector firstCircleMode
                  firstMultiplicity,
              ← primitiveSpinCGeometricL2CompletedBlockIsometry_single_one
                period hPeriod 0 secondSector secondCircleMode
                  secondMultiplicity]
            exact
              primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
                period hPeriod (by
                  intro hBlocks
                  exact hSector
                    (congrArg PrimitiveSpinCGeometricL2BlockIndex.sector
                      hBlocks))
                _ _
      | inr secondPositive =>
          rcases secondPositive with
            ⟨secondBranch, secondLevel, secondMultiplicity,
              secondCircleMode⟩
          rw [primitiveSpinCGeometricSignedModeVector,
            primitiveSpinCGeometricSignedModeVector,
            UniformSpace.Completion.inner_coe]
          apply Submodule.isOrtho_iff_inner_eq.mp
            (primitiveSpinCGeometricL2RawZeroBlockSpan_signedBranch_isOrtho
              period hPeriod firstSector secondSector firstCircleMode
                secondCircleMode secondLevel secondBranch)
          · rw [
              ← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
                period hPeriod 0 firstSector firstCircleMode]
            exact Submodule.subset_span (Set.mem_range_self firstMultiplicity)
          · exact
              (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                period hPeriod secondLevel secondBranch secondSector
                  secondCircleMode
                (signedBranchBasisIndex period hPeriod secondLevel
                  secondBranch secondSector secondCircleMode
                  secondMultiplicity)).property
  | inr firstPositive =>
      rcases firstPositive with
        ⟨firstBranch, firstLevel, firstMultiplicity, firstCircleMode⟩
      cases secondMode with
      | inl secondZero =>
          rcases secondZero with
            ⟨secondMultiplicity, secondCircleMode⟩
          rw [primitiveSpinCGeometricSignedModeVector,
            primitiveSpinCGeometricSignedModeVector,
            UniformSpace.Completion.inner_coe]
          apply Submodule.isOrtho_iff_inner_eq.mp
            (primitiveSpinCGeometricL2RawZeroBlockSpan_signedBranch_isOrtho
              period hPeriod secondSector firstSector secondCircleMode
                firstCircleMode firstLevel firstBranch).symm
          · exact
              (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                period hPeriod firstLevel firstBranch firstSector
                  firstCircleMode
                (signedBranchBasisIndex period hPeriod firstLevel
                  firstBranch firstSector firstCircleMode
                  firstMultiplicity)).property
          · rw [
              ← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
                period hPeriod 0 secondSector secondCircleMode]
            exact
              Submodule.subset_span (Set.mem_range_self secondMultiplicity)
      | inr secondPositive =>
          rcases secondPositive with
            ⟨secondBranch, secondLevel, secondMultiplicity,
              secondCircleMode⟩
          rw [primitiveSpinCGeometricSignedModeVector,
            primitiveSpinCGeometricSignedModeVector,
            UniformSpace.Completion.inner_coe]
          by_cases hLevel : firstLevel = secondLevel
          · subst secondLevel
            by_cases hSector : firstSector = secondSector
            · subst secondSector
              by_cases hCircle : firstCircleMode = secondCircleMode
              · subst secondCircleMode
                by_cases hBranch : firstBranch = secondBranch
                · subst secondBranch
                  apply
                    (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_orthonormal
                      period hPeriod firstLevel firstBranch firstSector
                        firstCircleMode).2
                  intro hIndex
                  have hMultiplicity :
                      firstMultiplicity = secondMultiplicity := by
                    apply Fin.ext
                    simpa [signedBranchBasisIndex] using
                      congrArg Fin.val hIndex
                  subst secondMultiplicity
                  exact hModes rfl
                · cases firstBranch <;> cases secondBranch
                  · exact (hBranch rfl).elim
                  · apply Submodule.isOrtho_iff_inner_eq.mp
                      (primitiveSpinCGeometricL2SignedBranchBlocks_isOrtho
                        period hPeriod firstLevel firstSector
                          firstCircleMode)
                    · exact
                        (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                          period hPeriod firstLevel .positive firstSector
                            firstCircleMode
                          (signedBranchBasisIndex period hPeriod firstLevel
                            .positive firstSector firstCircleMode
                            firstMultiplicity)).property
                    · exact
                        (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                          period hPeriod firstLevel .negative firstSector
                            firstCircleMode
                          (signedBranchBasisIndex period hPeriod firstLevel
                            .negative firstSector firstCircleMode
                            secondMultiplicity)).property
                  · apply Submodule.isOrtho_iff_inner_eq.mp
                      (primitiveSpinCGeometricL2SignedBranchBlocks_isOrtho
                        period hPeriod firstLevel firstSector
                          firstCircleMode).symm
                    · exact
                        (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                          period hPeriod firstLevel .negative firstSector
                            firstCircleMode
                          (signedBranchBasisIndex period hPeriod firstLevel
                            .negative firstSector firstCircleMode
                            firstMultiplicity)).property
                    · exact
                        (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                          period hPeriod firstLevel .positive firstSector
                            firstCircleMode
                          (signedBranchBasisIndex period hPeriod firstLevel
                            .positive firstSector firstCircleMode
                            secondMultiplicity)).property
                  · exact (hBranch rfl).elim
              · apply Submodule.isOrtho_iff_inner_eq.mp
                  (primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
                    period hPeriod firstLevel firstLevel firstBranch
                      secondBranch firstSector firstSector firstCircleMode
                      secondCircleMode (Or.inr (Or.inr hCircle)))
                · exact
                    (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                      period hPeriod firstLevel firstBranch firstSector
                        firstCircleMode
                      (signedBranchBasisIndex period hPeriod firstLevel
                        firstBranch firstSector firstCircleMode
                        firstMultiplicity)).property
                · exact
                    (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                      period hPeriod firstLevel secondBranch firstSector
                        secondCircleMode
                      (signedBranchBasisIndex period hPeriod firstLevel
                        secondBranch firstSector secondCircleMode
                        secondMultiplicity)).property
            · apply Submodule.isOrtho_iff_inner_eq.mp
                (primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
                  period hPeriod firstLevel firstLevel firstBranch
                    secondBranch firstSector secondSector firstCircleMode
                    secondCircleMode (Or.inr (Or.inl hSector)))
              · exact
                  (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                    period hPeriod firstLevel firstBranch firstSector
                      firstCircleMode
                    (signedBranchBasisIndex period hPeriod firstLevel
                      firstBranch firstSector firstCircleMode
                      firstMultiplicity)).property
              · exact
                  (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                    period hPeriod firstLevel secondBranch secondSector
                      secondCircleMode
                    (signedBranchBasisIndex period hPeriod firstLevel
                      secondBranch secondSector secondCircleMode
                      secondMultiplicity)).property
          · apply Submodule.isOrtho_iff_inner_eq.mp
              (primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
                period hPeriod firstLevel secondLevel firstBranch
                  secondBranch firstSector secondSector firstCircleMode
                  secondCircleMode (Or.inl hLevel))
            · exact
                (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                  period hPeriod firstLevel firstBranch firstSector
                    firstCircleMode
                  (signedBranchBasisIndex period hPeriod firstLevel
                    firstBranch firstSector firstCircleMode
                    firstMultiplicity)).property
            · exact
                (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
                  period hPeriod secondLevel secondBranch secondSector
                    secondCircleMode
                  (signedBranchBasisIndex period hPeriod secondLevel
                    secondBranch secondSector secondCircleMode
                    secondMultiplicity)).property

/-- Individual signed Hessian labels form an orthonormal geometric family. -/
theorem primitiveSpinCGeometricSignedModeVector_orthonormal :
    Orthonormal Complex
      (primitiveSpinCGeometricSignedModeVector period hPeriod) :=
  ⟨primitiveSpinCGeometricSignedModeVector_norm period hPeriod,
    fun _ _ hModes =>
      primitiveSpinCGeometricSignedModeVector_inner_eq_zero
        period hPeriod _ _ hModes⟩

/-- Isometric synthesis on the exact coefficient space used by the signed
matter Hessian. -/
def primitiveSpinCGeometricSignedModeSynthesis :
    ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode →ₗᵢ[Complex]
      GeometricL2 period hPeriod :=
  (primitiveSpinCGeometricSignedModeVector_orthonormal
    period hPeriod).orthogonalFamily.linearIsometry

@[simp]
theorem primitiveSpinCGeometricSignedModeSynthesis_single
    (mode : PrimitiveSpinCGeometricSignedMode) (coefficient : Complex) :
    primitiveSpinCGeometricSignedModeSynthesis period hPeriod
        (lp.single 2 mode coefficient) =
      coefficient •
        primitiveSpinCGeometricSignedModeVector period hPeriod mode := by
  rw [primitiveSpinCGeometricSignedModeSynthesis,
    OrthogonalFamily.linearIsometry_apply_single]
  rfl

theorem primitiveSpinCGeometricSignedModeVector_mem_synthesisRange
    (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCGeometricSignedModeVector period hPeriod mode ∈
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  refine ⟨lp.single 2 mode (1 : Complex), ?_⟩
  change
    primitiveSpinCGeometricSignedModeSynthesis period hPeriod
        (lp.single 2 mode (1 : Complex)) =
      primitiveSpinCGeometricSignedModeVector period hPeriod mode
  rw [primitiveSpinCGeometricSignedModeSynthesis_single, one_smul]

private theorem zeroBlock_mem_signedModeSynthesisRange
    (sector : NormalRootChoice) (circleMode : Int)
    (state : SmoothSection period hPeriod)
    (hState :
      state ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod 0 sector circleMode))) :
    (state : GeometricL2 period hPeriod) ∈
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  let range :=
    LinearMap.range
      (primitiveSpinCGeometricSignedModeSynthesis
        period hPeriod).toLinearMap
  refine Submodule.span_induction
    (R := Complex) (M := SmoothSection period hPeriod)
    (s := Set.range
      (primitiveSpinCGeometricL2OrthonormalBlockFamily
        period hPeriod 0 sector circleMode))
    (p := fun state _ =>
      (state : GeometricL2 period hPeriod) ∈ range)
    ?_ ?_ ?_ ?_ hState
  · rintro _ ⟨multiplicity, rfl⟩
    simpa [range, primitiveSpinCGeometricSignedModeVector,
      primitiveSpinCGeometricSignedModeSmoothVector] using
      primitiveSpinCGeometricSignedModeVector_mem_synthesisRange
        period hPeriod
        (sector, Sum.inl (multiplicity, circleMode))
  · exact range.zero_mem
  · intro first second _ _ hFirst hSecond
    change
      ((first + second : SmoothSection period hPeriod) :
        GeometricL2 period hPeriod) ∈ range
    rw [UniformSpace.Completion.coe_add]
    exact range.add_mem hFirst hSecond
  · intro scalar state _ hState
    change
      ((scalar • state : SmoothSection period hPeriod) :
        GeometricL2 period hPeriod) ∈ range
    rw [UniformSpace.Completion.coe_smul]
    exact range.smul_mem scalar hState

private theorem signedBranchBlock_mem_signedModeSynthesisRange
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (state : SmoothSection period hPeriod)
    (hState :
      state ∈
        primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode) :
    (state : GeometricL2 period hPeriod) ∈
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  let range :=
    LinearMap.range
      (primitiveSpinCGeometricSignedModeSynthesis
        period hPeriod).toLinearMap
  rw [
    ← primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_span
      period hPeriod positiveLevel branch sector circleMode] at hState
  refine Submodule.span_induction
    (R := Complex) (M := SmoothSection period hPeriod)
    (s := Set.range
      (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
        period hPeriod positiveLevel branch sector circleMode))
    (p := fun state _ =>
      (state : GeometricL2 period hPeriod) ∈ range)
    ?_ ?_ ?_ ?_ hState
  · rintro _ ⟨index, rfl⟩
    let multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) :=
      Fin.cast
        (primitiveSpinCGeometricL2SignedBranchBlock_finrank
          period hPeriod positiveLevel branch sector circleMode)
        index
    have hIndex :
        signedBranchBasisIndex period hPeriod positiveLevel branch
            sector circleMode multiplicity =
          index := by
      apply Fin.ext
      rfl
    simpa [range, primitiveSpinCGeometricSignedModeVector,
      primitiveSpinCGeometricSignedModeSmoothVector, hIndex] using
      primitiveSpinCGeometricSignedModeVector_mem_synthesisRange
        period hPeriod
        (sector, Sum.inr
          { branch := branch
            level := positiveLevel
            multiplicity := multiplicity
            circleMode := circleMode })
  · exact range.zero_mem
  · intro first second _ _ hFirst hSecond
    change
      ((first + second : SmoothSection period hPeriod) :
        GeometricL2 period hPeriod) ∈ range
    rw [UniformSpace.Completion.coe_add]
    exact range.add_mem hFirst hSecond
  · intro scalar state _ hState
    change
      ((scalar • state : SmoothSection period hPeriod) :
        GeometricL2 period hPeriod) ∈ range
    rw [UniformSpace.Completion.coe_smul]
    exact range.smul_mem scalar hState

private theorem signedBlock_mem_signedModeSynthesisRange
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) (state : SmoothSection period hPeriod)
    (hState :
      state ∈
        primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveLevel sector circleMode) :
    (state : GeometricL2 period hPeriod) ∈
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  rw [primitiveSpinCGeometricL2SignedBlock] at hState
  obtain ⟨positive, hPositive, negative, hNegative, hDecompose⟩ :=
    Submodule.mem_sup.mp hState
  rw [← hDecompose]
  change
    ((positive + negative : SmoothSection period hPeriod) :
        GeometricL2 period hPeriod) ∈
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap
  rw [UniformSpace.Completion.coe_add]
  exact
    (LinearMap.range
      (primitiveSpinCGeometricSignedModeSynthesis
        period hPeriod).toLinearMap).add_mem
      (signedBranchBlock_mem_signedModeSynthesisRange
        period hPeriod positiveLevel .positive sector circleMode
          positive hPositive)
      (signedBranchBlock_mem_signedModeSynthesisRange
        period hPeriod positiveLevel .negative sector circleMode
          negative hNegative)

/-- Every finite block used by the Fourier--monopole exhaustion lies in the
range of the individual signed-label synthesis. -/
private theorem signedGlobalBlockRange_le_signedModeSynthesisRange
    (block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex) :
    LinearMap.range
        (primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
          period hPeriod block).toLinearMap ≤
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  intro state hState
  obtain ⟨coefficients, rfl⟩ := hState
  cases block with
  | zero sector circleMode =>
      change
        EuclideanSpace Complex
          (Fin (primitiveSphereModeDegeneracy 0)) at coefficients
      change
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod 0 sector circleMode coefficients :
            GeometricL2 period hPeriod) ∈
          LinearMap.range
            (primitiveSpinCGeometricSignedModeSynthesis
              period hPeriod).toLinearMap
      apply zeroBlock_mem_signedModeSynthesisRange
        period hPeriod sector circleMode
      change
        (∑ index,
          coefficients index •
            primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod 0 sector circleMode index) ∈ _
      apply Submodule.sum_mem
      intro index _
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self index))
  | positive positiveBlock =>
      change
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode coefficients :
              GeometricL2 period hPeriod) ∈
          LinearMap.range
            (primitiveSpinCGeometricSignedModeSynthesis
              period hPeriod).toLinearMap
      apply signedBlock_mem_signedModeSynthesisRange
        period hPeriod positiveBlock.positiveLevel positiveBlock.sector
          positiveBlock.circleMode
      change
        (∑ index,
          coefficients index •
            primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
              period hPeriod positiveBlock.positiveLevel
                positiveBlock.sector positiveBlock.circleMode index) ∈ _
      apply Submodule.sum_mem
      intro index _
      exact Submodule.smul_mem _ _
        (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode index).property

theorem primitiveSpinCGeometricSignedModeSynthesis_range_closed :
    IsClosed
      (LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap :
        Set (GeometricL2 period hPeriod)) :=
  (primitiveSpinCGeometricSignedModeSynthesis period hPeriod).isometry
    |>.isUniformInducing.isComplete_range.isClosed

theorem primitiveSpinCGeometricL2SignedGlobalRange_le_signedModeRange :
    LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap ≤
      LinearMap.range
        (primitiveSpinCGeometricSignedModeSynthesis
          period hPeriod).toLinearMap := by
  rw [primitiveSpinCGeometricL2SignedGlobalJointSynthesis_range]
  apply Submodule.topologicalClosure_minimal
  · apply iSup_le
    intro block
    exact signedGlobalBlockRange_le_signedModeSynthesisRange
      period hPeriod block
  · exact primitiveSpinCGeometricSignedModeSynthesis_range_closed
      period hPeriod

/-- Fourier--monopole completeness is therefore also completeness in the
exact individual label space of the signed Hessian. -/
theorem primitiveSpinCGeometricSignedModeSynthesis_surjective :
    Function.Surjective
      (primitiveSpinCGeometricSignedModeSynthesis period hPeriod) := by
  intro state
  obtain ⟨coefficients, hCoefficients⟩ :=
    (primitiveSpinCGeometricL2SignedGlobalJointSynthesis_denseRange_iff_surjective
      period hPeriod).mp
      (primitiveSpinCGeometricL2SignedGlobalDensity_fourierMonopole
        period hPeriod) state
  have hOldRange :
      state ∈
        LinearMap.range
          (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
            period hPeriod).toLinearMap := by
    refine ⟨coefficients, ?_⟩
    exact hCoefficients
  exact
    primitiveSpinCGeometricL2SignedGlobalRange_le_signedModeRange
      period hPeriod hOldRange

/-- Unconditional geometric unitary in the exact signed coefficient labels
used by `primitiveSpinCGeometricSignedKineticHessianWeight`. -/
def primitiveSpinCGeometricSignedModeUnitary :
    ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode ≃ₗᵢ[Complex]
      GeometricL2 period hPeriod :=
  LinearIsometryEquiv.ofSurjective
    (primitiveSpinCGeometricSignedModeSynthesis period hPeriod)
    (primitiveSpinCGeometricSignedModeSynthesis_surjective
      period hPeriod)

/-! ## Orientation-corrected Dirac labels -/

/-- PT relabeling needed only on the undoubled zero tower.  It is the
identity for negative period and on every positive sphere level. -/
def primitiveSpinCGeometricSignedDiracModeRelabel :
    PrimitiveSpinCGeometricSignedMode →
      PrimitiveSpinCGeometricSignedMode
  | (sector, .inl (multiplicity, circleMode)) =>
      if 0 < period then
        (oppositeRoot sector, .inl (multiplicity, -circleMode))
      else
        (sector, .inl (multiplicity, circleMode))
  | (sector, .inr mode) => (sector, .inr mode)

private theorem primitiveSpinCGeometricSignedDiracModeRelabel_involutive :
    Function.Involutive
      (primitiveSpinCGeometricSignedDiracModeRelabel period) := by
  rintro ⟨sector, mode⟩
  cases mode with
  | inl zeroMode =>
      rcases zeroMode with ⟨multiplicity, circleMode⟩
      by_cases hPositive : 0 < period
      · simp [primitiveSpinCGeometricSignedDiracModeRelabel, hPositive,
          opposite_root_involutive]
      · simp [primitiveSpinCGeometricSignedDiracModeRelabel, hPositive]
  | inr mode =>
      rfl

/-- The zero-mode PT relabeling as an actual equivalence of the exact
signed Hessian labels. -/
def primitiveSpinCGeometricSignedDiracModeEquiv :
    PrimitiveSpinCGeometricSignedMode ≃
      PrimitiveSpinCGeometricSignedMode where
  toFun := primitiveSpinCGeometricSignedDiracModeRelabel period
  invFun := primitiveSpinCGeometricSignedDiracModeRelabel period
  left_inv :=
    primitiveSpinCGeometricSignedDiracModeRelabel_involutive period
  right_inv :=
    primitiveSpinCGeometricSignedDiracModeRelabel_involutive period

@[simp]
theorem primitiveSpinCGeometricSignedDiracModeEquiv_positive
    (sector : NormalRootChoice)
    (mode : PrimitiveSpinCSignedNonzeroMode) :
    primitiveSpinCGeometricSignedDiracModeEquiv period
        (sector, .inr mode) =
      (sector, .inr mode) :=
  rfl

/-- Smooth representative whose first-order eigenvalue has the orientation
of the exact signed coefficient label. -/
def primitiveSpinCGeometricSignedDiracModeSmoothVector
    (mode : PrimitiveSpinCGeometricSignedMode) :
    SmoothSection period hPeriod :=
  primitiveSpinCGeometricSignedModeSmoothVector period hPeriod
    (primitiveSpinCGeometricSignedDiracModeEquiv period mode)

/-- The orientation-corrected representative in geometric `L²`. -/
def primitiveSpinCGeometricSignedDiracModeVector
    (mode : PrimitiveSpinCGeometricSignedMode) :
    GeometricL2 period hPeriod :=
  primitiveSpinCGeometricSignedModeVector period hPeriod
    (primitiveSpinCGeometricSignedDiracModeEquiv period mode)

theorem primitiveSpinCGeometricSignedDiracModeVector_orthonormal :
    Orthonormal Complex
      (primitiveSpinCGeometricSignedDiracModeVector period hPeriod) := by
  change
    Orthonormal Complex
      (fun mode =>
        primitiveSpinCGeometricSignedModeVector period hPeriod
          (primitiveSpinCGeometricSignedDiracModeEquiv period mode))
  exact
    (primitiveSpinCGeometricSignedModeVector_orthonormal period hPeriod).comp
      (primitiveSpinCGeometricSignedDiracModeEquiv period)
      (primitiveSpinCGeometricSignedDiracModeEquiv period).injective

/-- The complete Fourier--monopole unitary after the exact zero-mode
orientation correction. -/
def primitiveSpinCGeometricSignedDiracModeUnitary :
    ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode ≃ₗᵢ[Complex]
      GeometricL2 period hPeriod :=
  (complexDiagonalHilbertCongr PrimitiveSpinCGeometricSignedMode
      (primitiveSpinCGeometricSignedDiracModeEquiv period)).trans
    (primitiveSpinCGeometricSignedModeUnitary period hPeriod)

@[simp]
theorem primitiveSpinCGeometricSignedModeUnitary_single
    (mode : PrimitiveSpinCGeometricSignedMode) (coefficient : Complex) :
    primitiveSpinCGeometricSignedModeUnitary period hPeriod
        (lp.single 2 mode coefficient) =
      coefficient •
        primitiveSpinCGeometricSignedModeVector period hPeriod mode := by
  change
    primitiveSpinCGeometricSignedModeSynthesis period hPeriod
        (lp.single 2 mode coefficient) =
      coefficient •
        primitiveSpinCGeometricSignedModeVector period hPeriod mode
  exact primitiveSpinCGeometricSignedModeSynthesis_single
    period hPeriod mode coefficient

@[simp]
theorem primitiveSpinCGeometricSignedDiracModeUnitary_single
    (mode : PrimitiveSpinCGeometricSignedMode) (coefficient : Complex) :
    primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
        (lp.single 2 mode coefficient) =
      coefficient •
        primitiveSpinCGeometricSignedDiracModeVector period hPeriod mode := by
  rw [primitiveSpinCGeometricSignedDiracModeUnitary,
    LinearIsometryEquiv.trans_apply,
    complexDiagonalHilbertCongr_single,
    primitiveSpinCGeometricSignedModeUnitary_single]
  rfl

private theorem
    primitiveSpinCGeometricL2OrthonormalZeroBlockFamily_dirac
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy 0)) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod 0 sector circleMode multiplicity) =
      ((-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode : Real) : Complex) •
        primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod 0 sector circleMode multiplicity := by
  rw [← Module.End.mem_eigenspace_iff]
  have hSpan :
      Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod 0 sector circleMode)) ≤
        Module.End.eigenspace
          (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod)
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode : Real) : Complex) := by
    rw [Submodule.span_le]
    rintro _ ⟨rawMultiplicity, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 sector circleMode rawMultiplicity) =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode : Real) : Complex)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 sector circleMode rawMultiplicity)
    rw [d9PrimitiveSpinCComplexScalarSection_ofReal]
    fin_cases rawMultiplicity
    simpa [primitiveSpinCGeometricL2RawBlockFamily,
      primitiveSpinCAllModeNullHarmonicRealSection] using
      primitiveSpinCHopfZeroModeGeometricDiracOperator_eigen
        period hPeriod sector circleMode
  apply hSpan
  rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
    period hPeriod 0 sector circleMode]
  exact Submodule.subset_span (Set.mem_range_self multiplicity)

/-- Every exact signed coefficient label is represented by a smooth
eigenvector of the genuine first-order geometric Dirac operator. -/
theorem primitiveSpinCGeometricSignedDiracModeSmoothVector_dirac
    (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricSignedDiracModeSmoothVector
          period hPeriod mode) =
      (primitiveSpinCGeometricSignedEigenvalue
          period hPeriod mode : Complex) •
        primitiveSpinCGeometricSignedDiracModeSmoothVector
          period hPeriod mode := by
  rcases mode with ⟨sector, mode⟩
  cases mode with
  | inl zeroMode =>
      rcases zeroMode with ⟨multiplicity, circleMode⟩
      rw [← primitiveSpinCGeometricSignedZeroActualEigenvalue_eq
        period hPeriod (sector, (multiplicity, circleMode))]
      by_cases hPositive : 0 < period
      · simpa [primitiveSpinCGeometricSignedDiracModeSmoothVector,
          primitiveSpinCGeometricSignedDiracModeEquiv,
          primitiveSpinCGeometricSignedDiracModeRelabel,
          primitiveSpinCGeometricSignedModeSmoothVector,
          primitiveSpinCGeometricSignedZeroSource, hPositive] using
          primitiveSpinCGeometricL2OrthonormalZeroBlockFamily_dirac
            period hPeriod (oppositeRoot sector) (-circleMode)
              multiplicity
      · simpa [primitiveSpinCGeometricSignedDiracModeSmoothVector,
          primitiveSpinCGeometricSignedDiracModeEquiv,
          primitiveSpinCGeometricSignedDiracModeRelabel,
          primitiveSpinCGeometricSignedModeSmoothVector,
          primitiveSpinCGeometricSignedZeroSource, hPositive] using
          primitiveSpinCGeometricL2OrthonormalZeroBlockFamily_dirac
            period hPeriod sector circleMode multiplicity
  | inr positiveMode =>
      rcases positiveMode with
        ⟨branch, positiveLevel, multiplicity, circleMode⟩
      have hEigenvalue :
          primitiveSpinCGeometricL2SignedBranchEigenvalue
              period positiveLevel branch sector circleMode =
            (primitiveSpinCGeometricSignedEigenvalue period hPeriod
              (sector, .inr
                { branch := branch
                  level := positiveLevel
                  multiplicity := multiplicity
                  circleMode := circleMode }) : Complex) := by
        change
          ((primitiveSpinCDiracBranchSign branch *
              primitiveSpinCHarmonicDiracFrequency
                period positiveLevel sector circleMode : Real) : Complex) =
            ((primitiveSpinCGeometricSignedNonzeroEigenvalue
              period hPeriod
              (sector,
                { branch := branch
                  level := positiveLevel
                  multiplicity := multiplicity
                  circleMode := circleMode }) : Real) : Complex)
        rw [primitiveSpinCGeometricSignedNonzeroEigenvalue,
          primitiveSpinCAllLevelSignedGeometricFrequency_eq]
      change
        primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
            (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode
              (signedBranchBasisIndex period hPeriod positiveLevel branch
                sector circleMode multiplicity)) =
          (primitiveSpinCGeometricSignedEigenvalue period hPeriod
            (sector, .inr
              { branch := branch
                level := positiveLevel
                multiplicity := multiplicity
                circleMode := circleMode }) : Complex) •
            primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode
              (signedBranchBasisIndex period hPeriod positiveLevel branch
                sector circleMode multiplicity)
      rw [← hEigenvalue]
      exact
        primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_dirac
          period hPeriod positiveLevel branch sector circleMode
          (signedBranchBasisIndex period hPeriod positiveLevel branch
            sector circleMode multiplicity)

/-! ## Exact SpinC action Hessian on the smooth spectral core -/

/-- The genuine smooth differential expression `2D + m²` dictated by the
real kinetic action and a scalar mass-squared term. -/
def primitiveSpinCGeometricSignedActionHessianSmoothCore
    (massSquared : Real) :
    SmoothSection period hPeriod →ₗ[Complex]
      SmoothSection period hPeriod :=
  (2 : Complex) •
      primitiveSpinCGeometricDiracComplexLinearMap period hPeriod +
    (massSquared : Complex) • LinearMap.id

/-- The genuine smooth action Hessian has the exact diagonal coefficient
used by the maximal signed Hessian model. -/
theorem primitiveSpinCGeometricSignedActionHessianSmoothCore_mode
    (massSquared : Real) (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCGeometricSignedActionHessianSmoothCore
        period hPeriod massSquared
        (primitiveSpinCGeometricSignedDiracModeSmoothVector
          period hPeriod mode) =
      ((primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared : Real) : Complex) •
        primitiveSpinCGeometricSignedDiracModeSmoothVector
          period hPeriod mode := by
  rw [primitiveSpinCGeometricSignedActionHessianSmoothCore,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply,
    primitiveSpinCGeometricSignedDiracModeSmoothVector_dirac]
  simp only [primitiveSpinCGeometricSignedKineticHessianWeight,
    smul_smul, Complex.ofReal_ofNat, Complex.ofReal_add,
    Complex.ofReal_mul]
  module

/-- Finite signed coefficients form the canonical smooth core of the
Fourier--monopole unitary. -/
abbrev PrimitiveSpinCGeometricSignedFiniteCoefficients :=
  PrimitiveSpinCGeometricSignedMode →₀ Complex

/-- Finite synthesis into genuine smooth eigensections. -/
def primitiveSpinCGeometricSignedDiracFiniteSynthesis :
    PrimitiveSpinCGeometricSignedFiniteCoefficients →ₗ[Complex]
      SmoothSection period hPeriod :=
  Finsupp.linearCombination Complex
    (primitiveSpinCGeometricSignedDiracModeSmoothVector
      period hPeriod)

@[simp]
theorem primitiveSpinCGeometricSignedDiracFiniteSynthesis_single
    (mode : PrimitiveSpinCGeometricSignedMode) (coefficient : Complex) :
    primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod (Finsupp.single mode coefficient) =
      coefficient •
        primitiveSpinCGeometricSignedDiracModeSmoothVector
          period hPeriod mode := by
  simp [primitiveSpinCGeometricSignedDiracFiniteSynthesis]

/-- Finite diagonal coefficient realization of `2D + m²`. -/
def primitiveSpinCGeometricSignedFiniteActionHessian
    (massSquared : Real) :
    PrimitiveSpinCGeometricSignedFiniteCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricSignedFiniteCoefficients :=
  Finsupp.lsum Complex fun mode =>
    (Finsupp.lsingle mode).comp
      (((primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared : Real) : Complex) •
        (LinearMap.id : Complex →ₗ[Complex] Complex))

@[simp]
theorem primitiveSpinCGeometricSignedFiniteActionHessian_single
    (massSquared : Real) (mode : PrimitiveSpinCGeometricSignedMode)
    (coefficient : Complex) :
    primitiveSpinCGeometricSignedFiniteActionHessian
        period hPeriod massSquared
        (Finsupp.single mode coefficient) =
      ((primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared : Real) : Complex) •
        Finsupp.single mode coefficient := by
  simp [primitiveSpinCGeometricSignedFiniteActionHessian]

/-- Exact operator intertwining on the whole finite Fourier--monopole
smooth core. -/
theorem primitiveSpinCGeometricSignedDiracFiniteSynthesis_intertwines_hessian
    (massSquared : Real)
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    primitiveSpinCGeometricSignedActionHessianSmoothCore
        period hPeriod massSquared
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients) =
      primitiveSpinCGeometricSignedDiracFiniteSynthesis period hPeriod
        (primitiveSpinCGeometricSignedFiniteActionHessian
          period hPeriod massSquared coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add, map_add, inductionHypothesis,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
        map_smul,
        primitiveSpinCGeometricSignedActionHessianSmoothCore_mode,
        primitiveSpinCGeometricSignedFiniteActionHessian_single,
        map_smul,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
        smul_smul]
      simp only [smul_smul, mul_comm]

/-- Maximal coefficient-space realization of the same action Hessian. -/
abbrev primitiveSpinCGeometricSignedActionHessianOperator
    (massSquared : Real) :=
  complexDiagonalOperator PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared)

/-- Pullback of the maximal coefficient Hessian domain to the independent
geometric completion. -/
def primitiveSpinCGeometricSignedActionHessianGeometricDomain
    (massSquared : Real) :
    Submodule Complex (GeometricL2 period hPeriod) :=
  (primitiveSpinCGeometricSignedActionHessianOperator
      period hPeriod massSquared).domain.comap
    (primitiveSpinCGeometricSignedDiracModeUnitary
      period hPeriod).symm.toLinearMap

/-- The geometric maximal domain is unitarily identical to the coefficient
maximal domain. -/
def primitiveSpinCGeometricSignedActionHessianGeometricDomainEquiv
    (massSquared : Real) :
    primitiveSpinCGeometricSignedActionHessianGeometricDomain
        period hPeriod massSquared ≃ₗᵢ[Complex]
      (primitiveSpinCGeometricSignedActionHessianOperator
        period hPeriod massSquared).domain where
  toFun state :=
    ⟨(primitiveSpinCGeometricSignedDiracModeUnitary
      period hPeriod).symm state.1, state.2⟩
  invFun state :=
    ⟨primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod state.1, by
      change
        (primitiveSpinCGeometricSignedDiracModeUnitary
          period hPeriod).symm
            (primitiveSpinCGeometricSignedDiracModeUnitary
              period hPeriod state.1) ∈
          (primitiveSpinCGeometricSignedActionHessianOperator
            period hPeriod massSquared).domain
      simpa using state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod).apply_symm_apply state.1
  right_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod).symm_apply_apply state.1
  map_add' first second := by
    apply Subtype.ext
    exact map_add
      (primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod).symm first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    exact map_smul
      (primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod).symm scalar state.1
  norm_map' state :=
    (primitiveSpinCGeometricSignedDiracModeUnitary
      period hPeriod).symm.norm_map state.1

/-- Maximal action Hessian transported to the independent geometric
completion. -/
def primitiveSpinCGeometricSignedActionHessianGeometricToFun
    (massSquared : Real) :
    primitiveSpinCGeometricSignedActionHessianGeometricDomain
        period hPeriod massSquared →ₗ[Complex]
      GeometricL2 period hPeriod :=
  (primitiveSpinCGeometricSignedDiracModeUnitary
      period hPeriod).toLinearMap.comp
    ((primitiveSpinCGeometricSignedActionHessianOperator
      period hPeriod massSquared).toFun.comp
      (primitiveSpinCGeometricSignedActionHessianGeometricDomainEquiv
        period hPeriod massSquared).toLinearMap)

/-- Genuine maximal-domain unbounded Hessian on geometric `L²`. -/
def primitiveSpinCGeometricSignedActionHessianGeometricOperator
    (massSquared : Real) :
    GeometricL2 period hPeriod →ₗ.[Complex]
      GeometricL2 period hPeriod where
  domain :=
    primitiveSpinCGeometricSignedActionHessianGeometricDomain
      period hPeriod massSquared
  toFun :=
    primitiveSpinCGeometricSignedActionHessianGeometricToFun
      period hPeriod massSquared

/-- Exact unitary conjugacy of the geometric and coefficient maximal
Hessians. -/
theorem primitiveSpinCGeometricSignedActionHessianGeometricOperator_conjugacy
    (massSquared : Real)
    (state :
      primitiveSpinCGeometricSignedActionHessianGeometricDomain
        period hPeriod massSquared) :
    (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
        (primitiveSpinCGeometricSignedActionHessianGeometricOperator
          period hPeriod massSquared state) =
      primitiveSpinCGeometricSignedActionHessianOperator
        period hPeriod massSquared
        (primitiveSpinCGeometricSignedActionHessianGeometricDomainEquiv
          period hPeriod massSquared state) := by
  exact
    (primitiveSpinCGeometricSignedDiracModeUnitary
      period hPeriod).symm_apply_apply _

theorem primitiveSpinCGeometricSignedActionHessianOperator_selfAdjoint
    (massSquared : Real) :
    IsSelfAdjoint
      (primitiveSpinCGeometricSignedActionHessianOperator
        period hPeriod massSquared) :=
  complexDiagonalOperator_isSelfAdjoint
    PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared)

theorem primitiveSpinCGeometricSignedActionHessianOperator_fredholm
    (massSquared : Real) :
    IsClosed
        (LinearMap.range
          (primitiveSpinCGeometricSignedActionHessianOperator
            period hPeriod massSquared).toFun :
          Set (ComplexDiagonalHilbert
            PrimitiveSpinCGeometricSignedMode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (primitiveSpinCGeometricSignedActionHessianOperator
            period hPeriod massSquared).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalOperatorCokernel
          PrimitiveSpinCGeometricSignedMode
          (fun mode =>
            primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared)) :=
  complexDiagonalOperator_fredholm_of_proper_shift
    PrimitiveSpinCGeometricSignedMode
    (primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod)
    (primitiveSpinCGeometricSignedKineticHessianWeight_proper
      period hPeriod)
    massSquared

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
end JanusFormal
