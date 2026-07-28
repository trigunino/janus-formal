import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D

/-!
# Radial orthogonality in the primitive SpinC geometric L² core

The doubled Clifford generators are skew-Hermitian for the descended fiber
pairing.  Consequently the radial `+i` and `-i` eigenspaces are pointwise,
and hence geometrically, orthogonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D

set_option autoImplicit false
noncomputable section

open InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- Every doubled Clifford generator is skew-Hermitian for the canonical
fiber pairing. -/
theorem d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew
    (direction : Fin 3) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction left) right =
      -d9DoubledMatterSpinorHermitianPairing left
        (d9DoubledMatterFiberCliffordGamma direction right) := by
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  change
    ambientHalfSpinorHermitianPairing
          (d9DoubledMatterFiberHalfSpinorLinearEquiv
            (d9DoubledMatterFiberCliffordGamma direction left)).1
          (d9DoubledMatterFiberHalfSpinorLinearEquiv right).1 +
        ambientHalfSpinorHermitianPairing
          (d9DoubledMatterFiberHalfSpinorLinearEquiv
            (d9DoubledMatterFiberCliffordGamma direction left)).2
          (d9DoubledMatterFiberHalfSpinorLinearEquiv right).2 =
      -(ambientHalfSpinorHermitianPairing
            (d9DoubledMatterFiberHalfSpinorLinearEquiv left).1
            (d9DoubledMatterFiberHalfSpinorLinearEquiv
              (d9DoubledMatterFiberCliffordGamma direction right)).1 +
          ambientHalfSpinorHermitianPairing
            (d9DoubledMatterFiberHalfSpinorLinearEquiv left).2
            (d9DoubledMatterFiberHalfSpinorLinearEquiv
              (d9DoubledMatterFiberCliffordGamma direction right)).2)
  rw [show
      d9DoubledMatterFiberHalfSpinorLinearEquiv
          (d9DoubledMatterFiberCliffordGamma direction left) =
        d9DoubledMatterSpinorCliffordGamma direction
          (d9DoubledMatterFiberHalfSpinorLinearEquiv left) by
      exact d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma direction left,
    show
      d9DoubledMatterFiberHalfSpinorLinearEquiv
          (d9DoubledMatterFiberCliffordGamma direction right) =
        d9DoubledMatterSpinorCliffordGamma direction
          (d9DoubledMatterFiberHalfSpinorLinearEquiv right) by
      exact d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma direction right]
  fin_cases direction <;>
    simp [ambientHalfSpinorHermitianPairing,
      ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
      Fin.sum_univ_succ] <;>
    ring

theorem d9DoubledMatterSpinorHermitianPairing_real_smul_left
    (scalar : Real) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (scalar • left) right =
      (scalar : Complex) *
        d9DoubledMatterSpinorHermitianPairing left right := by
  have hAction :
      d9PrimitiveSpinCComplexActionCLM (scalar : Complex) left =
        scalar • left := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  rw [← hAction,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left]
  simp

theorem d9DoubledMatterSpinorHermitianPairing_real_smul_right
    (scalar : Real) (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        left (scalar • right) =
      (scalar : Complex) *
        d9DoubledMatterSpinorHermitianPairing left right := by
  have hAction :
      d9PrimitiveSpinCComplexActionCLM (scalar : Complex) right =
        scalar • right := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  rw [← hAction,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right]

theorem d9DoubledMatterSpinorHermitianPairing_neg_left
    (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing (-left) right =
      -d9DoubledMatterSpinorHermitianPairing left right := by
  have hAdd :=
    d9DoubledMatterSpinorHermitianPairing_add_left
      left (-left) right
  simp only [add_neg_cancel] at hAdd
  have hZero :
      d9DoubledMatterSpinorHermitianPairing
          (0 : D9DoubledMatterFiber) right = 0 := by
    unfold d9DoubledMatterSpinorHermitianPairing
      d9MatterSpinorHermitianPairing
    simp [ambientHalfSpinorHermitianPairing,
      ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed]
  rw [hZero] at hAdd
  exact eq_neg_of_add_eq_zero_right hAdd.symm

theorem d9DoubledMatterSpinorHermitianPairing_neg_right
    (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing left (-right) =
      -d9DoubledMatterSpinorHermitianPairing left right := by
  have hAdd :=
    d9DoubledMatterSpinorHermitianPairing_add_right
      left right (-right)
  simp only [add_neg_cancel] at hAdd
  have hZero :
      d9DoubledMatterSpinorHermitianPairing
          left (0 : D9DoubledMatterFiber) = 0 := by
    unfold d9DoubledMatterSpinorHermitianPairing
      d9MatterSpinorHermitianPairing
    simp [ambientHalfSpinorHermitianPairing,
      ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed]
  rw [hZero] at hAdd
  exact eq_neg_of_add_eq_zero_right hAdd.symm

/-- Clifford multiplication by the quotient radial unit vector is
skew-Hermitian. -/
theorem d9DoubledMatterSpinorHermitianPairing_baseUnitRadial_skew
    (base : ThroatBase period hPeriod)
    (left right : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base left) right =
      -d9DoubledMatterSpinorHermitianPairing left
        (d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base right) := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  simp [Fin.sum_univ_succ,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right]
  rw [d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew,
    d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew,
    d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew]
  ring

/-- Opposite radial Clifford eigenspaces are orthogonal in one fiber. -/
theorem d9DoubledMatterSpinorHermitianPairing_radial_eigen_anti_eigen
    (base : ThroatBase period hPeriod)
    (left right : D9DoubledMatterFiber)
    (hLeft :
      d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base left =
        d9PrimitiveSpinCImaginaryAction left)
    (hRight :
      d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base right =
        -d9PrimitiveSpinCImaginaryAction right) :
    d9DoubledMatterSpinorHermitianPairing left right = 0 := by
  have hSkew :=
    d9DoubledMatterSpinorHermitianPairing_baseUnitRadial_skew
      period hPeriod base left right
  rw [hLeft, hRight] at hSkew
  have hImaginaryLeft :
      d9PrimitiveSpinCImaginaryAction left =
        d9PrimitiveSpinCComplexActionCLM Complex.I left := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  have hNegativeImaginaryRight :
      -d9PrimitiveSpinCImaginaryAction right =
        d9PrimitiveSpinCComplexActionCLM (-Complex.I) right := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  rw [hImaginaryLeft, hNegativeImaginaryRight,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right] at hSkew
  let pairing := d9DoubledMatterSpinorHermitianPairing left right
  have hOpposite : -(Complex.I * pairing) = Complex.I * pairing := by
    simpa [pairing, Complex.star_def] using hSkew
  have hDouble : (2 : Complex) * (Complex.I * pairing) = 0 := by
    calc
      (2 : Complex) * (Complex.I * pairing) =
          Complex.I * pairing - (-(Complex.I * pairing)) := by ring
      _ = 0 := by rw [hOpposite]; ring
  have hImaginaryZero : Complex.I * pairing = 0 :=
    (mul_eq_zero.mp hDouble).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hImaginaryZero).resolve_left Complex.I_ne_zero

/-- The positive/negative radial smooth submodules are pointwise
orthogonal. -/
theorem primitiveSpinCGeometricL2RadialSubmodules_pointwise_orthogonal
    {left right : SmoothSection period hPeriod}
    (hLeft :
      left ∈
        primitiveSpinCGeometricL2PositiveRadialSubmodule
          period hPeriod)
    (hRight :
      right ∈
        primitiveSpinCGeometricL2NegativeRadialSubmodule
          period hPeriod)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter left right base = 0 := by
  exact
    d9DoubledMatterSpinorHermitianPairing_radial_eigen_anti_eigen
      period hPeriod base (left base) (right base)
      (hLeft base) (hRight base)

/-- The positive/negative radial smooth submodules are orthogonal for the
independently integrated geometric product. -/
theorem primitiveSpinCGeometricL2RadialSubmodules_isOrtho :
    primitiveSpinCGeometricL2PositiveRadialSubmodule period hPeriod ⟂
      primitiveSpinCGeometricL2NegativeRadialSubmodule
        period hPeriod := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro left hLeft right hRight
  change
    d9PrimitiveSpinCGeometricL2Pairing
      period hPeriod .positiveQuarter left right = 0
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [show
      d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter left right =
        0 by
      funext base
      exact
        primitiveSpinCGeometricL2RadialSubmodules_pointwise_orthogonal
          period hPeriod hLeft hRight base]
  simp

/-- Scalar and Clifford-gradient components of arbitrary positive-level
packets are geometrically orthogonal, independently of all spectral
labels. -/
theorem primitiveSpinCAllLevelNullHarmonicScalarGradient_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity firstSector firstCircleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity secondSector
              secondCircleMode
          |>.gradientSection) =
      0 := by
  change
    inner Complex
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity firstSector firstCircleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity secondSector
              secondCircleMode
          |>.gradientSection) =
      0
  exact
    Submodule.isOrtho_iff_inner_eq.mp
      (primitiveSpinCGeometricL2RadialSubmodules_isOrtho
        period hPeriod)
      _
      (primitiveSpinCAllLevelNullHarmonicScalar_mem_positiveRadial
        period hPeriod firstPositiveLevel firstMultiplicity
        firstSector firstCircleMode)
      _
      (primitiveSpinCAllLevelNullHarmonicGradient_mem_negativeRadial
        period hPeriod secondPositiveLevel secondMultiplicity
        secondSector secondCircleMode)

/-- Every signed-packet pairing splits into a scalar term and a gradient
term; both mixed radial terms vanish unconditionally. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_pairing_eq_diagonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstBranch secondBranch : PrimitiveSpinCDiracBranch)
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod firstPositiveLevel firstBranch firstSector
            firstCircleMode firstMultiplicity)
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod secondPositiveLevel secondBranch secondSector
            secondCircleMode secondMultiplicity) =
      star
          (primitiveSpinCGeometricL2SignedBranchScalarCoefficient
            period firstPositiveLevel firstBranch firstSector
              firstCircleMode) *
        primitiveSpinCGeometricL2SignedBranchScalarCoefficient
            period secondPositiveLevel secondBranch secondSector
              secondCircleMode *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity firstSector firstCircleMode
            |>.scalarSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity secondSector
                secondCircleMode
            |>.scalarSection) +
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity firstSector firstCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity secondSector
              secondCircleMode
          |>.gradientSection) := by
  let firstScalar :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        firstPositiveLevel firstMultiplicity firstSector firstCircleMode
      |>.scalarSection)
  let firstGradient :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        firstPositiveLevel firstMultiplicity firstSector firstCircleMode
      |>.gradientSection)
  let secondScalar :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        secondPositiveLevel secondMultiplicity secondSector secondCircleMode
      |>.scalarSection)
  let secondGradient :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        secondPositiveLevel secondMultiplicity secondSector secondCircleMode
      |>.gradientSection)
  have hScalarGradient : inner Complex firstScalar secondGradient = 0 := by
    change
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter firstScalar secondGradient = 0
    dsimp only [firstScalar, secondGradient]
    exact
      primitiveSpinCAllLevelNullHarmonicScalarGradient_orthogonal
        period hPeriod firstPositiveLevel secondPositiveLevel
        firstMultiplicity secondMultiplicity firstSector secondSector
        firstCircleMode secondCircleMode
  have hGradientScalar : inner Complex firstGradient secondScalar = 0 := by
    rw [inner_eq_zero_symm]
    change
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter secondScalar firstGradient = 0
    dsimp only [secondScalar, firstGradient]
    exact
      primitiveSpinCAllLevelNullHarmonicScalarGradient_orthogonal
        period hPeriod secondPositiveLevel firstPositiveLevel
        secondMultiplicity firstMultiplicity secondSector firstSector
        secondCircleMode firstCircleMode
  rw [
    primitiveSpinCGeometricL2SignedBranchRawFamily_eq_radial_components,
    primitiveSpinCGeometricL2SignedBranchRawFamily_eq_radial_components]
  change
    inner Complex
        (_ • firstScalar + firstGradient)
        (_ • secondScalar + secondGradient) =
      _ * _ *
          inner Complex firstScalar secondScalar +
        inner Complex firstGradient secondGradient
  simp_rw [inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right,
    hScalarGradient, hGradientScalar, starRingEnd_apply]
  ring

/-- Assumption-free certificate for radial Hermitian orthogonality. -/
structure ProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonalityCertificate4D
    where
  cliffordSkew :
    ∀ direction left right,
      d9DoubledMatterSpinorHermitianPairing
          (d9DoubledMatterFiberCliffordGamma direction left) right =
        -d9DoubledMatterSpinorHermitianPairing left
          (d9DoubledMatterFiberCliffordGamma direction right)
  radialSubmodulesOrtho :
    primitiveSpinCGeometricL2PositiveRadialSubmodule period hPeriod ⟂
      primitiveSpinCGeometricL2NegativeRadialSubmodule period hPeriod
  scalarGradientOrtho :
    ∀ firstPositiveLevel secondPositiveLevel
      firstMultiplicity secondMultiplicity
      firstSector secondSector firstCircleMode secondCircleMode,
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity firstSector firstCircleMode
            |>.scalarSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity secondSector
                secondCircleMode
            |>.gradientSection) =
        0

def programPD9PrimitiveSpinCGeometricL2RadialOrthogonalityCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonalityCertificate4D
      period hPeriod where
  cliffordSkew :=
    d9DoubledMatterSpinorHermitianPairing_cliffordGamma_skew
  radialSubmodulesOrtho :=
    primitiveSpinCGeometricL2RadialSubmodules_isOrtho period hPeriod
  scalarGradientOrtho :=
    primitiveSpinCAllLevelNullHarmonicScalarGradient_orthogonal
      period hPeriod

theorem primitiveSpinCGeometricL2RadialOrthogonality_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonalityCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2RadialOrthogonalityCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
end JanusFormal
