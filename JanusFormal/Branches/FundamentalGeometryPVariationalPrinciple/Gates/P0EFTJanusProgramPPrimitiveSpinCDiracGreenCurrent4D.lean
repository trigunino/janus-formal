import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCCliffordSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCConnectionHermitian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameIPP4D

/-!
# Primitive SpinC Dirac Green current

For two genuine primitive SpinC sections the current

`Jᵢ(ψ, φ) = ⟨γᵢ ψ, φ⟩`

is a globally defined smooth complex scalar on the throat.  This file computes
its intrinsic-frame derivative in one arbitrary local gauge and then assembles
the complete pointwise Green residual of the implemented geometric Dirac
operator.

The flat derivative gives `-∑ eᵢ Jᵢ`; the monopole/normal `U(1)` correction
cancels algebraically; the radial Levi--Civita spin correction contributes
`2 ⟨γ(n)ψ,φ⟩`.  This is exactly the term cancelled after applying the intrinsic
frame IPP.  No boundary condition, coefficient model or D10 direction is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCDiracGreenCurrent4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff BigOperators InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
open P0EFTJanusProgramPPrimitiveSpinCCliffordSection4D
open P0EFTJanusProgramPPrimitiveSpinCConnectionHermitian4D
open P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameIPP4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## The fiber pairing as a continuous real bilinear map -/

private def d9DoubledMatterPairingRightCLM
    (first : D9DoubledMatterFiber) :
    D9DoubledMatterFiber →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun second =>
        d9DoubledMatterSpinorHermitianPairing first second
      map_add' := fun second third =>
        d9DoubledMatterSpinorHermitianPairing_add_right first second third
      map_smul' := fun scalar second => by
        simpa using
          d9DoubledMatterSpinorHermitianPairing_real_smul_right
            scalar first second }

@[simp]
private theorem d9DoubledMatterPairingRightCLM_apply
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterPairingRightCLM first second =
      d9DoubledMatterSpinorHermitianPairing first second :=
  rfl

private def d9DoubledMatterPairingCLM :
    D9DoubledMatterFiber →L[Real]
      D9DoubledMatterFiber →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := d9DoubledMatterPairingRightCLM
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro third
        exact d9DoubledMatterSpinorHermitianPairing_add_left
          first second third
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        exact d9DoubledMatterSpinorHermitianPairing_real_smul_left
          scalar first second }

private def d9DoubledMatterPairingLeftCLM
    (second : D9DoubledMatterFiber) :
    D9DoubledMatterFiber →L[Real] Complex :=
  (ContinuousLinearMap.apply Real Complex second).comp
    d9DoubledMatterPairingCLM

@[simp]
private theorem d9DoubledMatterPairingCLM_apply
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterPairingCLM first second =
      d9DoubledMatterSpinorHermitianPairing first second :=
  rfl

@[simp]
private theorem d9DoubledMatterPairingLeftCLM_apply
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterPairingLeftCLM second first =
      d9DoubledMatterSpinorHermitianPairing first second :=
  rfl

/-- Manifold product rule for the doubled Hermitian pairing. -/
theorem d9DoubledMatterSpinorHermitianPairing_mfderiv
    (first second : ThroatBase period hPeriod → D9DoubledMatterFiber)
    (base : ThroatBase period hPeriod)
    (hFirst : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) first base)
    (hSecond : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) second base)
    (tangent : TangentSpace throatCoverModelWithCorners base) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun current =>
          d9DoubledMatterSpinorHermitianPairing
            (first current) (second current)) base tangent =
      d9DoubledMatterSpinorHermitianPairing (first base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber) second base tangent) +
        d9DoubledMatterSpinorHermitianPairing
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber) first base tangent)
          (second base) := by
  have hFirstPairing : HasMFDerivAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber →L[Real] Complex)
      (fun current => d9DoubledMatterPairingCLM (first current)) base
      (d9DoubledMatterPairingCLM.comp
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) first base)) := by
    convert d9DoubledMatterPairingCLM.hasFDerivAt.hasMFDerivAt.comp
      base hFirst.hasMFDerivAt using 1 <;> rfl
  have hApply :=
    (isBoundedBilinearMap_apply.hasFDerivAt
      (d9DoubledMatterPairingCLM (first base), second base)).hasMFDerivAt.comp
        base (hFirstPairing.prodMk hSecond.hasMFDerivAt)
  have hDerivative := hApply.mfderiv
  have hAt := congrArg (fun derivative => derivative tangent) hDerivative
  change (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
      ((fun p : (D9DoubledMatterFiber →L[Real] Complex) ×
          D9DoubledMatterFiber => p.1 p.2) ∘
        fun y => (d9DoubledMatterPairingCLM (first y), second y)) base)
      tangent = _
  rw [hAt]
  rfl

/-! ## Clifford transforms and the global current -/

/-- Flat local differentiation commutes with a fixed Clifford generator. -/
theorem d9PrimitiveSpinCCliffordLocalGaugeFamily_flatDerivative
    (choice : NormalRootChoice) (direction derivativeDirection : Fin 3)
    (family : SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
        (d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice
          direction family)
        index derivativeDirection base =
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice family
          index derivativeDirection base) := by
  have hFamily : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) (family.localValue index) base :=
    ((family.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hBase))
      |>.mdifferentiableAt (by simp)
  have hGamma : MDifferentiableAt 𝓘(Real, D9DoubledMatterFiber)
      𝓘(Real, D9DoubledMatterFiber)
      (d9DoubledMatterFiberCliffordGammaCLM direction)
      (family.localValue index base) :=
    (d9DoubledMatterFiberCliffordGammaCLM direction)
      |>.differentiableAt.mdifferentiableAt
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    mfderiv throatCoverModelWithCorners 𝓘(Real, D9DoubledMatterFiber)
        ((d9DoubledMatterFiberCliffordGammaCLM direction) ∘
          family.localValue index) base
        (d9IntrinsicThroatFrame period hPeriod derivativeDirection base) = _
  rw [mfderiv_comp base hGamma hFamily]
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

/-- The global smooth Green current in one intrinsic direction. -/
def d9PrimitiveSpinCGreenCurrent
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    SmoothThroatField period hPeriod Complex where
  toFun :=
    d9PrimitiveSpinCPointwiseHermitianPairing period hPeriod choice
      (d9PrimitiveSpinCCliffordSection period hPeriod choice direction first)
      second
  contMDiff_toFun :=
    d9PrimitiveSpinCPointwiseHermitianPairing_contMDiff period hPeriod choice
      (d9PrimitiveSpinCCliffordSection period hPeriod choice direction first)
      second

@[simp]
theorem d9PrimitiveSpinCGreenCurrent_apply
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first second
        base =
      d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction (first base))
        (second base) := by
  change d9PrimitiveSpinCPointwiseHermitianPairing period hPeriod choice
    (d9PrimitiveSpinCCliffordSection period hPeriod choice direction first)
      second base = _
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  rw [d9PrimitiveSpinCCliffordSection_apply]

/-- The derivative of the global current is computed by the two local flat
derivatives in any joint gauge containing the base point. -/
theorem d9PrimitiveSpinCGreenCurrent_mvfderiv
    (choice : NormalRootChoice) (direction derivativeDirection : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second) base
        (d9IntrinsicThroatFrame period hPeriod derivativeDirection base) =
      d9DoubledMatterSpinorHermitianPairing
          (d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice first
              index base))
          (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
            (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice
              second)
            index derivativeDirection base) +
        d9DoubledMatterSpinorHermitianPairing
          (d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
              (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod
                choice first)
              index derivativeDirection base))
          (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice second
            index base) := by
  let firstFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice first
  let secondFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice second
  let cliffordFamily :=
    d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice direction
      firstFamily
  let localCurrent : ThroatBase period hPeriod → Complex := fun current =>
    d9DoubledMatterSpinorHermitianPairing
      (cliffordFamily.localValue index current)
      (secondFamily.localValue index current)
  have hEventually :
      (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first second)
          =ᶠ[𝓝 base] localCurrent := by
    filter_upwards
      [(d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hBase]
      with current hCurrent
    change d9PrimitiveSpinCPointwiseHermitianPairing period hPeriod choice
        (d9PrimitiveSpinCCliffordSection period hPeriod choice direction first)
          second current = localCurrent current
    rw [d9PrimitiveSpinCPointwiseHermitianPairing_eq_coordChange period hPeriod
      choice index]
    change d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice
          (d9PrimitiveSpinCCliffordSection period hPeriod choice direction first)
            index current)
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice second
          index current) = localCurrent current
    rw [d9PrimitiveSpinCCliffordSection_localValue period hPeriod choice
      direction first index current hCurrent]
    rfl
  have hDerivativeEq := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners) (I' := 𝓘(Real, Complex)) hEventually
  have hMvDerivativeEq :
      mvfderiv throatCoverModelWithCorners
          (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second) base =
        mvfderiv throatCoverModelWithCorners localCurrent base := by
    exact hDerivativeEq
  rw [hMvDerivativeEq]
  have hFirstDiff : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) (cliffordFamily.localValue index) base :=
    ((cliffordFamily.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hBase))
      |>.mdifferentiableAt (by simp)
  have hSecondDiff : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) (secondFamily.localValue index) base :=
      ((secondFamily.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hBase))
      |>.mdifferentiableAt (by simp)
  change (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
      (fun current => d9DoubledMatterSpinorHermitianPairing
        (cliffordFamily.localValue index current)
        (secondFamily.localValue index current)) base)
      (d9IntrinsicThroatFrame period hPeriod derivativeDirection base) = _
  rw [d9DoubledMatterSpinorHermitianPairing_mfderiv
    period hPeriod (cliffordFamily.localValue index)
      (secondFamily.localValue index) base hFirstDiff hSecondDiff]
  change d9DoubledMatterSpinorHermitianPairing
        ((d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice
          direction firstFamily).localValue index base)
        (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
          secondFamily index derivativeDirection base) +
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
          (d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice
            direction firstFamily) index derivativeDirection base)
        (secondFamily.localValue index base) = _
  rw [d9PrimitiveSpinCCliffordLocalGaugeFamily_flatDerivative
    period hPeriod choice direction derivativeDirection firstFamily index base
      hBase]
  rfl

/-! ## Algebraic zeroth-order terms -/

/-- Unit-radial Clifford contraction directly on the quotient throat. -/
def d9PrimitiveSpinCBaseUnitRadialClifford
    (base : ThroatBase period hPeriod) (matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
      d9DoubledMatterFiberCliffordGamma direction matter

/-- The local radial spin correction contracts to minus unit-radial Clifford
multiplication. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_contraction
    (base : ThroatBase period hPeriod) (matter : D9DoubledMatterFiber) :
    (∑ direction : Fin 3,
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection period hPeriod direction
          base matter)) =
      -d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base matter := by
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) base
  simpa [d9PrimitiveSpinCBaseLeviCivitaSpinCorrection,
    d9PrimitiveSpinCBaseUnitRadialClifford,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk,
    d9LeviCivitaSpinCorrection, d9UnitRadialClifford] using
      d9LeviCivitaSpinCorrection_contraction period hPeriod point matter

/-- Unit-radial Clifford multiplication is skew-Hermitian. -/
theorem d9PrimitiveSpinCBaseUnitRadialClifford_pairing_skew
    (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base first)
        second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base second) := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  change d9DoubledMatterPairingLeftCLM second
      (∑ direction : Fin 3,
        d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
          d9DoubledMatterFiberCliffordGamma direction first) =
    -d9DoubledMatterPairingRightCLM first
      (∑ direction : Fin 3,
        d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
          d9DoubledMatterFiberCliffordGamma direction second)
  rw [map_sum, map_sum]
  simp_rw [d9DoubledMatterPairingLeftCLM_apply,
    d9DoubledMatterPairingRightCLM_apply,
    d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9DoubledMatterSpinorHermitianPairing_gamma,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right, mul_neg]
  rw [Finset.sum_neg_distrib]

/-- The commuting product `γᵢ I` is Hermitian, hence every real `U(1)`
connection coefficient cancels from the Green residual. -/
theorem d9PrimitiveSpinCGaugeCorrection_pairing_symmetric
    (direction : Fin 3) (coefficient : Real)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first
        (d9DoubledMatterFiberCliffordGamma direction
          (coefficient • d9PrimitiveSpinCImaginaryAction second)) =
      d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction
          (coefficient • d9PrimitiveSpinCImaginaryAction first)) second := by
  have hCommute (matter : D9DoubledMatterFiber) :
      d9DoubledMatterFiberCliffordGamma direction
          (d9PrimitiveSpinCImaginaryAction matter) =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGamma direction matter) := by
    unfold d9PrimitiveSpinCImaginaryAction
    exact
      (d9PrimitiveSpinCPhaseAction_clifford d9PrimitiveSpinCImaginaryPhase
        direction matter).symm
  rw [map_smul, map_smul,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right,
    d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9DoubledMatterSpinorHermitianPairing_gamma_right,
    hCommute,
    d9DoubledMatterSpinorHermitianPairing_imaginaryAction]

/-! ## Pointwise Green residual -/

private def d9PrimitiveSpinCLocalFlatDirac
    (choice : NormalRootChoice)
    (family : SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) : D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGamma direction
      (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice family
        index direction base)

private def d9PrimitiveSpinCLocalSpinCorrectionDirac
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGamma direction
      (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection period hPeriod direction
        base matter)

private def d9PrimitiveSpinCLocalGaugeCorrectionDirac
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGamma direction
      (d9PrimitiveSpinCTotalConnectionFrameCoefficient period hPeriod index.2
          direction base • d9PrimitiveSpinCImaginaryAction matter)

private theorem d9PrimitiveSpinCLocalGeometricDirac_eq_three_blocks
    (choice : NormalRootChoice)
    (family : SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCLocalGeometricDirac period hPeriod choice family index base =
      d9PrimitiveSpinCLocalFlatDirac period hPeriod choice family index base +
        d9PrimitiveSpinCLocalSpinCorrectionDirac period hPeriod base
          (family.localValue index base) +
        d9PrimitiveSpinCLocalGaugeCorrectionDirac period hPeriod index base
          (family.localValue index base) := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
    d9PrimitiveSpinCLocalDirectionalDerivative
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
    d9PrimitiveSpinCLocalFlatDirac
    d9PrimitiveSpinCLocalSpinCorrectionDirac
    d9PrimitiveSpinCLocalGaugeCorrectionDirac
  simp only [map_add, Finset.sum_add_distrib]
  abel

/-- Flat differential part of the Green residual is minus the divergence of
the global Clifford current. -/
theorem d9PrimitiveSpinCLocalFlatGreenResidual
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice first
          index base)
        (d9PrimitiveSpinCLocalFlatDirac period hPeriod choice
          (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice
            second) index base) -
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCLocalFlatDirac period hPeriod choice
          (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice
            first) index base)
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice second
          index base) =
      -∑ direction : Fin 3,
        mvfderiv throatCoverModelWithCorners
          (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second) base
          (d9IntrinsicThroatFrame period hPeriod direction base) := by
  unfold d9PrimitiveSpinCLocalFlatDirac
  change d9DoubledMatterPairingRightCLM
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice first
          index base)
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
              (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod
                choice second) index direction base)) -
      d9DoubledMatterPairingLeftCLM
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice second
          index base)
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCLocalFlatFrameDerivative period hPeriod choice
              (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod
                choice first) index direction base)) = _
  rw [map_sum, map_sum]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [d9DoubledMatterPairingRightCLM_apply,
    d9DoubledMatterPairingLeftCLM_apply]
  rw [d9DoubledMatterSpinorHermitianPairing_gamma_right]
  rw [d9PrimitiveSpinCGreenCurrent_mvfderiv period hPeriod choice direction
    direction first second index base hBase]
  ring

/-- Radial spin correction contributes exactly twice the radial current. -/
theorem d9PrimitiveSpinCLocalSpinGreenResidual
    (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first
        (d9PrimitiveSpinCLocalSpinCorrectionDirac period hPeriod base second) -
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCLocalSpinCorrectionDirac period hPeriod base first)
        second =
      2 * d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base first)
        second := by
  unfold d9PrimitiveSpinCLocalSpinCorrectionDirac
  rw [d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_contraction,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_contraction,
    d9PrimitiveSpinCBaseUnitRadialClifford_pairing_skew]
  rw [show -d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base second =
        (-1 : Real) • d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod
          base second by simp,
    show -d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base first =
        (-1 : Real) • d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod
          base first by simp,
    d9DoubledMatterSpinorHermitianPairing_real_smul_right,
    d9DoubledMatterSpinorHermitianPairing_real_smul_left]
  norm_num
  rw [d9PrimitiveSpinCBaseUnitRadialClifford_pairing_skew]
  ring

/-- The complete `U(1)` correction has zero Green residual pointwise. -/
theorem d9PrimitiveSpinCLocalGaugeGreenResidual
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first
        (d9PrimitiveSpinCLocalGaugeCorrectionDirac period hPeriod index base
          second) -
      d9DoubledMatterSpinorHermitianPairing
          (d9PrimitiveSpinCLocalGaugeCorrectionDirac period hPeriod index base
           first) second = 0 := by
  unfold d9PrimitiveSpinCLocalGaugeCorrectionDirac
  change d9DoubledMatterPairingRightCLM first
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCTotalConnectionFrameCoefficient period hPeriod
              index.2 direction base • d9PrimitiveSpinCImaginaryAction second)) -
      d9DoubledMatterPairingLeftCLM second
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGamma direction
            (d9PrimitiveSpinCTotalConnectionFrameCoefficient period hPeriod
              index.2 direction base • d9PrimitiveSpinCImaginaryAction first)) = 0
  rw [map_sum, map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro direction _
  simp only [d9DoubledMatterPairingRightCLM_apply,
    d9DoubledMatterPairingLeftCLM_apply]
  rw [d9PrimitiveSpinCGaugeCorrection_pairing_symmetric]
  exact sub_self _

/-- Pointwise Green identity for the genuine globally descended Dirac output. -/
theorem d9PrimitiveSpinCGeometricDirac_pointwiseGreen
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing (first base)
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice second
          base) -
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice first
          base) (second base) =
      -∑ direction : Fin 3,
        mvfderiv throatCoverModelWithCorners
          (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second) base
          (d9IntrinsicThroatFrame period hPeriod direction base) +
        2 * d9DoubledMatterSpinorHermitianPairing
          (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
            (first base))
          (second base) := by
  let index :=
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).indexAt base
  have hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).mem_baseSet_at base
  let firstFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice first
  let secondFamily :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice second
  have hFirstValue : firstFamily.localValue index base = first base := by
    exact d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_indexAt
      period hPeriod choice first base
  have hSecondValue : secondFamily.localValue index base = second base := by
    exact d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_indexAt
      period hPeriod choice second base
  dsimp [firstFamily, secondFamily, index] at hFirstValue hSecondValue ⊢
  rw [d9PrimitiveSpinCGeometricDiracOperator,
    d9PrimitiveSpinCGeometricDiracOperator,
    d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCLocalGeometricDirac_eq_three_blocks,
    d9PrimitiveSpinCLocalGeometricDirac_eq_three_blocks]
  rw [d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_right,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    d9DoubledMatterSpinorHermitianPairing_add_left,
    ← hFirstValue, ← hSecondValue]
  have hFlat := d9PrimitiveSpinCLocalFlatGreenResidual period hPeriod choice
    first second index base hBase
  have hSpin := d9PrimitiveSpinCLocalSpinGreenResidual period hPeriod base
    ((d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice first).localValue
      index base)
    ((d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice second).localValue
      index base)
  have hGauge := d9PrimitiveSpinCLocalGaugeGreenResidual period hPeriod index base
    ((d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice first).localValue
      index base)
    ((d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice second).localValue
      index base)
  dsimp [index, d9PrimitiveSpinCSmoothSectionLocalGaugeFamily]
    at hFlat hSpin hGauge ⊢
  linear_combination hFlat + hSpin + hGauge

/-- Radial current is exactly the coefficient contraction of the three Green
currents. -/
theorem d9PrimitiveSpinCBaseRadialCurrent_eq_sum
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (first base)) (second base) =
      ∑ direction : Fin 3,
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base :
          Complex) *
          d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second base := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  change d9DoubledMatterPairingLeftCLM
      (show D9DoubledMatterFiber from second base)
      (∑ direction : Fin 3,
        d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
          d9DoubledMatterFiberCliffordGamma direction
            (show D9DoubledMatterFiber from first base)) = _
  rw [map_sum]
  simp only [d9DoubledMatterPairingLeftCLM_apply]
  apply Finset.sum_congr rfl
  intro direction _
  rw [d9DoubledMatterSpinorHermitianPairing_real_smul_left,
    d9PrimitiveSpinCGreenCurrent_apply]

/-- Public pointwise Green certificate for the exact implemented Dirac. -/
structure ProgramPPrimitiveSpinCDiracPointwiseGreenCertificate4D : Prop where
  pointwise : ∀ choice first second base,
    d9DoubledMatterSpinorHermitianPairing (first base)
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice second
          base) -
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice first
          base) (second base) =
      -∑ direction : Fin 3,
        mvfderiv throatCoverModelWithCorners
          (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second) base
          (d9IntrinsicThroatFrame period hPeriod direction base) +
        2 * d9DoubledMatterSpinorHermitianPairing
          (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
            (first base)) (second base)

/-- All terms are constructed by the existing connection and frame geometry. -/
def programPPrimitiveSpinCDiracPointwiseGreenCertificate4D :
    ProgramPPrimitiveSpinCDiracPointwiseGreenCertificate4D period hPeriod where
  pointwise := d9PrimitiveSpinCGeometricDirac_pointwiseGreen period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCDiracGreenCurrent4D
end JanusFormal
