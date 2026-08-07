import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

/-!
# Global Green closure for the primitive SpinC Dirac operator

The pointwise Green residual constructed previously is

`-∑ᵢ eᵢ Jᵢ + 2 ⟨γ(n)ψ,φ⟩`.

The intrinsic-frame integration-by-parts theorem gives

`∫ eᵢ Jᵢ = 2 ∫ nᵢ Jᵢ`,

and the radial-current identity identifies `∑ᵢ nᵢJᵢ` with
`⟨γ(n)ψ,φ⟩`.  The two contributions therefore cancel exactly.  This proves
formal symmetry of the genuine globally descended first-order Dirac operator
on the whole primitive smooth core.

Consequently the maximal-domain, coefficient-intertwining, Parseval and
same-action matter graph packages are all unconditional for every real matter
mass.  No boundary condition, spectral-decay input, graph-core hypothesis or
D10 direction remains in the SpinC part of H14.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff BigOperators InnerProductSpace ENNReal lp LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenCurrent4D
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

local instance throatBaseCompactSpace : CompactSpace (ThroatBase period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) := borel _

local instance throatBaseBorelSpace : BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-! ## Smooth fields appearing in the integrated residual -/

/-- One intrinsic derivative of one global Green current, packaged as a smooth
complex throat field. -/
def d9PrimitiveSpinCGreenCurrentIntrinsicDerivative
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    SmoothThroatField period hPeriod Complex where
  toFun base :=
    mvfderiv throatCoverModelWithCorners
      (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
        second).toFun base
      (d9IntrinsicThroatFrame period hPeriod direction base)
  contMDiff_toFun := by
    have hDerivative :=
      (contMDiff_snd_tangentBundle_modelSpace Complex 𝓘(Real, Complex)).comp
        (((d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
            second).contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
          (d9IntrinsicThroatFrame period hPeriod direction).contMDiff_toFun)
    convert hDerivative using 1
    rfl

@[simp]
theorem d9PrimitiveSpinCGreenCurrentIntrinsicDerivative_apply
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod choice
        direction first second base =
      mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second).toFun base
        (d9IntrinsicThroatFrame period hPeriod direction base) :=
  rfl

/-- Radial Green current written as the exact finite contraction of the three
global currents. -/
def d9PrimitiveSpinCRadialGreenCurrent
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    SmoothThroatField period hPeriod Complex where
  toFun base :=
    ∑ direction : Fin 3,
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
        d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second base
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro direction _
    exact
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod direction).smul
        (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second).contMDiff_toFun

/-- The smooth finite contraction is exactly the radial Clifford pairing. -/
theorem d9PrimitiveSpinCRadialGreenCurrent_apply
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first second base =
      d9DoubledMatterSpinorHermitianPairing
        (d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (first base)) (second base) := by
  rw [d9PrimitiveSpinCBaseRadialCurrent_eq_sum]
  apply Finset.sum_congr rfl
  intro direction _
  change
    d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
        d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second base =
      (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base :
          Complex) *
        d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second base
  rfl

private theorem d9PrimitiveSpinCGreenCurrentIntrinsicDerivative_integrable
    (choice : NormalRootChoice) (direction : Fin 3)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Integrable
      (d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod choice
        direction first second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod choice
    direction first second).contMDiff_toFun.continuous
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem d9PrimitiveSpinCRadialGreenCurrent_integrable
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Integrable
      (d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first second)
    |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-! ## Integrated cancellation -/

/-- The integral of the pointwise Green residual is exactly zero. -/
theorem d9PrimitiveSpinCGeometricDirac_integratedGreenResidual_eq_zero
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    (∫ base,
      (d9PrimitiveSpinCPointwiseHermitianPairing period hPeriod choice first
          (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice second)
          base -
        d9PrimitiveSpinCPointwiseHermitianPairing period hPeriod choice
          (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice first)
          second base)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0 := by
  have hDerivativeIntegrable (direction : Fin 3) :=
    d9PrimitiveSpinCGreenCurrentIntrinsicDerivative_integrable period hPeriod
      choice direction first second
  have hSumIntegrable : Integrable
      (fun base =>
        ∑ direction : Fin 3,
          d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod choice
            direction first second base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    integrable_finset_sum Finset.univ fun direction _ =>
      hDerivativeIntegrable direction
  have hRadialIntegrable :=
    d9PrimitiveSpinCRadialGreenCurrent_integrable period hPeriod choice first
      second
  calc
    _ = ∫ base,
        (-∑ direction : Fin 3,
            d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod
              choice direction first second base) +
          (2 : Complex) •
            d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first
              second base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      filter_upwards with base
      rw [d9PrimitiveSpinCGeometricDirac_pointwiseGreen]
      simp only [d9PrimitiveSpinCGreenCurrentIntrinsicDerivative_apply,
        d9PrimitiveSpinCRadialGreenCurrent_apply]
      rfl
    _ =
        -(∑ direction : Fin 3,
          ∫ base,
            d9PrimitiveSpinCGreenCurrentIntrinsicDerivative period hPeriod
              choice direction first second base
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
          (2 : Complex) •
            ∫ base,
              d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first
                second base
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      rw [integral_add hSumIntegrable.neg
        (hRadialIntegrable.const_smul (2 : Complex)),
        integral_neg, integral_finsetSum Finset.univ
          (fun direction _ => hDerivativeIntegrable direction),
        integral_const_smul]
    _ =
        -(∑ direction : Fin 3,
          (2 : Real) •
            ∫ base,
              d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
                  base •
                d9PrimitiveSpinCGreenCurrent period hPeriod choice direction
                  first second base
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
          (2 : Complex) •
            ∫ base,
              d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first
                second base
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply congrArg (fun value => -value +
        (2 : Complex) •
          ∫ base,
            d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first second
              base
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      apply Finset.sum_congr rfl
      intro direction _
      exact d9IntrinsicThroatFrame_integral_mvfderiv_eq_two period hPeriod
        (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
          second) direction
    _ =
        -(2 : Complex) •
            ∫ base,
              d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first
                second base
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
          (2 : Complex) •
            ∫ base,
              d9PrimitiveSpinCRadialGreenCurrent period hPeriod choice first
                second base
              ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      congr 1
      rw [Finset.smul_sum, integral_finsetSum]
      · apply congrArg ((2 : Complex) • ·)
        apply integral_congr_ae
        filter_upwards with base
        rfl
      · intro direction _
        exact
          ((d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod
              direction).smul
            (d9PrimitiveSpinCGreenCurrent period hPeriod choice direction first
              second).contMDiff_toFun).continuous
              |>.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)
    _ = 0 := by simp

/-- Formal symmetry of the globally descended primitive SpinC Dirac operator
for the independently integrated geometric `L²` pairing. -/
theorem d9PrimitiveSpinCGeometricDirac_pairing_symm
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricL2Pairing period hPeriod choice first
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice second) =
      d9PrimitiveSpinCGeometricL2Pairing period hPeriod choice
        (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice first)
        second := by
  have hFirstIntegrable :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable period hPeriod choice
      first (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice second)
  have hSecondIntegrable :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable period hPeriod choice
      (d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice first) second
  apply sub_eq_zero.mp
  unfold d9PrimitiveSpinCGeometricL2Pairing
  rw [← integral_sub hFirstIntegrable hSecondIntegrable]
  exact d9PrimitiveSpinCGeometricDirac_integratedGreenResidual_eq_zero
    period hPeriod choice first second

/-- Unconditional inhabitant of the sole SpinC input retained by the previous
Green-to-maximal-domain reduction. -/
def programPPrimitiveSpinCSmoothDiracFormalSymmetryData4D :
    ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod where
  pairing_symm := by
    intro first second
    change
      d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter first
          (d9PrimitiveSpinCGeometricDiracOperator period hPeriod
            .positiveQuarter second) =
        d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator period hPeriod
            .positiveQuarter first) second
    exact d9PrimitiveSpinCGeometricDirac_pairing_symm period hPeriod
      .positiveQuarter first second

/-- Every real matter mass now has the exact maximal-domain and same-action
primitive SpinC graph realization without any analytic input. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
    (massSquared : Real) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_diracFormalSymmetry
    period hPeriod massSquared
      (programPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)

/-- Public certificate: the SpinC part of the global Hessian frontier is closed
by the implemented throat geometry alone. -/
structure ProgramPPrimitiveSpinCDiracGreenClosureCertificate4D : Prop where
  formalSymmetry :
    ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod
  graphRealization : ∀ massSquared,
    Nonempty
      (ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod
        massSquared)

/-- Unconditional terminal SpinC certificate. -/
def programPPrimitiveSpinCDiracGreenClosureCertificate4D :
    ProgramPPrimitiveSpinCDiracGreenClosureCertificate4D period hPeriod where
  formalSymmetry :=
    programPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod
  graphRealization := fun massSquared =>
    ⟨programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
      period hPeriod massSquared⟩

end
end P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
end JanusFormal
