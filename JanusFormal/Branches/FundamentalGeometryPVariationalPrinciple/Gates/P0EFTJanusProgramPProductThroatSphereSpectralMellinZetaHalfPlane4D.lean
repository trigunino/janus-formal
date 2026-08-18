import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D

/-!
# Spectral Mellin zeta of the reduced product-throat sphere

On `1 < re s`, the Gamma-normalized Mellin transform is the absolutely
convergent Dirichlet series of the positive dimensionless sphere spectrum.
No continuation to the origin is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereSpectralMellinZetaHalfPlane4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- Positive dimensionless squared eigenvalue at a nonzero sphere level. -/
def reducedSphereDimensionlessEigenvalueSquared
    (data : ProductThroatSpectralData) (level : Nat) : Real :=
  (((level + 1 : Nat) : Real) *
    ((level + 1 + monopoleAbsCharge data : Nat) : Real))

theorem reducedSphereDimensionlessEigenvalueSquared_pos
    (data : ProductThroatSpectralData) (level : Nat) :
    0 < reducedSphereDimensionlessEigenvalueSquared data level := by
  unfold reducedSphereDimensionlessEigenvalueSquared
  positivity

theorem reducedSphereDimensionlessEigenvalueSquared_eq
    (data : ProductThroatSpectralData) (level : Nat) :
    reducedSphereDimensionlessEigenvalueSquared data level =
      data.sphereRadius ^ 2 * sphereEigenvalueSquared data level := by
  unfold reducedSphereDimensionlessEigenvalueSquared sphereEigenvalueSquared
  have hRadius : data.sphereRadius ≠ 0 := ne_of_gt data.sphereRadiusPositive
  field_simp [hRadius]

/-- Twice the positive-level multiplicity in the reduced dimensionless heat
trace. -/
def reducedSphereSpectralCoefficient
    (data : ProductThroatSpectralData) (level : Nat) : Complex :=
  (2 : Complex) * (sphereMultiplicity data level : Complex)

/-- One term of the dimensionless reduced-sphere spectral zeta series. -/
def reducedSphereSpectralZetaTerm
    (data : ProductThroatSpectralData) (spectral : Complex)
    (level : Nat) : Complex :=
  reducedSphereSpectralCoefficient data level /
    (reducedSphereDimensionlessEigenvalueSquared data level : Complex) ^ spectral

/-- Dimensionless reduced-sphere spectral zeta on its convergence
half-plane. -/
def reducedSphereSpectralZeta
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  ∑' level : Nat, reducedSphereSpectralZetaTerm data spectral level

/-- The positive dimensionless sphere heat trace is the exponential series
of the dimensionless positive spectrum. -/
theorem reducedSphereDimensionlessHeat_hasSum
    (data : ProductThroatSpectralData) {time : Real} (hTime : 0 < time) :
    HasSum (fun level : Nat =>
      reducedSphereSpectralCoefficient data level *
        (Real.exp
          (-reducedSphereDimensionlessEigenvalueSquared data level * time) :
            Complex))
      (positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace data) time : Complex) := by
  have hRadius : 0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  have hReal :=
    (sphere_heat_trace_has_sum data (time * data.sphereRadius ^ 2)
      (mul_pos hTime hRadius)).mul_left (2 : Real)
  have hComplex :
      HasSum (fun level : Nat =>
        ((2 * sphereHeatTerm data (time * data.sphereRadius ^ 2) level : Real) :
          Complex))
        ((2 * sphereHeatTrace data (time * data.sphereRadius ^ 2) : Real) :
          Complex) :=
    Complex.hasSum_ofReal.mpr hReal
  convert hComplex using 1 with level
  · funext level
    unfold reducedSphereSpectralCoefficient sphereHeatTerm
    rw [reducedSphereDimensionlessEigenvalueSquared_eq]
    have hExponent :
        -(data.sphereRadius ^ 2 * sphereEigenvalueSquared data level) * time =
          -(time * data.sphereRadius ^ 2) *
            sphereEigenvalueSquared data level := by
      ring
    rw [hExponent]
    norm_cast
    push_cast
    ring
  · rw [positiveTimeTraceExtension_of_pos _ hTime,
      dimensionlessReducedSphereHeatTrace_eq]

private theorem reducedSphereSpectralWeight_bound
    (data : ProductThroatSpectralData) (sigma : Real)
    (hSigma : 1 < sigma) (level : Nat) :
    ‖reducedSphereSpectralCoefficient data level‖ /
        reducedSphereDimensionlessEigenvalueSquared data level ^ sigma ≤
      (2 * ((monopoleAbsCharge data : Real) + 2)) *
        (((level + 1 : Nat) : Real) ^ (1 - 2 * sigma)) := by
  let n : Real := ((level + 1 : Nat) : Real)
  let q : Real := (monopoleAbsCharge data : Real)
  have hn : 1 ≤ n := by
    dsimp [n]
    norm_num
  have hnPos : 0 < n := zero_lt_one.trans_le hn
  have hq : 0 ≤ q := by positivity
  have hSigmaNonnegative : 0 ≤ sigma := le_trans (by norm_num) hSigma.le
  have hNumerator :
      ‖reducedSphereSpectralCoefficient data level‖ ≤
        (2 * (q + 2)) * n := by
    unfold reducedSphereSpectralCoefficient sphereMultiplicity
    dsimp [n, q]
    rw [norm_mul, Complex.norm_natCast]
    norm_num
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hn)]
  have hEigenvalue : n * n ≤
      reducedSphereDimensionlessEigenvalueSquared data level := by
    unfold reducedSphereDimensionlessEigenvalueSquared
    dsimp [n, q]
    push_cast
    nlinarith
  have hPower :
      (n * n) ^ sigma ≤
        reducedSphereDimensionlessEigenvalueSquared data level ^ sigma :=
    Real.rpow_le_rpow (mul_nonneg hnPos.le hnPos.le) hEigenvalue
      hSigmaNonnegative
  calc
    ‖reducedSphereSpectralCoefficient data level‖ /
          reducedSphereDimensionlessEigenvalueSquared data level ^ sigma ≤
        ((2 * (q + 2)) * n) /
          reducedSphereDimensionlessEigenvalueSquared data level ^ sigma :=
      div_le_div_of_nonneg_right hNumerator
        (Real.rpow_nonneg
          (reducedSphereDimensionlessEigenvalueSquared_pos data level).le _)
    _ ≤ ((2 * (q + 2)) * n) / (n * n) ^ sigma :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hq (by norm_num)))
          hnPos.le)
        (Real.rpow_pos_of_pos (mul_pos hnPos hnPos) _)
        hPower
    _ = (2 * (q + 2)) * n ^ (1 - 2 * sigma) := by
      rw [Real.mul_rpow hnPos.le hnPos.le,
        Real.rpow_sub hnPos, Real.rpow_one,
        show 2 * sigma = sigma + sigma by ring,
        Real.rpow_add hnPos]
      ring
    _ = (2 * ((monopoleAbsCharge data : Real) + 2)) *
        (((level + 1 : Nat) : Real) ^ (1 - 2 * sigma)) := by
      rfl

theorem reducedSphereSpectralWeight_summable
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    Summable (fun level : Nat =>
      ‖reducedSphereSpectralCoefficient data level‖ /
        reducedSphereDimensionlessEigenvalueSquared data level ^ spectral.re) := by
  have hPSeries : Summable (fun level : Nat =>
      (((level + 1 : Nat) : Real) ^ (1 - 2 * spectral.re))) := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  refine (hPSeries.mul_left
    (2 * ((monopoleAbsCharge data : Real) + 2))).of_nonneg_of_le ?_ ?_
  · intro level
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg
        (reducedSphereDimensionlessEigenvalueSquared_pos data level).le _)
  · exact reducedSphereSpectralWeight_bound data spectral.re hSpectral

theorem reducedSphereSpectralZeta_summable
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    Summable (reducedSphereSpectralZetaTerm data spectral) := by
  apply Summable.of_norm
  refine (reducedSphereSpectralWeight_summable data spectral hSpectral).congr ?_
  intro level
  unfold reducedSphereSpectralZetaTerm
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos
    (reducedSphereDimensionlessEigenvalueSquared_pos data level)]

/-- On `1 < re s`, termwise Mellin integration gives the Gamma-weighted
dimensionless sphere Dirichlet series. -/
theorem reducedSphereMellinDirichlet_hasSum
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    HasSum (fun level : Nat =>
      Complex.Gamma spectral * reducedSphereSpectralCoefficient data level /
        (reducedSphereDimensionlessEigenvalueSquared data level : Complex) ^
          spectral)
      (relativeHeatMellinIntegral
        (dimensionlessReducedSphereHeatTrace data) spectral) := by
  have hMellin := hasSum_mellin
    (a := reducedSphereSpectralCoefficient data)
    (p := reducedSphereDimensionlessEigenvalueSquared data)
    (F := fun time =>
      (positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace data) time : Complex))
    (s := spectral)
    (fun level => Or.inr
      (reducedSphereDimensionlessEigenvalueSquared_pos data level))
    (by linarith)
    (fun time hTime =>
      reducedSphereDimensionlessHeat_hasSum data hTime)
    (reducedSphereSpectralWeight_summable data spectral hSpectral)
  simpa [mellin, relativeHeatMellinIntegral, relativeHeatMellinKernel,
    smul_eq_mul] using hMellin

/-- Gamma normalization removes the Gamma factor from every spectral term. -/
theorem reducedSphereSpectralZeta_hasSum
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    HasSum (reducedSphereSpectralZetaTerm data spectral)
      (relativeHeatMellinZetaCandidate
        (dimensionlessReducedSphereHeatTrace data) spectral) := by
  have hGamma : Complex.Gamma spectral ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by linarith)
  unfold relativeHeatMellinZetaCandidate
  apply ((reducedSphereMellinDirichlet_hasSum data spectral hSpectral).mul_left
    (Complex.Gamma spectral)⁻¹).congr
  intro level
  unfold reducedSphereSpectralZetaTerm
  simp [div_eq_mul_inv, hGamma, mul_assoc]

/-- In its honest convergence half-plane, the Gamma-normalized heat Mellin
candidate equals the absolutely convergent spectral zeta series. -/
theorem relativeHeatMellinZetaCandidate_eq_reducedSphereSpectralZeta
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    relativeHeatMellinZetaCandidate
        (dimensionlessReducedSphereHeatTrace data) spectral =
      reducedSphereSpectralZeta data spectral := by
  unfold reducedSphereSpectralZeta
  exact (reducedSphereSpectralZeta_hasSum data spectral hSpectral).tsum_eq.symm

/-- Public checkpoint for the honest spectral/Mellin identity.  This gate
makes no assertion about continuation to the origin. -/
theorem product_throat_sphere_spectral_mellin_zeta_half_plane_gate
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    Summable (reducedSphereSpectralZetaTerm data spectral) ∧
      relativeHeatMellinZetaCandidate
          (dimensionlessReducedSphereHeatTrace data) spectral =
        reducedSphereSpectralZeta data spectral ∧
      IntegrableOn
        (relativeHeatMellinKernel
          (dimensionlessReducedSphereHeatTrace data) spectral)
        (Set.Ioi (0 : Real)) :=
  ⟨reducedSphereSpectralZeta_summable data spectral hSpectral,
    relativeHeatMellinZetaCandidate_eq_reducedSphereSpectralZeta
      data spectral hSpectral,
    reducedSphereMellinKernel_integrable data spectral hSpectral⟩

end
end P0EFTJanusProgramPProductThroatSphereSpectralMellinZetaHalfPlane4D
end JanusFormal
