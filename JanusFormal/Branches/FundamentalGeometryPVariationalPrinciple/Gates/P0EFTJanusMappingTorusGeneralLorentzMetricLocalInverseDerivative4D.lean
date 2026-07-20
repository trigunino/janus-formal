import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

/-!
# Actual derivative of the local inverse Lorentz metric

The algebraic inverse-metric derivative stored in the local Levi--Civita jet is
identified here with the genuine Frechet derivative of the smooth inverse
metric matrix in every coordinate basis direction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

variable (period : Real) (hPeriod : period ≠ 0)

theorem localMetricMatrix_fderiv_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate
        (Pi.single derivative 1) =
      metricDerivativeMatrix
        (localMetricDerivative period hPeriod metric patch coordinate) derivative := by
  ext first second
  have hMatrix : DifferentiableAt Real
      (localMetricMatrix period hPeriod metric patch) coordinate :=
    ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable
      (by simp)).differentiableAt
  have hRow : DifferentiableAt Real
      (fun current => localMetricMatrix period hPeriod metric patch current first)
      coordinate :=
    differentiableAt_pi.1 hMatrix first
  have hFirst := fderiv_apply hMatrix first
  have hSecond := fderiv_apply hRow second
  unfold metricDerivativeMatrix localMetricDerivative
  change
    (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate
        (Pi.single derivative 1)) first second =
      fderiv Real
        (localMetricCoefficient period hPeriod metric patch first second)
        coordinate (Pi.single derivative 1)
  have hFirstEntry :
      (fderiv Real
          (fun current => localMetricMatrix period hPeriod metric patch current first)
          coordinate (Pi.single derivative 1)) second =
        (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate
          (Pi.single derivative 1)) first second := by
    have hApply := congrArg
      (fun map => map (Pi.single derivative 1)) hFirst
    exact congrArg (fun row => row second) hApply
  have hSecondEntry :
      fderiv Real
          (fun current => localMetricMatrix period hPeriod metric patch current first second)
          coordinate (Pi.single derivative 1) =
        (fderiv Real
          (fun current => localMetricMatrix period hPeriod metric patch current first)
          coordinate (Pi.single derivative 1)) second := by
    exact congrArg (fun map => map (Pi.single derivative 1)) hSecond
  exact hFirstEntry.symm.trans (by
    simpa [localMetricMatrix] using hSecondEntry.symm)

/-- Genuine coordinate derivative of the smooth inverse metric matrix. -/
def localActualInverseMetricDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) : Matrix4 :=
  fderiv Real
    (fun current => Ring.inverse
      (localMetricMatrix period hPeriod metric patch current))
    coordinate (Pi.single derivative 1)

/-- The genuine derivative is exactly the differentiated-inverse expression
used by the local Levi--Civita connection jet. -/
theorem localActualInverseMetricDerivative_eq_leviCivita
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative =
      -((localMetricMatrix period hPeriod metric patch coordinate)⁻¹ *
          metricDerivativeMatrix
            (localMetricDerivative period hPeriod metric patch coordinate) derivative *
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹) := by
  have hMetric : DifferentiableAt Real
      (localMetricMatrix period hPeriod metric patch) coordinate :=
    ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable
      (by simp)).differentiableAt
  let unitMetric : Matrix4ˣ :=
    (localFixedSignMetric period hPeriod metric patch coordinate).metric_isUnit.unit
  have hUnitSpec : (unitMetric : Matrix4) =
      localMetricMatrix period hPeriod metric patch coordinate :=
    (localFixedSignMetric period hPeriod metric patch coordinate).metric_isUnit.unit_spec
  have hInverse := (hasFDerivAt_ringInverse (R := Matrix4) (𝕜 := Real) unitMetric).comp
    coordinate hMetric.hasFDerivAt
  unfold localActualInverseMetricDerivative
  change (fderiv Real
      (Ring.inverse ∘ localMetricMatrix period hPeriod metric patch) coordinate)
      (Pi.single derivative 1) = _
  calc
    _ = ((-ContinuousLinearMap.mulLeftRight Real Matrix4
          (↑(unitMetric⁻¹) : Matrix4) (↑(unitMetric⁻¹) : Matrix4)).comp
          (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate))
          (Pi.single derivative 1) :=
      congrArg (fun map => map (Pi.single derivative 1)) hInverse.fderiv
    _ = _ := by
      simp only [ContinuousLinearMap.comp_apply]
      change -((↑(unitMetric⁻¹) : Matrix4) *
          (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate)
            (Pi.single derivative 1) *
        (↑(unitMetric⁻¹) : Matrix4)) = _
      rw [localMetricMatrix_fderiv_basis]
      simp [hUnitSpec]

theorem localActualInverseMetricDerivative_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative
        first second =
      leviCivitaInverseMetricDerivative
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localMetricDerivative period hPeriod metric patch coordinate)
        derivative first second := by
  rw [localActualInverseMetricDerivative_eq_leviCivita]
  rfl

/-- Entrywise form: differentiating an actual inverse coefficient gives the
corresponding entry of the matrix derivative above. -/
theorem localMetricInverseEntry_fderiv_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    fderiv Real
        (fun current => Ring.inverse
          (localMetricMatrix period hPeriod metric patch current) first second)
        coordinate (Pi.single derivative 1) =
      localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative
        first second := by
  have hInverse : DifferentiableAt Real
      (fun current => Ring.inverse
        (localMetricMatrix period hPeriod metric patch current)) coordinate := by
    have hFunctions :
        (fun current => Ring.inverse
          (localMetricMatrix period hPeriod metric patch current)) =
        fun current => (localMetricMatrix period hPeriod metric patch current)⁻¹ := by
      funext current
      exact (Matrix.nonsing_inv_eq_ringInverse
        (A := localMetricMatrix period hPeriod metric patch current)).symm
    rw [hFunctions]
    exact ((localMetricInverse_contDiff period hPeriod metric patch).differentiable
      (by simp)).differentiableAt
  have hRow : DifferentiableAt Real
      (fun current => Ring.inverse
        (localMetricMatrix period hPeriod metric patch current) first) coordinate :=
    differentiableAt_pi.1 hInverse first
  have hFirst := fderiv_apply hInverse first
  have hSecond := fderiv_apply hRow second
  have hFirstEntry :
      (fderiv Real
          (fun current => Ring.inverse
            (localMetricMatrix period hPeriod metric patch current) first)
          coordinate (Pi.single derivative 1)) second =
        (fderiv Real
          (fun current => Ring.inverse
            (localMetricMatrix period hPeriod metric patch current))
          coordinate (Pi.single derivative 1)) first second := by
    have hApply := congrArg (fun map => map (Pi.single derivative 1)) hFirst
    exact congrArg (fun row => row second) hApply
  have hSecondEntry := congrArg
    (fun map => map (Pi.single derivative 1)) hSecond
  exact hSecondEntry.trans hFirstEntry

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
end JanusFormal
