import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

/-!
# Local Lorenz codifferential for the intrinsic abelian potential

In one genuine holonomic chart, the intrinsic one-form is raised with the
inverse metric and its Levi--Civita divergence is computed.  This is the
coordinate formula for `div_g (A♯)`.  On an exact potential `A = dc`, it is
the already constructed covariant scalar wave operator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coordinate components of the metric-raised intrinsic gauge one-form. -/
def localRaisedAbelianGaugePotential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 :=
  Matrix.mulVec
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
    (fun lower =>
      localGaugeCoefficient period hPeriod potential component patch lower
        coordinate)

theorem localRaisedAbelianGaugePotential_component_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper : Index4) :
    ContDiff Real ∞
      (fun coordinate =>
        localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate upper) := by
  change ContDiff Real ∞ (fun coordinate =>
    ∑ lower : Index4,
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ upper lower *
        localGaugeCoefficient period hPeriod potential component patch lower
          coordinate)
  apply ContDiff.sum
  intro lower _
  exact
    (localMetricInverseEntry_contDiff period hPeriod metric patch upper lower).mul
      (localGaugeCoefficient_contDiff period hPeriod potential component patch
        lower)

theorem localRaisedAbelianGaugePotential_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localRaisedAbelianGaugePotential period hPeriod metric potential
        component patch) := by
  rw [contDiff_pi]
  exact localRaisedAbelianGaugePotential_component_contDiff period hPeriod
    metric potential component patch

theorem localGaugeCoefficient_exact
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) (coordinate : Vector4) :
    localGaugeCoefficient period hPeriod
        (exactGaugePotential period hPeriod parameter) component patch index
        coordinate =
      localScalarGradient period hPeriod
        (ghostComponent period hPeriod parameter component) patch coordinate
        index := by
  change
    scalarDifferential period hPeriod
        (ghostComponent period hPeriod parameter component)
        (patch.coordinateMap coordinate) (patch.frame coordinate index) =
      _
  exact
    (localScalarGradient_eq_scalarDifferential_frame period hPeriod
      (ghostComponent period hPeriod parameter component) patch coordinate
      index).symm

theorem localRaisedAbelianGaugePotential_exact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localRaisedAbelianGaugePotential period hPeriod metric
        (exactGaugePotential period hPeriod parameter) component patch =
      localActualScalarRaisedGradient period hPeriod metric patch
        (ghostComponent period hPeriod parameter component) := by
  funext coordinate upper
  unfold localRaisedAbelianGaugePotential
    localActualScalarRaisedGradient Matrix.mulVec dotProduct
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  simp_rw [localGaugeCoefficient_exact period hPeriod parameter component patch]

theorem localRaisedAbelianGaugePotential_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localRaisedAbelianGaugePotential period hPeriod metric (first + second)
        component patch =
      localRaisedAbelianGaugePotential period hPeriod metric first component
          patch +
        localRaisedAbelianGaugePotential period hPeriod metric second component
          patch := by
  funext coordinate upper
  simp only [localRaisedAbelianGaugePotential, Matrix.mulVec, dotProduct,
    Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro lower _
  change
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ upper lower *
        ((first.toFun component (patch.coordinateMap coordinate) +
          second.toFun component (patch.coordinateMap coordinate))
          (patch.frame coordinate lower)) =
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ upper lower *
          first.toFun component (patch.coordinateMap coordinate)
            (patch.frame coordinate lower) +
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ upper lower *
          second.toFun component (patch.coordinateMap coordinate)
            (patch.frame coordinate lower)
  rw [add_apply]
  ring

theorem localRaisedAbelianGaugePotential_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localRaisedAbelianGaugePotential period hPeriod metric (scalar • potential)
        component patch =
      scalar • localRaisedAbelianGaugePotential period hPeriod metric potential
        component patch := by
  funext coordinate upper
  simp only [localRaisedAbelianGaugePotential, Matrix.mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  unfold localGaugeCoefficient
  rw [smoothAbelianGaugePotential_smul_apply]
  ring

/-- Holonomic formula `∂_μ A^μ + Γ^μ_{μρ} A^ρ` for `div_g (A♯)`. -/
def localAbelianLorenzDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ derivative : Index4,
    (fderiv Real
        (fun current =>
          localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch current derivative)
        coordinate (Pi.single derivative 1) +
      ∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch coordinate lower)

theorem localAbelianLorenzDivergence_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localAbelianLorenzDivergence period hPeriod metric potential component
        patch) := by
  apply ContDiff.sum
  intro derivative _
  apply ContDiff.add
  · exact
      ((localRaisedAbelianGaugePotential_component_contDiff period hPeriod
          metric potential component patch derivative).fderiv_right
        (m := ∞) (by simp)).clm_apply contDiff_const
  · apply ContDiff.sum
    intro lower _
    exact
      (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        derivative derivative lower).mul
        (localRaisedAbelianGaugePotential_component_contDiff period hPeriod
          metric potential component patch lower)

theorem localAbelianLorenzDivergence_exact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric
        (exactGaugePotential period hPeriod parameter) component patch
        coordinate =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (ghostComponent period hPeriod parameter component) coordinate) := by
  rw [localAbelianLorenzDivergence,
    localRaisedAbelianGaugePotential_exact]
  exact localActualScalarRaisedGradientDivergence_eq_wave period hPeriod metric
    patch (ghostComponent period hPeriod parameter component) coordinate

theorem localAbelianLorenzDivergence_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric (first + second)
        component patch coordinate =
      localAbelianLorenzDivergence period hPeriod metric first component patch
          coordinate +
        localAbelianLorenzDivergence period hPeriod metric second component patch
          coordinate := by
  have hFirst (index : Index4) :
      DifferentiableAt Real
        (fun current =>
          localRaisedAbelianGaugePotential period hPeriod metric first component
            patch current index) coordinate :=
    (localRaisedAbelianGaugePotential_component_contDiff period hPeriod metric
      first component patch index).differentiable (by simp) coordinate
  have hSecond (index : Index4) :
      DifferentiableAt Real
        (fun current =>
          localRaisedAbelianGaugePotential period hPeriod metric second
            component patch current index) coordinate :=
    (localRaisedAbelianGaugePotential_component_contDiff period hPeriod metric
      second component patch index).differentiable (by simp) coordinate
  have hFunction (index : Index4) :
      (fun current =>
        localRaisedAbelianGaugePotential period hPeriod metric (first + second)
          component patch current index) =
        (fun current =>
          localRaisedAbelianGaugePotential period hPeriod metric first component
            patch current index) +
          fun current =>
            localRaisedAbelianGaugePotential period hPeriod metric second
              component patch current index := by
    funext current
    exact congrFun
      (congrFun
        (localRaisedAbelianGaugePotential_add period hPeriod metric first second
          component patch) current) index
  have hDerivative (index : Index4) :
      fderiv Real
          (fun current =>
            localRaisedAbelianGaugePotential period hPeriod metric
              (first + second) component patch current index) coordinate =
        fderiv Real
            (fun current =>
              localRaisedAbelianGaugePotential period hPeriod metric first
                component patch current index) coordinate +
          fderiv Real
            (fun current =>
              localRaisedAbelianGaugePotential period hPeriod metric second
                component patch current index) coordinate := by
    rw [hFunction index, fderiv_add (hFirst index) (hSecond index)]
  have hRaisedAt (index : Index4) :
      localRaisedAbelianGaugePotential period hPeriod metric (first + second)
          component patch coordinate index =
        localRaisedAbelianGaugePotential period hPeriod metric first component
            patch coordinate index +
          localRaisedAbelianGaugePotential period hPeriod metric second
            component patch coordinate index :=
    congrFun
      (congrFun
        (localRaisedAbelianGaugePotential_add period hPeriod metric first second
          component patch) coordinate) index
  unfold localAbelianLorenzDivergence
  simp_rw [hDerivative, add_apply, hRaisedAt, mul_add,
    Finset.sum_add_distrib]
  ring

theorem localAbelianLorenzDivergence_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric (scalar • potential)
        component patch coordinate =
      scalar *
        localAbelianLorenzDivergence period hPeriod metric potential component
          patch coordinate := by
  have hPotential (index : Index4) :
      DifferentiableAt Real
        (fun current =>
          localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch current index) coordinate :=
    (localRaisedAbelianGaugePotential_component_contDiff period hPeriod metric
      potential component patch index).differentiable (by simp) coordinate
  have hFunction (index : Index4) :
      (fun current =>
        localRaisedAbelianGaugePotential period hPeriod metric
          (scalar • potential) component patch current index) =
        fun current =>
          scalar *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch current index := by
    funext current
    exact congrFun
      (congrFun
        (localRaisedAbelianGaugePotential_smul period hPeriod metric scalar
          potential component patch) current) index
  have hDerivative (index : Index4) :
      fderiv Real
          (fun current =>
            localRaisedAbelianGaugePotential period hPeriod metric
              (scalar • potential) component patch current index) coordinate =
        scalar •
          fderiv Real
            (fun current =>
              localRaisedAbelianGaugePotential period hPeriod metric potential
                component patch current index) coordinate := by
    rw [hFunction index, fderiv_const_mul (hPotential index) scalar]
  have hRaisedAt (index : Index4) :
      localRaisedAbelianGaugePotential period hPeriod metric
          (scalar • potential) component patch coordinate index =
        scalar *
          localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch coordinate index := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun
        (congrFun
          (localRaisedAbelianGaugePotential_smul period hPeriod metric scalar
            potential component patch) coordinate) index
  unfold localAbelianLorenzDivergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [hDerivative derivative, smul_apply]
  simp_rw [hRaisedAt]
  have hConnection :
      (∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          (scalar *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate lower)) =
        scalar *
          ∑ lower : Index4,
            localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
              localRaisedAbelianGaugePotential period hPeriod metric potential
                component patch coordinate lower := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  rw [hConnection]
  ring

end
end P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
end JanusFormal
