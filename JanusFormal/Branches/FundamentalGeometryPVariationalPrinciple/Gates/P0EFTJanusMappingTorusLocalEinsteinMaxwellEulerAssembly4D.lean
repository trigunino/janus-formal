import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D

/-!
# Local Einstein--Maxwell Euler assembly

After the Palatini/GHY and Maxwell boundary currents have been removed, the
remaining pointwise first variation is exactly the coupled metric and gauge
Euler pairing.  Stationarity under independent variations is equivalent to
both weak tensor equations.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalEinsteinMaxwellEulerAssembly4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

local instance localRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  inferInstance

local instance localRealNormedSpace : NormedSpace ℝ ℝ :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup ℝ :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module ℝ ℝ :=
  localRealNormedSpace.toModule

def coupledMetricEulerPairing
    (gravitationalCoupling volume : ℝ)
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ)
    (curvature : Fin 2 → Matrix4) (inverseVelocity : Matrix4) : ℝ :=
  (volume / (2 * gravitationalCoupling)) *
      tensorPairing inverseVelocity
        (einsteinTensorAt metric inverse ricci cosmologicalConstant) +
    (volume / 2) *
      variationalMaxwellInverseStressPairing metric inverse curvature
        inverseVelocity

def coupledGaugeEulerPairing
    (excitation : Fin 2 → Vector4 → Matrix4) (coordinate : Vector4)
    (variation : Fin 2 → Vector4) : ℝ :=
  ∑ component : Fin 2, ∑ index : Index4,
    maxwellEulerCoefficient (excitation component) coordinate index *
      variation component index

def localEinsteinMaxwellBulkEuler
    (gravitationalCoupling volume : ℝ)
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ)
    (curvature : Fin 2 → Matrix4)
    (excitation : Fin 2 → Vector4 → Matrix4) (coordinate : Vector4)
    (inverseVelocity : Matrix4) (gaugeVariation : Fin 2 → Vector4) : ℝ :=
  coupledMetricEulerPairing gravitationalCoupling volume metric inverse ricci
      cosmologicalConstant curvature inverseVelocity +
    coupledGaugeEulerPairing excitation coordinate gaugeVariation

/-- The complete local first variation is the coupled Euler pairing plus
the derived EH Palatini divergence and minus the derived Maxwell boundary
divergence. -/
theorem localEinsteinMaxwellFirstVariation_eq_bulk_add_boundary
    (gravitationalCoupling cosmologicalConstant : ℝ)
    (metric ricci inverseVelocity : Matrix4)
    (volumeField : Vector4 → ℝ) (inverseField : Vector4 → Matrix4)
    (curvatureField : Fin 2 → Vector4 → Matrix4)
    (gaugeVariation : Fin 2 → Vector4 → Vector4)
    (coordinate : Vector4) (palatiniJet : DensitizedPalatiniJet4)
    (hVolumeAt : volumeField coordinate = palatiniJet.volume)
    (hInverseAt : inverseField coordinate = palatiniJet.inverse)
    (hCurvatureSkew : ∀ component first second,
      curvatureField component coordinate second first =
        -curvatureField component coordinate first second)
    (hExcitation : ∀ component first second,
      DifferentiableAt ℝ
        (fun current =>
          maxwellExcitationField volumeField inverseField curvatureField
            component current first second) coordinate)
    (hGaugeVariation : ∀ component second,
      DifferentiableAt ℝ
        (fun current => gaugeVariation component current second) coordinate) :
    einsteinHilbertDensityVelocity gravitationalCoupling
          cosmologicalConstant (volumeField coordinate)
          (-((volumeField coordinate) / 2) *
            tensorPairing metric inverseVelocity)
          (inverseField coordinate) ricci inverseVelocity
          (fun first second =>
            ricciVelocityFromConnection palatiniJet.connectionJet
              first second) +
        localMaxwellMetricVariation (volumeField coordinate)
          (-((volumeField coordinate) / 2) *
            matrixPairing metric inverseVelocity)
          (inverseField coordinate) inverseVelocity
          (fun component => curvatureField component coordinate) +
        localMaxwellGaugeVariation (volumeField coordinate)
          (inverseField coordinate)
          (fun component => curvatureField component coordinate)
          (fun component =>
            gaugeCurvatureVelocity (gaugeVariation component) coordinate) =
      localEinsteinMaxwellBulkEuler gravitationalCoupling
          (volumeField coordinate) metric (inverseField coordinate) ricci
          cosmologicalConstant
          (fun component => curvatureField component coordinate)
          (maxwellExcitationField volumeField inverseField curvatureField)
          coordinate inverseVelocity
          (fun component => gaugeVariation component coordinate) +
        (1 / (2 * gravitationalCoupling)) *
          densitizedPalatiniCoordinateDivergence palatiniJet -
        ∑ component : Fin 2,
          maxwellBoundaryDivergence
            (maxwellExcitationField volumeField inverseField curvatureField
              component)
            (gaugeVariation component) coordinate := by
  rw [hVolumeAt, hInverseAt]
  have hGaugeMetric :=
    localMaxwellGaugeVariation_eq_sum_raw volumeField inverseField
      curvatureField gaugeVariation coordinate
      (fun first second => by
        rw [hInverseAt]
        exact palatiniJet.inverse_symmetric first second)
  have hExcitationSkew : ∀ component first second,
      maxwellExcitationField volumeField inverseField curvatureField component
          coordinate second first =
        -maxwellExcitationField volumeField inverseField curvatureField
          component coordinate first second := by
    intro component first second
    unfold maxwellExcitationField
    have hSkew := maxwellExcitationAt_skew
      (volumeField coordinate) (inverseField coordinate)
      (curvatureField component coordinate)
      (hCurvatureSkew component)
    exact congrFun (congrFun hSkew first) second
  have hRaw (component : Fin 2) :=
    rawMaxwellGaugeVariation_eq_euler_sub_boundaryDivergence
      (maxwellExcitationField volumeField inverseField curvatureField component)
      (gaugeVariation component) coordinate
      (hExcitation component) (hGaugeVariation component)
      (hExcitationSkew component)
  have hRawSum :
      (∑ component : Fin 2,
        rawMaxwellGaugeVariation
          (maxwellExcitationField volumeField inverseField curvatureField
            component)
          (gaugeVariation component) coordinate) =
        coupledGaugeEulerPairing
            (maxwellExcitationField volumeField inverseField curvatureField)
            coordinate
            (fun component => gaugeVariation component coordinate) -
          ∑ component : Fin 2,
            maxwellBoundaryDivergence
              (maxwellExcitationField volumeField inverseField curvatureField
                component)
              (gaugeVariation component) coordinate := by
    simp_rw [hRaw, Finset.sum_sub_distrib]
    rfl
  rw [hVolumeAt, hInverseAt] at hGaugeMetric
  rw [einsteinHilbertDensityVelocity_eq_einstein_add_palatini,
    palatiniScalarVelocity_fromConnection,
    localMaxwellMetricVariation_eq_inverseStressPairing,
    hGaugeMetric, hRawSum]
  have hPalatini :=
    volume_mul_contractedPalatiniDerivative_eq_coordinateDivergence
      palatiniJet
  unfold localEinsteinMaxwellBulkEuler coupledMetricEulerPairing
  rw [← hPalatini]
  ring

def SatisfiesCoupledMetricEquation
    (gravitationalCoupling volume : ℝ)
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ)
    (curvature : Fin 2 → Matrix4) : Prop :=
  ∀ inverseVelocity : Matrix4,
    coupledMetricEulerPairing gravitationalCoupling volume metric inverse ricci
      cosmologicalConstant curvature inverseVelocity = 0

def SatisfiesMaxwellEquation
    (excitation : Fin 2 → Vector4 → Matrix4) (coordinate : Vector4) : Prop :=
  ∀ component index,
    maxwellEulerCoefficient (excitation component) coordinate index = 0

def IsEinsteinMaxwellBulkStationary
    (gravitationalCoupling volume : ℝ)
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ)
    (curvature : Fin 2 → Matrix4)
    (excitation : Fin 2 → Vector4 → Matrix4) (coordinate : Vector4) : Prop :=
  ∀ (inverseVelocity : Matrix4) (gaugeVariation : Fin 2 → Vector4),
    localEinsteinMaxwellBulkEuler gravitationalCoupling volume metric inverse
      ricci cosmologicalConstant curvature excitation coordinate
      inverseVelocity gaugeVariation = 0

theorem bulkStationary_iff_coupledMetric_and_maxwell
    (gravitationalCoupling volume : ℝ)
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ)
    (curvature : Fin 2 → Matrix4)
    (excitation : Fin 2 → Vector4 → Matrix4) (coordinate : Vector4) :
    IsEinsteinMaxwellBulkStationary gravitationalCoupling volume metric inverse
        ricci cosmologicalConstant curvature excitation coordinate ↔
      SatisfiesCoupledMetricEquation gravitationalCoupling volume metric
          inverse ricci cosmologicalConstant curvature ∧
        SatisfiesMaxwellEquation excitation coordinate := by
  constructor
  · intro hStationary
    constructor
    · intro inverseVelocity
      have h := hStationary inverseVelocity (fun _ => 0)
      simpa [localEinsteinMaxwellBulkEuler, coupledGaugeEulerPairing] using h
    · intro component index
      let variation : Fin 2 → Vector4 :=
        fun current =>
          if current = component then Pi.single index 1 else 0
      have h := hStationary (0 : Matrix4) variation
      have hMetric :
          coupledMetricEulerPairing gravitationalCoupling volume metric inverse
            ricci cosmologicalConstant curvature 0 = 0 := by
        simp [coupledMetricEulerPairing,
          P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D.tensorPairing,
          variationalMaxwellInverseStressPairing,
          localMaxwellMetricVariation, matrixPairing,
          maxwellMetricPairingVelocityAt]
      have hGauge :
          coupledGaugeEulerPairing excitation coordinate variation =
            maxwellEulerCoefficient (excitation component) coordinate index := by
        unfold coupledGaugeEulerPairing
        rw [Finset.sum_eq_single component]
        · rw [Finset.sum_eq_single index]
          · simp [variation, Pi.single_apply]
          · intro other _ hOther
            simp [variation, Pi.single_apply, Ne.symm hOther]
          · simp
        · intro other _ hOther
          simp [variation, hOther]
        · simp
      rw [localEinsteinMaxwellBulkEuler, hMetric, zero_add] at h
      rw [hGauge] at h
      exact h
  · rintro ⟨hMetric, hMaxwell⟩ inverseVelocity gaugeVariation
    rw [localEinsteinMaxwellBulkEuler, hMetric]
    rw [zero_add]
    unfold coupledGaugeEulerPairing
    apply Finset.sum_eq_zero
    intro component _
    apply Finset.sum_eq_zero
    intro index _
    rw [hMaxwell component index, zero_mul]

end

end P0EFTJanusMappingTorusLocalEinsteinMaxwellEulerAssembly4D
end JanusFormal
