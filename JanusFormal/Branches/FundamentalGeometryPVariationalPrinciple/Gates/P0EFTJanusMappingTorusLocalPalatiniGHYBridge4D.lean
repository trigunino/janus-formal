import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEHGHYCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D

/-!
# Bridge from the local Palatini vector to the Gaussian-normal GHY flux

The connection variation used in the Gaussian-normal calculation is inserted
into the general metric-compatible Palatini jet.  Its normal vector component
is proved equal to the previously derived Gaussian Palatini trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev BoundaryMatrix3 :=
  P0EFTJanusGaussianNormalEHGHYCancellation.Matrix3

local instance localRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  inferInstance

local instance localRealNormedSpace : NormedSpace ℝ ℝ :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup ℝ :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module ℝ ℝ :=
  localRealNormedSpace.toModule

theorem inducedInverse_symmetric (data : NonNullBoundaryPointData) :
    data.inducedInverse.transpose = data.inducedInverse := by
  have hRightTranspose :
      data.inducedMetric * data.inducedInverse.transpose = 1 := by
    have hTranspose :=
      congrArg Matrix.transpose data.inverseWitness.inverse_mul
    simpa [Matrix.transpose_mul, data.inducedMetricSymmetric] using hTranspose
  calc
    data.inducedInverse.transpose =
        1 * data.inducedInverse.transpose := by rw [one_mul]
    _ = (data.inducedInverse * data.inducedMetric) *
          data.inducedInverse.transpose := by
            rw [data.inverseWitness.inverse_mul]
    _ = data.inducedInverse *
          (data.inducedMetric * data.inducedInverse.transpose) := by
            rw [Matrix.mul_assoc]
    _ = data.inducedInverse * 1 := by rw [hRightTranspose]
    _ = data.inducedInverse := by rw [mul_one]

theorem gaussianInverse_symmetric (data : NonNullBoundaryPointData) :
    (gaussianInverse data.orientationSign data.inducedInverse).transpose =
      gaussianInverse data.orientationSign data.inducedInverse := by
  have hInverse := inducedInverse_symmetric data
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [Matrix.transpose_apply] at hInverse ⊢
  all_goals
    first
    | exact congrFun (congrFun hInverse _ ) _
    | rfl

theorem normalMetricVariationJet_lower_symmetric
    (normalJet : BoundaryMatrix3)
    (hNormalJet : normalJet.transpose = normalJet)
    (derivative first second : Index4) :
    normalMetricVariationJet normalJet derivative first second =
      normalMetricVariationJet normalJet derivative second first := by
  refine Fin.cases ?_ (fun _ => ?_) derivative
  · refine Fin.cases ?_ (fun tangentFirst => ?_) first
    · fin_cases second <;> rfl
    · refine Fin.cases ?_ (fun tangentSecond => ?_) second
      · rfl
      · have hEntry :=
          congrFun (congrFun hNormalJet tangentFirst) tangentSecond
        simpa [normalMetricVariationJet, Matrix.transpose_apply] using
          hEntry.symm
  · rfl

theorem linearizedChristoffel_lower_symmetric
    (epsilon : ℝ) (inverse normalJet : BoundaryMatrix3)
    (hNormalJet : normalJet.transpose = normalJet)
    (upper first second : Index4) :
    linearizedChristoffel epsilon inverse normalJet upper first second =
      linearizedChristoffel epsilon inverse normalJet upper second first := by
  unfold linearizedChristoffel
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro contracted _
  rw [normalMetricVariationJet_lower_symmetric normalJet hNormalJet
    contracted first second]
  ring

/-- The Gaussian linearized Christoffel tensor regarded as a general
metric-compatible Palatini jet at the boundary point.  Zero base connection
is a valid pointwise normal-coordinate representative. -/
def gaussianMetricCompatiblePalatiniJet
    (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    MetricCompatiblePalatiniJet4 where
  connectionJet :=
    { connection := fun _ _ _ => 0
      variation := linearizedChristoffel data.orientationSign
        data.inducedInverse jet.normalMetricVariation
      partialVariation := fun _ _ _ _ => 0
      connection_torsionFree := by intros; rfl }
  inverse := gaussianInverse data.orientationSign data.inducedInverse
  partialInverse := fun _ _ _ => 0
  inverse_symmetric := by
    intro first second
    have hSymmetric := gaussianInverse_symmetric data
    exact congrFun (congrFun hSymmetric second) first
  inverse_metric_compatible := by
    intros
    simp

/-- The normal component of the general Palatini vector is exactly the
Gaussian-normal Palatini vector used by the GHY calculation. -/
theorem palatiniVector_normal_eq_gaussian
    (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    palatiniVector (gaussianMetricCompatiblePalatiniJet data jet)
        normalIndex =
      palatiniNormalVector data.orientationSign data.inducedInverse
        jet.normalMetricVariation := by
  unfold palatiniVector palatiniNormalVector palatiniFirstTrace
    palatiniSecondTrace
  dsimp only [gaussianMetricCompatiblePalatiniJet]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [linearizedChristoffel_lower_symmetric _ _ _
      jet.normalMetricVariationSymmetric]
  · apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro contracted _
    have hInverse := gaussianInverse_symmetric data
    have hInverseEntry :=
      congrFun (congrFun hInverse normalIndex) first
    rw [linearizedChristoffel_lower_symmetric _ _ _
      jet.normalMetricVariationSymmetric]
    change
      gaussianInverse data.orientationSign data.inducedInverse first
            normalIndex *
          linearizedChristoffel data.orientationSign data.inducedInverse
            jet.normalMetricVariation contracted first contracted =
        gaussianInverse data.orientationSign data.inducedInverse normalIndex
            first *
          linearizedChristoffel data.orientationSign data.inducedInverse
            jet.normalMetricVariation contracted first contracted
    rw [show
      gaussianInverse data.orientationSign data.inducedInverse first
          normalIndex =
        gaussianInverse data.orientationSign data.inducedInverse normalIndex
          first by
      simpa [Matrix.transpose_apply] using hInverseEntry]

/-- Consequently the EH boundary density uses the normal component of the
same Palatini vector as the local bulk variation. -/
theorem einsteinHilbertDirichletBoundaryFlux_eq_localPalatiniVector
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    einsteinHilbertDirichletBoundaryFlux einsteinScale data jet =
      (einsteinScale / 2) *
        Real.sqrt |Matrix.det data.inducedMetric| *
          (data.orientationSign * data.orientationSign *
            palatiniVector (gaussianMetricCompatiblePalatiniJet data jet)
              normalIndex) := by
  unfold einsteinHilbertDirichletBoundaryFlux
    stokesContractedPalatini
  rw [palatiniVector_normal_eq_gaussian]

end

end P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D
end JanusFormal
