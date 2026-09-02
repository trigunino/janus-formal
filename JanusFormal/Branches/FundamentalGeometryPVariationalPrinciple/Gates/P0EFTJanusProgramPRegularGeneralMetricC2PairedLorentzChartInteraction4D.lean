import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-!
# Smooth Candidate-A interaction on the paired regular metric chart

The completed relative root is evaluated in the regular plus frame.  Its
matrix spectral potential is polynomial, hence smooth, and multiplication by
the existing smooth plus-volume field gives the interaction density required
by `GlobalCandidateAActionData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

private def matrix4TraceContinuousLinearMap : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 4) Real Real)

private def matrix4EntryContinuousLinearMap
    (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The complete finite-matrix interaction potential is a smooth polynomial. -/
theorem matrixSpectralPotential_contDiff
    (coefficients : PotentialCoefficients) :
    ContDiff Real ∞ (matrixSpectralPotential coefficients) := by
  have hTrace : ContDiff Real ∞
      (fun root : Matrix4 => Matrix.trace root) := by
    change ContDiff Real ∞ matrix4TraceContinuousLinearMap
    exact matrix4TraceContinuousLinearMap.contDiff
  have hDet : ContDiff Real ∞
      (fun root : Matrix4 => Matrix.det root) := by
    rw [show (fun root : Matrix4 => Matrix.det root) =
        fun root => ∑ σ : Equiv.Perm (Fin 4),
          ((Equiv.Perm.sign σ : ℤ) : Real) * ∏ i, root (σ i) i by
      funext root
      exact Matrix.det_apply' root]
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro i _
    simpa [matrix4EntryContinuousLinearMap] using
      (matrix4EntryContinuousLinearMap (σ i) i).contDiff
  unfold matrixSpectralPotential matrixElementary0 matrixElementary1
    matrixElementary2 matrixElementary3 matrixElementary4
  fun_prop

/-- The action's regular basis evaluates to the stored regular frame. -/
@[simp]
theorem regularMetricBasisAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    regularMetricBasisAt period hPeriod metric point index =
      metric.frame index point := by
  simp [regularMetricBasisAt,
    RegularGeneralLorentzMetric.frame_eq_basisFun]

/-- In the regular basis, the intrinsic chart root has exactly the completed
smooth matrix coefficients constructed by the C² root lift. -/
theorem regularGeneralMetricC2LorentzChartGeometry_rootMatrixAt_regularMetricBasis
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2LorentzChartGeometry period hPeriod metric tensor
        hVariation).rootMatrixAt period hPeriod point
          (regularMetricBasisAt period hPeriod metric point) =
      regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point := by
  unfold GlobalCandidateAGeometry.rootMatrixAt
  rw [regularGeneralMetricC2LorentzChartGeometry_rootAt]
  ext row column
  rw [LinearMap.toMatrix_apply]
  simp [regularMetricBasisAt,
    regularGeneralMetricC2IdentityRootAt_apply,
    Pi.basisFun_apply]

/-- Smooth interaction density of the independently varied metric pair. -/
def regularGeneralMetricC2PairedInteractionDensity
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    -interactionScale *
      (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
        minusBase plusVariation minusVariation hAdmissible).volume point *
      matrixSpectralPotential coefficients
        (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod
          (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
            minusBase plusVariation minusVariation hAdmissible)
          (regularGeneralMetricC2PairedRelativeTensor period hPeriod plusBase
            minusBase plusVariation minusVariation) point)
  contMDiff_toFun := by
    let metric := regularGeneralMetricC2PairedPlusMetric period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible
    let tensor := regularGeneralMetricC2PairedRelativeTensor period hPeriod
      plusBase minusBase plusVariation minusVariation
    have hRoot : RegularGeneralMetricC2IdentityRootAdmissible
        period hPeriod metric tensor :=
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hAdmissible.relative_mem).1
    have hMatrix := regularGeneralMetricC2IdentityRootMatrixAt_contMDiff
      period hPeriod metric tensor hRoot
    have hPotential :=
      (matrixSpectralPotential_contDiff coefficients).contMDiff.comp hMatrix
    exact (contMDiff_const.mul metric.volume.contMDiff_toFun).mul hPotential

/-- Exact `interactionDensity_eq` field required by
`GlobalCandidateAActionData` for the paired chart configuration. -/
theorem regularGeneralMetricC2PairedInteractionDensity_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2PairedInteractionDensity period hPeriod plusBase
        minusBase plusVariation minusVariation hAdmissible interactionScale
        coefficients point =
      (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
        configuration plusBase minusBase plusVariation minusVariation
        hAdmissible potential).geometry.interactionDensityAt period hPeriod
          interactionScale coefficients point
          (regularMetricBasisAt period hPeriod
            (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
              minusBase plusVariation minusVariation hAdmissible).metric
            point) := by
  change
    -interactionScale *
        (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible).volume point *
        matrixSpectralPotential coefficients
          (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod
            (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
              minusBase plusVariation minusVariation hAdmissible)
            (regularGeneralMetricC2PairedRelativeTensor period hPeriod
              plusBase minusBase plusVariation minusVariation) point) = _
  unfold GlobalCandidateAGeometry.interactionDensityAt
  rw [regularGeneralMetricC2PairedLorentzChartConfiguration_geometry]
  rw [regularGeneralMetricC2PairedPlusGravity_metric]
  rw [(regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
    minusBase plusVariation minusVariation hAdmissible).volume_eq point]
  have hFrame :
      (fun index =>
        (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible).frame index
            point) =
        fun index => regularMetricBasisAt period hPeriod
          (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
            minusBase plusVariation minusVariation hAdmissible) point index := by
    funext index
    exact regularMetricBasisAt_apply period hPeriod _ point index |>.symm
  rw [hFrame]
  unfold regularGeneralMetricC2PairedLorentzChartGeometry
  rw [regularGeneralMetricC2LorentzChartGeometry_plusMetric]
  rw [regularGeneralMetricC2LorentzChartGeometry_rootMatrixAt_regularMetricBasis]

/-- Gate marker: the paired chart supplies the exact smooth interaction field
needed by the global Candidate-A action package. -/
theorem regular_general_metric_c2_paired_lorentz_chart_interaction_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ∃ density : SmoothScalarField period hPeriod, ∀ point,
      density point =
        (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
          configuration plusBase minusBase plusVariation minusVariation
          hAdmissible potential).geometry.interactionDensityAt period hPeriod
            interactionScale coefficients point
            (regularMetricBasisAt period hPeriod
              (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
                minusBase plusVariation minusVariation hAdmissible).metric
              point) := by
  exact ⟨regularGeneralMetricC2PairedInteractionDensity period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible
      interactionScale coefficients,
    regularGeneralMetricC2PairedInteractionDensity_eq period hPeriod
      configuration plusBase minusBase plusVariation minusVariation
      hAdmissible potential interactionScale coefficients⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
end JanusFormal
