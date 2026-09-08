import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2RootDerivativePointwiseSylvester4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionRecenterValue4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInteractionSpectralCommutatorReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D

/-! # Finite-frame/regular Sylvester bridge at the paired center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

open scoped Manifold ContDiff Topology Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D
open P0EFTJanusFiniteFrameC2RootDerivativePointwiseSylvester4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusInteractionSpectralCommutatorReduction4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
@[reducible] local instance : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup
@[reducible] local instance : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace
local instance : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

/-- A smooth metric variation encoded in any redundant finite frame decodes
to its intrinsic four-dimensional matrix in the regular metric basis. -/
theorem finiteFrameDecodedSmoothLiftMatrixAt_regularMetricBasis
    (frame : SmoothD8Frame period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    LinearMap.toMatrix
        (regularMetricBasisAt period hPeriod metric point)
        (regularMetricBasisAt period hPeriod metric point)
        (finiteFrameMatrixDecodeAt period hPeriod frame metric.metric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame metric.metric tensor) point)).toLinearMap =
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor) point := by
  have hValue :
      c2FiniteMatrixValueAt period hPeriod frame.count
          (smoothGeneralMetricRelativeEndomorphismToC2
            period hPeriod frame metric.metric tensor) point =
        finiteFrameEndomorphismMatrixAt period hPeriod frame metric.metric point
          (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point) := by
    ext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            frame metric.metric tensor row column)) point = _
    rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    exact congrFun (congrFun
      (smoothGeneralMetricRelativeEndomorphismMatrix_apply
        period hPeriod frame metric.metric tensor point) row) column
  rw [hValue, finiteFrameMatrixDecodeAt_encode,
    regularGeneralMetricC2VariationMatrix_valueAt]
  let basis := regularMetricBasisAt period hPeriod metric point
  ext row column
  rw [LinearMap.toMatrix_apply, finiteFrameEndomorphismMatrixAt_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  change basis.repr
      (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point
        (basis column)) row =
    (metric.frameEquiv point).symm
      (raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point
        (metric.frame column point)) row
  rw [show basis column = metric.frame column point from
    regularMetricBasisAt_apply period hPeriod metric point column]
  rfl

/-- The decoded finite Candidate-A root is the regular paired-relative root at
the center, in the regular plus-metric basis. -/
theorem finiteFrameCandidateRootMatrix_eq_regularPairedRoot_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod
      plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point
        (regularMetricBasisAt period hPeriod plusBase point)
        (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame) =
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod
          plusBase minusBase 0) point := by
  dsimp only
  rw [finiteFrameC2CornerMatrixAtCLM_candidateRoot]
  change
    (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart).rootMatrixAt
        period hPeriod point
          (regularMetricBasisAt period hPeriod plusBase point) = _
  rw [regularGeneralMetricC2LorentzChartGeometry_rootMatrixAt_regularMetricBasis]
  unfold regularGeneralMetricC2PairedRelativeRoot
  rw [pairedInteractionRelativeMatrix_zero]
  rfl

/-- The concrete regular Lorentz-chart geometry supplies its intrinsic
Sylvester bijectivity directly from the completed matrix root branch. -/
theorem regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod
          metric tensor hChart) point) := by
  intro point
  apply intrinsicCandidateASylvesterAt_bijective_of_matrix
    period hPeriod
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod
        metric tensor hChart) point
      (regularMetricBasisAt period hPeriod metric point)
  rw [regularGeneralMetricC2LorentzChartGeometry_rootMatrixAt_regularMetricBasis,
    candidateAMatrixSylvester_eq_canonical]
  exact regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hChart).1 point

/-- Intrinsic pointwise matrices turn the product of two completed corner
elements into ordinary four-dimensional matrix multiplication. -/
theorem finiteFrameC2CornerProductMatrixAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (first second : C2FiniteFrameCorner
      period hPeriod frame geometry.plusMetric)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
              frame.count first.1 second.1) point)).toLinearMap =
      finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis first *
        finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis second := by
  rw [c2FiniteMatrixValueAt_product,
    finiteFrameMatrixDecodeAt_mul_of_corner period hPeriod frame
      geometry.plusMetric point _ _
        (c2FiniteFrameCorner_valueAt period hPeriod frame
          geometry.plusMetric first point)
        (c2FiniteFrameCorner_valueAt period hPeriod frame
          geometry.plusMetric second point)]
  simp only [finiteFrameC2CornerMatrixAtCLM_apply]
  change LinearMap.toMatrix basis basis
      ((finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count first.1 point)).toLinearMap.comp
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count second.1 point)).toLinearMap) = _
  rw [LinearMap.toMatrix_comp basis basis basis
    (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
      (c2FiniteMatrixValueAt period hPeriod frame.count first.1 point)).toLinearMap
    (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
      (c2FiniteMatrixValueAt period hPeriod frame.count second.1 point)).toLinearMap]

/-- The decoded matrix of the affine target `-first * second + third` is the
same affine expression in intrinsic four-dimensional matrices. -/
theorem finiteFrameC2CornerNegProductAddMatrixAt
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (first second third : C2FiniteFrameCorner
      period hPeriod frame geometry.plusMetric)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
                frame.count first.1 second.1 + third.1) point)).toLinearMap =
      -(finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis first *
        finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis second) +
        finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis third := by
  let decodedValue :
      C2FiniteMatrix period hPeriod frame.count →L[Real] Matrix4 :=
    (finiteFrameDecodeMatrixAtCLM
      period hPeriod frame geometry.plusMetric point basis).comp
        (finiteFrameC2MatrixValueAtCLM period hPeriod frame point)
  change decodedValue
      (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
          frame.count first.1 second.1 + third.1) = _
  rw [map_add, map_neg]
  have hProduct := finiteFrameC2CornerProductMatrixAt
    period hPeriod geometry frame first second point basis
  change -(LinearMap.toMatrix basis basis
      (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        (c2FiniteMatrixValueAt period hPeriod frame.count
          (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
            frame.count first.1 second.1) point)).toLinearMap) +
      finiteFrameC2CornerMatrixAtCLM
        period hPeriod geometry frame point basis third = _
  rw [hProduct]

/-- On genuine smooth metric lifts, the finite target derivative is the
ordinary affine matrix expression `-A₊ R₀² + A₋`. -/
theorem pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_smooth_lifts
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        frame point (regularMetricBasisAt period hPeriod plusBase point)
        (smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric minusVariation) =
      -(c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix
            period hPeriod plusBase plusVariation) point *
        (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point *
          c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point)) +
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix
            period hPeriod plusBase minusVariation) point := by
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let plusLift := smoothToGeneralMetricRelativeC2Core
    period hPeriod frame plusBase.metric plusVariation
  let minusLift := smoothToGeneralMetricRelativeC2Core
    period hPeriod frame plusBase.metric minusVariation
  let plusCorner : C2FiniteFrameCorner period hPeriod frame geometry.plusMetric :=
    ⟨plusLift.1, by
      simpa [geometry] using generalMetricRelativeC2Core_mem_corner
        period hPeriod frame plusBase.metric plusLift⟩
  let minusCorner : C2FiniteFrameCorner period hPeriod frame geometry.plusMetric :=
    ⟨minusLift.1, by
      simpa [geometry] using generalMetricRelativeC2Core_mem_corner
        period hPeriod frame plusBase.metric minusLift⟩
  let rootCorner := c2GlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  let rootSquare := c2FiniteFrameCornerSquare
    period hPeriod frame geometry.plusMetric rootCorner
  let basis := regularMetricBasisAt period hPeriod plusBase point
  have hPlus :
      finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis plusCorner =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix
            period hPeriod plusBase plusVariation) point := by
    rw [finiteFrameC2CornerMatrixAtCLM_apply]
    change LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame plusBase.metric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame plusBase.metric plusVariation) point)).toLinearMap = _
    exact finiteFrameDecodedSmoothLiftMatrixAt_regularMetricBasis
      period hPeriod frame plusBase plusVariation point
  have hMinus :
      finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis minusCorner =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix
            period hPeriod plusBase minusVariation) point := by
    rw [finiteFrameC2CornerMatrixAtCLM_apply]
    change LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame plusBase.metric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (smoothGeneralMetricRelativeEndomorphismToC2
              period hPeriod frame plusBase.metric minusVariation) point)).toLinearMap = _
    exact finiteFrameDecodedSmoothLiftMatrixAt_regularMetricBasis
      period hPeriod frame plusBase minusVariation point
  have hRoot :
      finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis rootCorner =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point := by
    simpa [geometry, rootCorner, basis] using
      finiteFrameCandidateRootMatrix_eq_regularPairedRoot_zero
        period hPeriod plusBase minusBase hChart frame point
  have hRootSquare :
      finiteFrameC2CornerMatrixAtCLM
          period hPeriod geometry frame point basis rootSquare =
        c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point *
          c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point := by
    rw [finiteFrameC2CornerMatrixAtCLM_apply]
    change LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
              frame.count rootCorner.1 rootCorner.1) point)).toLinearMap = _
    rw [finiteFrameC2CornerProductMatrixAt
      period hPeriod geometry frame rootCorner rootCorner point basis, hRoot]
  rw [pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_apply]
  change LinearMap.toMatrix basis basis
      (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
        (c2FiniteMatrixValueAt period hPeriod frame.count
          (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
              frame.count plusCorner.1 rootSquare.1 + minusCorner.1) point)).toLinearMap = _
  rw [finiteFrameC2CornerNegProductAddMatrixAt
    period hPeriod geometry frame plusCorner rootSquare minusCorner point basis,
    hPlus, hRootSquare, hMinus]

/-- At the paired center, the regular selected root squares to the identity
plus the base relative matrix. -/
theorem regularPairedRelativeRoot_zero_square
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point *
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point =
      1 + c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor)) point := by
  have hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
      period hPeriod plusBase hChart).1
  have hC2 := c2IdentityRootBranch_square period hPeriod hRoot
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hC2
  unfold regularGeneralMetricC2PairedRelativeRoot
  rw [pairedInteractionRelativeMatrix_zero]
  simpa only [c2FiniteMatrixSquare, c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_identity] using hValue

/-- The finite left-relative target and the symmetrically recentered target
differ by the exact relative-matrix commutator generated by `A / 2`. -/
theorem matrixFiniteTarget_eq_centerTarget_add_commutator
    (plusVelocity minusVelocity relative : Matrix4) :
    -plusVelocity * (1 + relative) + minusVelocity =
      (relative * (-((1 / 2 : Real) • plusVelocity)) +
          (minusVelocity - plusVelocity) +
        (-((1 / 2 : Real) • plusVelocity)) * relative) +
      (relative * ((1 / 2 : Real) • plusVelocity) -
        ((1 / 2 : Real) • plusVelocity) * relative) := by
  let half := (1 / 2 : Real) • plusVelocity
  have hHalf : half + half = plusVelocity := by
    dsimp [half]
    rw [← add_smul]
    norm_num
  have hHalfRight :
      half * relative + half * relative = plusVelocity * relative := by
    rw [← add_mul, hHalf]
  change -plusVelocity * (1 + relative) + minusVelocity =
    (relative * (-half) + (minusVelocity - plusVelocity) +
      (-half) * relative) +
    (relative * half - half * relative)
  simp only [mul_neg, neg_mul]
  calc
    -(plusVelocity * (1 + relative)) + minusVelocity =
        minusVelocity - plusVelocity - plusVelocity * relative := by
      noncomm_ring
    _ = minusVelocity - plusVelocity -
        (half * relative + half * relative) := by rw [hHalfRight]
    _ = (- (relative * half) + (minusVelocity - plusVelocity) +
          -(half * relative)) +
        (relative * half - half * relative) := by abel

/-- On the common smooth core, the finite target derivative is the regular
centered target plus the explicit relative commutator generated by `A₊ / 2`. -/
theorem pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_smooth_lifts_commutator
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let plusVelocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix
        period hPeriod plusBase plusVariation) point
    let relative := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor)) point
    pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        frame point (regularMetricBasisAt period hPeriod plusBase point)
        (smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric minusVariation) =
      c2FiniteMatrixValueAt period hPeriod 4
          (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
            (regularGeneralMetricC2VariationMatrix
              period hPeriod plusBase plusVariation)
            (regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase minusVariation -
              regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase plusVariation)) point +
        (relative * ((1 / 2 : Real) • plusVelocity) -
          ((1 / 2 : Real) • plusVelocity) * relative) := by
  dsimp only
  rw [pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_smooth_lifts
      period hPeriod plusBase minusBase hChart frame plusVariation minusVariation point,
    regularPairedRelativeRoot_zero_square
      period hPeriod plusBase minusBase hChart point]
  have hCenter :
      c2FiniteMatrixValueAt period hPeriod 4
          (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
            (regularGeneralMetricC2VariationMatrix
              period hPeriod plusBase plusVariation)
            (regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase minusVariation -
              regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase plusVariation)) point =
        c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor)) point *
            (-((1 / 2 : Real) •
              c2FiniteMatrixValueAt period hPeriod 4
                (regularGeneralMetricC2VariationMatrix
                  period hPeriod plusBase plusVariation) point)) +
          (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase minusVariation) point -
            c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase plusVariation) point) +
          (-((1 / 2 : Real) •
              c2FiniteMatrixValueAt period hPeriod 4
                (regularGeneralMetricC2VariationMatrix
                  period hPeriod plusBase plusVariation) point)) *
            c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
                (minusBase.metric.tensor - plusBase.metric.tensor)) point := by
    unfold pairedInteractionMetricCenterVelocity
    simp only [c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product]
    rfl
  rw [hCenter]
  simpa only [neg_mul] using
    matrixFiniteTarget_eq_centerTarget_add_commutator
      (c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix
          period hPeriod plusBase plusVariation) point)
      (c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix
          period hPeriod plusBase minusVariation) point)
      (c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor)) point)

/-- Point evaluation transports the regular paired root-derivative Sylvester
equation to ordinary four-dimensional matrices. -/
theorem regularPairedRelativeRootDerivative_zero_sylvester_pointwise
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
    (direction : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod) :
    let root := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase 0) point
    let velocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
        plusBase minusBase 0 hZero direction) point
    root * velocity + velocity * root =
      c2FiniteMatrixValueAt period hPeriod 4
        (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
          direction.2.1 direction.2.2) point := by
  dsimp only
  have hEquation :=
    regularGeneralMetricC2PairedRelativeRootDerivative_zero_sylvester
      period hPeriod plusBase minusBase hZero direction
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hEquation
  simpa only [c2FiniteMatrixSylvester, add_apply,
    ContinuousLinearMap.flip_apply, c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_product] using hValue

/-- The finite and regular root velocities have Sylvester images differing
exactly by the relative commutator on every common smooth metric lift. -/
theorem pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester_smooth_lifts_commutator
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hFiniteRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart) point))
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let basis := regularMetricBasisAt period hPeriod plusBase point
    let finiteDirection :=
      (smoothToGeneralMetricRelativeC2Core
          period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core
          period hPeriod frame plusBase.metric minusVariation)
    let regularDirection := pairedInteractionSmoothCore period hPeriod
      plusBase minusBase plusVariation minusVariation
    let root := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase 0) point
    let finiteVelocity := pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
      period hPeriod geometry frame hFiniteRegular point basis finiteDirection
    let regularVelocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
        plusBase minusBase 0 hZero regularDirection) point
    let plusVelocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix
        period hPeriod plusBase plusVariation) point
    let relative := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor)) point
    root * finiteVelocity + finiteVelocity * root =
      (root * regularVelocity + regularVelocity * root) +
        (relative * ((1 / 2 : Real) • plusVelocity) -
          ((1 / 2 : Real) • plusVelocity) * relative) := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let basis := regularMetricBasisAt period hPeriod plusBase point
  let finiteDirection :=
    (smoothToGeneralMetricRelativeC2Core
        period hPeriod frame plusBase.metric plusVariation,
      smoothToGeneralMetricRelativeC2Core
        period hPeriod frame plusBase.metric minusVariation)
  let regularDirection := pairedInteractionSmoothCore period hPeriod
    plusBase minusBase plusVariation minusVariation
  have hCandidateRoot := finiteFrameC2CornerMatrixAtCLM_candidateRoot
    period hPeriod geometry frame point basis
  have hRootBridge := finiteFrameCandidateRootMatrix_eq_regularPairedRoot_zero
    period hPeriod plusBase minusBase hChart frame point
  have hGeometryRoot :
      LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point := by
    exact hCandidateRoot.symm.trans (by
      simpa [geometry, basis] using hRootBridge)
  have hFinite :=
    pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester
      period hPeriod geometry frame hFiniteRegular finiteDirection point basis
  rw [hGeometryRoot] at hFinite
  have hTarget :=
    pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_smooth_lifts_commutator
      period hPeriod plusBase minusBase hChart frame plusVariation minusVariation point
  have hRegular := regularPairedRelativeRootDerivative_zero_sylvester_pointwise
    period hPeriod plusBase minusBase hZero regularDirection point
  have hRegular' :
      c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point *
          c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
              plusBase minusBase 0 hZero regularDirection) point +
        c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
              plusBase minusBase 0 hZero regularDirection) point *
          c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase 0) point =
      c2FiniteMatrixValueAt period hPeriod 4
        (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
          (regularGeneralMetricC2VariationMatrix
            period hPeriod plusBase plusVariation)
          (regularGeneralMetricC2VariationMatrix
              period hPeriod plusBase minusVariation -
            regularGeneralMetricC2VariationMatrix
              period hPeriod plusBase plusVariation)) point := by
    simpa [regularDirection, pairedInteractionSmoothCore] using hRegular
  calc
    _ = pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero period hPeriod
        geometry frame point basis finiteDirection := hFinite
    _ = c2FiniteMatrixValueAt period hPeriod 4
          (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
            (regularGeneralMetricC2VariationMatrix
              period hPeriod plusBase plusVariation)
            (regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase minusVariation -
              regularGeneralMetricC2VariationMatrix
                period hPeriod plusBase plusVariation)) point +
        (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
                (minusBase.metric.tensor - plusBase.metric.tensor)) point *
            ((1 / 2 : Real) •
              c2FiniteMatrixValueAt period hPeriod 4
                (regularGeneralMetricC2VariationMatrix
                  period hPeriod plusBase plusVariation) point) -
          ((1 / 2 : Real) •
              c2FiniteMatrixValueAt period hPeriod 4
                (regularGeneralMetricC2VariationMatrix
                  period hPeriod plusBase plusVariation) point) *
            c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
                (minusBase.metric.tensor - plusBase.metric.tensor)) point) := by
      simpa [geometry, basis, finiteDirection] using hTarget
    _ = _ := by rw [← hRegular']

/-- The commutator discrepancy between the finite and regular root velocities
is annihilated by every spectral-potential differential. -/
theorem pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_spectral_smooth_lifts
    (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hFiniteRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart) point))
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let basis := regularMetricBasisAt period hPeriod plusBase point
    let finiteDirection :=
      (smoothToGeneralMetricRelativeC2Core
          period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core
          period hPeriod frame plusBase.metric minusVariation)
    let regularDirection := pairedInteractionSmoothCore period hPeriod
      plusBase minusBase plusVariation minusVariation
    let root := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase 0) point
    let finiteVelocity := pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
      period hPeriod geometry frame hFiniteRegular point basis finiteDirection
    let regularVelocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
        plusBase minusBase 0 hZero regularDirection) point
    matrixSpectralPotentialDerivative coefficients root finiteVelocity =
      matrixSpectralPotentialDerivative coefficients root regularVelocity := by
  dsimp only
  apply matrixSpectralPotentialDerivative_eq_of_relative_commutator
    coefficients
    (c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase 0) point)
    (c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor)) point)
    (pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero period hPeriod
      (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      frame hFiniteRegular point
        (regularMetricBasisAt period hPeriod plusBase point)
        (smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric plusVariation,
          smoothToGeneralMetricRelativeC2Core
            period hPeriod frame plusBase.metric minusVariation))
    (c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
        plusBase minusBase 0 hZero
          (pairedInteractionSmoothCore period hPeriod plusBase minusBase
            plusVariation minusVariation)) point)
    ((1 / 2 : Real) • c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix
        period hPeriod plusBase plusVariation) point)
  · exact regularPairedRelativeRoot_zero_square
      period hPeriod plusBase minusBase hChart point
  · have hRootValue :
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point =
      regularGeneralMetricC2IdentityRootMatrixAt period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) point := by
      unfold regularGeneralMetricC2PairedRelativeRoot
      rw [pairedInteractionRelativeMatrix_zero]
      rfl
    rw [hRootValue]
    exact (regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective
      period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor)
          (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
            period hPeriod plusBase hChart).1 point).1
  · have hBridge :=
      pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester_smooth_lifts_commutator
        period hPeriod plusBase minusBase hChart frame hFiniteRegular hZero
          plusVariation minusVariation point
    dsimp only at hBridge
    exact hBridge

/-- Final pointwise bridge: the actual finite-frame C² spectral covector on
a smooth lift equals the regular paired-root spectral derivative. -/
theorem pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_smooth_lifts_regular
    (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hFiniteRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod
        (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart) point))
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
          frame hFiniteRegular coefficients
          (smoothToGeneralMetricRelativeC2Core
              period hPeriod frame plusBase.metric plusVariation,
            smoothToGeneralMetricRelativeC2Core
              period hPeriod frame plusBase.metric minusVariation)) point =
      matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
            plusBase minusBase 0 hZero
              (pairedInteractionSmoothCore period hPeriod plusBase minusBase
                plusVariation minusVariation)) point) := by
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let basis := regularMetricBasisAt period hPeriod plusBase point
  let finiteDirection :=
    (smoothToGeneralMetricRelativeC2Core
        period hPeriod frame plusBase.metric plusVariation,
      smoothToGeneralMetricRelativeC2Core
        period hPeriod frame plusBase.metric minusVariation)
  have hValue := pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_valueAt
    period hPeriod geometry frame hFiniteRegular coefficients finiteDirection point basis
  have hCandidateRoot := finiteFrameC2CornerMatrixAtCLM_candidateRoot
    period hPeriod geometry frame point basis
  have hRootBridge := finiteFrameCandidateRootMatrix_eq_regularPairedRoot_zero
    period hPeriod plusBase minusBase hChart frame point
  have hGeometryRoot :
      LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point := by
    exact hCandidateRoot.symm.trans (by
      simpa [geometry, basis] using hRootBridge)
  rw [hGeometryRoot] at hValue
  have hSpectral :=
    pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_spectral_smooth_lifts
      period hPeriod coefficients plusBase minusBase hChart frame hFiniteRegular hZero
        plusVariation minusVariation point
  dsimp only at hSpectral
  exact hValue.trans hSpectral

/-- Canonical chart version of the final bridge: no separate finite Sylvester
regularity hypothesis is required. -/
theorem pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_smooth_lifts_regular_of_chart
    (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
        period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotentialDerivativeAtZero period hPeriod
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
          frame hFiniteRegular coefficients
          (smoothToGeneralMetricRelativeC2Core
              period hPeriod frame plusBase.metric plusVariation,
            smoothToGeneralMetricRelativeC2Core
              period hPeriod frame plusBase.metric minusVariation)) point =
      matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase 0) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
            plusBase minusBase 0 hZero
              (pairedInteractionSmoothCore period hPeriod plusBase minusBase
                plusVariation minusVariation)) point) := by
  dsimp only
  exact pairedFiniteFrameC2SpectralPotentialDerivativeAtZero_smooth_lifts_regular
    period hPeriod coefficients plusBase minusBase hChart frame
      (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
        period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      hZero plusVariation minusVariation point

end
end P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
end JanusFormal
