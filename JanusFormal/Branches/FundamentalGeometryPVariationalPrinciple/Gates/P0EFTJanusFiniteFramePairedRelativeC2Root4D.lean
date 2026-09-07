import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameLocalRootExactCenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2OpenDomain4D

/-! # Paired relative C² metric input to the stored finite-frame root

Both variations are raised with the same fixed plus metric. The actual
relative matrix is obtained using the existing C² inverse and the redundant
frame projector. Its difference from the stored root square supplies the
constructed local inverse branch. The domain here concerns this relative
algebra and the root branch; Lorentzian metric reconstruction is separate.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedRelativeC2Root4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameLocalRootExactCenter4D

private theorem projector_inverse_product
    {E : Type*} (product : E → E → E) (unit projector extended inverse numerator : E)
    (hAssoc : ∀ first second third,
      product (product first second) third = product first (product second third))
    (hUnit : ∀ value, product unit value = value)
    (hCommute : product extended projector = product projector extended)
    (hInverse : product extended inverse = unit)
    (hLeft : product projector numerator = numerator)
    (hRight : product numerator projector = numerator) :
    product extended (product projector (product (product inverse numerator) projector)) =
      numerator := by
  rw [← hAssoc, hCommute, hAssoc, ← hAssoc extended,
    ← hAssoc extended inverse, hInverse, hUnit, hRight, hLeft]

private theorem relative_affine_equation
    {V W : Type*} [AddCommGroup V] [Module Real V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W] [ContinuousAdd W]
    (base varied : V ≃L[Real] W) (difference right : V →L[Real] W)
    (hVaried : (varied : V →L[Real] W) = (base : V →L[Real] W) + difference) :
    (varied.symm : W →L[Real] V).comp right +
      ((base.symm : W →L[Real] V).comp difference).comp
        ((varied.symm : W →L[Real] V).comp right) =
      (base.symm : W →L[Real] V).comp right := by
  apply ContinuousLinearMap.ext
  intro vector
  apply base.injective
  change base (varied.symm (right vector) +
    base.symm (difference (varied.symm (right vector)))) = base (base.symm (right vector))
  rw [map_add, base.apply_symm_apply, base.apply_symm_apply]
  have hValue := congrArg (fun operator : V →L[Real] W =>
    operator (varied.symm (right vector))) hVaried
  simpa only [ContinuousLinearEquiv.coe_coe, add_apply,
    ContinuousLinearEquiv.apply_symm_apply] using hValue.symm

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance c2ScalarNormedSpace : NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance
local instance c2ScalarCompleteSpace : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance cornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule period hPeriod frame metric).normedAddCommGroup
local instance cornerNormedSpace
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (C2FiniteFrameCorner period hPeriod frame metric) := inferInstance
local instance relativeNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance relativeNormedSpace
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance

/-- Two independently variable metrics encoded in one fixed intrinsic corner. -/
abbrev PairedFiniteFrameMetricC2Core
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :=
  GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric ×
    GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric

def finiteFrameC2CornerProjection
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FiniteMatrix period hPeriod frame.count →L[Real]
      C2FiniteFrameCorner period hPeriod frame metric :=
  (c2FiniteFrameCornerProjection period hPeriod frame metric).codRestrict
    (c2FiniteFrameCornerSubmodule period hPeriod frame metric)
    (c2FiniteFrameCornerProjection_mem period hPeriod frame metric)

/-- The constant term really is the encoding of the given metric pair. -/
theorem finiteFrameStoredRootSquare_eq_relative
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
      (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)).1 =
      smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame
        geometry.plusMetric geometry.minusMetric.tensor := by
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients period hPeriod geometry frame))
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothGlobalCandidateAFiniteFrameRootCoefficients period hPeriod geometry frame)) = _
  rw [c2FiniteMatrixProduct_smooth]
  apply congrArg (smoothFiniteMatrixToC2 period hPeriod frame.count)
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hEntry := congrFun (congrFun
    (globalCandidateAFiniteFrameRootMatrix_sq period hPeriod geometry frame point) row) column
  have hRelative : relativeEndomorphismAt period hPeriod
      geometry.plusMetric geometry.minusMetric point =
      raisedGeneralMetricTensorAt period hPeriod geometry.plusMetric
        geometry.minusMetric.tensor point := by
    unfold relativeEndomorphismAt raisedGeneralMetricTensorAt
    rw [← geometry.minusMetric.musical_eq_tensor point]
    rfl
  rw [hRelative] at hEntry
  simp only [smoothFiniteMatrixProduct, smoothGlobalCandidateAFiniteFrameRootCoefficients,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply]
  simpa only [Matrix.mul_apply, globalCandidateAFiniteFrameRootMatrix_apply,
    globalCandidateAFiniteFrameRootCoefficient_apply,
    finiteFrameEndomorphismMatrixAt_apply] using hEntry

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)

local notation "Model" => PairedFiniteFrameMetricC2Core period hPeriod geometry frame
local notation "Corner" => C2FiniteFrameCorner period hPeriod frame geometry.plusMetric
local notation "root" => c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame
local notation "square" => c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric

private theorem finiteFrameEndomorphismMatrixAt_add
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point →L[Real] TangentFiber period hPeriod point) :
    finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point (first + second) =
      finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point first +
        finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point second := by
  ext row column
  exact (generalMetricFiniteFrameCoefficientAt period hPeriod frame geometry.plusMetric point row).map_add
    (first (frame.vectorAt point column)) (second (frame.vectorAt point column))

/-- The genuine varied relative endomorphism, encoded with the fixed reference coefficients. -/
def smoothPairedFiniteFrameRelativeMatrix
    (variedPlus variedMinus : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothFiniteMatrix period hPeriod frame.count :=
  fun row column => generalMetricFiniteFrameCoefficient period hPeriod frame geometry.plusMetric
    (generalMetricRaisedFrameVector period hPeriod frame variedPlus variedMinus.tensor column) row

theorem smoothPairedFiniteFrameRelativeMatrix_entry_apply
    (variedPlus variedMinus : SmoothGeneralLorentzMetric period hPeriod)
    (row column : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus
        row column point =
      finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point
        (raisedGeneralMetricTensorAt period hPeriod variedPlus variedMinus.tensor point) row column :=
  rfl

private theorem smoothPairedFiniteFrameRelativeMatrix_equation
    (plusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedPlus variedMinus : SmoothGeneralLorentzMetric period hPeriod)
    (hPlus : variedPlus.tensor = geometry.plusMetric.tensor + plusVariation) :
    smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus +
      smoothFiniteMatrixProduct period hPeriod frame.count
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame geometry.plusMetric
          plusVariation)
        (smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus) =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame geometry.plusMetric
        variedMinus.tensor := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hPlusAt : (variedPlus.musical point : _ →L[Real] _) =
      (geometry.plusMetric.musical point : _ →L[Real] _) + plusVariation.tensor point := by
    rw [variedPlus.musical_eq_tensor point, geometry.plusMetric.musical_eq_tensor point, hPlus]
    rfl
  have hIntrinsic := relative_affine_equation
    (V := TangentFiber period hPeriod point)
    (W := TangentFiber period hPeriod point →L[Real] Real)
    (geometry.plusMetric.musical point)
    (variedPlus.musical point) (plusVariation.tensor point) (variedMinus.tensor.tensor point) hPlusAt
  have hMatrix := congrArg
    (finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point) hIntrinsic
  rw [finiteFrameEndomorphismMatrixAt_add period hPeriod geometry frame point,
    finiteFrameEndomorphismMatrixAt_comp] at hMatrix
  have hEntry := congrFun (congrFun hMatrix row) column
  change smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus
      row column point +
    smoothFiniteMatrixProduct period hPeriod frame.count
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame geometry.plusMetric
        plusVariation)
      (smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus)
      row column point = _
  simp only [smoothFiniteMatrixProduct,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, smoothPairedFiniteFrameRelativeMatrix_entry_apply,
    smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply]
  simpa only [Matrix.add_apply, Matrix.mul_apply, raisedGeneralMetricTensorAt] using hEntry

def pairedFiniteFrameRelativeC2Domain : Set Model :=
  Prod.fst ⁻¹' generalMetricRelativeC2OpenDomain period hPeriod frame geometry.plusMetric

theorem pairedFiniteFrameRelativeC2Domain_isOpen :
    IsOpen (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame geometry.plusMetric).preimage
    continuous_fst

theorem zero_mem_pairedFiniteFrameRelativeC2Domain :
    (0 : Model) ∈ pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame :=
  zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame geometry.plusMetric

/-- `P (I + A₊)⁻¹ (R₀ + A₋) P`, with both `A` in the same reference corner. -/
def pairedFiniteFrameRelativeC2Target (variation : Model) : Corner :=
  finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2InverseMatrix period hPeriod frame geometry.plusMetric variation.1)
      ((square root).1 + variation.2.1))

theorem pairedFiniteFrameRelativeC2Target_contDiffOn :
    ContDiffOn Real ∞ (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame)
      (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) := by
  have hFirst : ContDiffOn Real ∞ (fun variation : Model => variation.1)
      (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :=
    contDiff_fst.contDiffOn
  have hInverse :=
    (generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod frame geometry.plusMetric).comp
      hFirst (fun _ hPoint => hPoint)
  have hSecond : ContDiffOn Real ∞ (fun variation : Model => variation.2.1)
      (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :=
    ((generalMetricRelativeC2CoreToMatrix period hPeriod frame
      geometry.plusMetric).contDiff.comp contDiff_snd).contDiffOn
  have hNumerator : ContDiffOn Real ∞ (fun variation : Model => (square root).1 + variation.2.1)
      (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :=
    contDiffOn_const.add hSecond
  have hProduct := ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
    frame.count).contDiff.comp_contDiffOn hInverse).clm_apply hNumerator
  exact (finiteFrameC2CornerProjection period hPeriod frame geometry.plusMetric).contDiff.comp_contDiffOn
    hProduct

theorem pairedFiniteFrameRelativeC2Target_zero :
    pairedFiniteFrameRelativeC2Target period hPeriod geometry frame 0 = square root := by
  have hInverse := generalMetricRelativeC2Extended_mul_inverse period hPeriod frame
    geometry.plusMetric 0 (zero_mem_generalMetricRelativeC2OpenDomain
      period hPeriod frame geometry.plusMetric)
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
    (c2FiniteMatrixIdentity period hPeriod frame.count + 0)
    (generalMetricRelativeC2InverseMatrix period hPeriod frame geometry.plusMetric 0) = _
    at hInverse
  rw [add_zero, c2FiniteMatrixProduct_identity_left] at hInverse
  apply Subtype.ext
  change c2FiniteFrameCornerProjection period hPeriod frame geometry.plusMetric
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2InverseMatrix period hPeriod frame geometry.plusMetric 0)
      ((square root).1 + 0)) = (square root).1
  rw [hInverse, add_zero, c2FiniteMatrixProduct_identity_left]
  exact (c2FiniteFrameCorner_mem_iff period hPeriod frame geometry.plusMetric _).1
    (square root).2

/-- Exact relative-metric equation on the completed model: projection has
not changed the solution of `(I + A₊) R = R₀ + A₋`. -/
theorem pairedFiniteFrameRelativeC2Target_mul
    (variation : Model)
    (hVariation : variation ∈ pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame geometry.plusMetric variation.1)
      (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame variation).1 =
      (square root).1 + variation.2.1 := by
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
  let projector := c2FiniteFrameProjector period hPeriod frame geometry.plusMetric
  let extended := generalMetricRelativeC2ExtendedMatrix period hPeriod frame
    geometry.plusMetric variation.1
  let inverse := generalMetricRelativeC2InverseMatrix period hPeriod frame
    geometry.plusMetric variation.1
  let numerator : Corner := square root +
    ⟨variation.2.1, generalMetricRelativeC2Core_mem_corner period hPeriod frame
      geometry.plusMetric variation.2⟩
  have hNumerator := (c2FiniteFrameCorner_mem_iff period hPeriod frame
    geometry.plusMetric numerator.1).1 numerator.2
  have hLeft := c2FiniteMatrixSandwich_left period hPeriod frame.count projector numerator.1
    (c2FiniteFrameProjector_idempotent period hPeriod frame geometry.plusMetric) hNumerator
  have hRight := c2FiniteMatrixSandwich_right period hPeriod frame.count projector numerator.1
    (c2FiniteFrameProjector_idempotent period hPeriod frame geometry.plusMetric) hNumerator
  have hCommute : product extended projector = product projector extended := by
    change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteMatrixIdentity period hPeriod frame.count + variation.1.1)
        (c2FiniteFrameProjector period hPeriod frame geometry.plusMetric) =
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame geometry.plusMetric)
        (c2FiniteMatrixIdentity period hPeriod frame.count + variation.1.1)
    simp only [map_add, add_apply, c2FiniteMatrixProduct_identity_left,
      c2FiniteMatrixProduct_identity_right, generalMetricRelativeC2Core_left_projector,
      generalMetricRelativeC2Core_right_projector]
  have hInverse : product extended inverse = c2FiniteMatrixIdentity period hPeriod frame.count :=
    generalMetricRelativeC2Extended_mul_inverse period hPeriod frame geometry.plusMetric
      variation.1 hVariation
  have hResult := projector_inverse_product (fun first second => product first second)
    (c2FiniteMatrixIdentity period hPeriod frame.count) projector extended inverse numerator.1
    (c2FiniteMatrixProduct_assoc period hPeriod frame.count)
    (c2FiniteMatrixProduct_identity_left period hPeriod frame.count)
    hCommute hInverse hLeft hRight
  exact hResult

/-- On genuine smooth variations the numerator is precisely `g₊⁻¹(g₋ + h₋)`. -/
theorem pairedFiniteFrameRelativeC2Target_smooth_input
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation)).1 =
      c2FiniteFrameCornerProjection period hPeriod frame geometry.plusMetric
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
          (generalMetricRelativeC2InverseMatrix period hPeriod frame geometry.plusMetric
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation))
          (smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame geometry.plusMetric
            (geometry.minusMetric.tensor + minusVariation))) := by
  change c2FiniteFrameCornerProjection period hPeriod frame geometry.plusMetric
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count _
      ((square root).1 + smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame
        geometry.plusMetric minusVariation)) = _
  rw [finiteFrameStoredRootSquare_eq_relative,
    (smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame geometry.plusMetric).map_add
      geometry.minusMetric.tensor minusVariation]

/-- SAME-MATRIX in the full C² core, proved by uniqueness of the existing
relative-metric equation. Both varied metrics are genuine supplied metrics. -/
theorem pairedFiniteFrameRelativeC2Target_eq_smooth
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedPlus variedMinus : SmoothGeneralLorentzMetric period hPeriod)
    (hPlus : variedPlus.tensor = geometry.plusMetric.tensor + plusVariation)
    (hMinus : variedMinus.tensor = geometry.minusMetric.tensor + minusVariation)
    (hVariation :
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation) ∈
        pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :
    (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation)).1 =
      smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus) := by
  let input : Model :=
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
     smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation)
  let candidate := smoothFiniteMatrixToC2 period hPeriod frame.count
    (smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus)
  have hCandidate : c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame geometry.plusMetric input.1)
      candidate = (square root).1 + input.2.1 := by
    change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count +
        smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame geometry.plusMetric
            plusVariation))
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothPairedFiniteFrameRelativeMatrix period hPeriod geometry frame variedPlus variedMinus)) = _
    rw [map_add, add_apply, c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_smooth,
      ← (smoothFiniteMatrixToC2 period hPeriod frame.count).map_add,
      smoothPairedFiniteFrameRelativeMatrix_equation period hPeriod geometry frame
        plusVariation variedPlus variedMinus hPlus]
    change smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame geometry.plusMetric
      variedMinus.tensor = (square root).1 +
        smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame geometry.plusMetric minusVariation
    rw [hMinus, (smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame
      geometry.plusMetric).map_add, finiteFrameStoredRootSquare_eq_relative]
  have hTarget := pairedFiniteFrameRelativeC2Target_mul period hPeriod geometry frame input hVariation
  have hUnit : (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame geometry.plusMetric input.1)).IsInvertible :=
    hVariation
  exact hUnit.injective (hTarget.trans hCandidate.symm)

/-- Actual pointwise relative matrix `sharp(variedPlus) ∘ variedMinus.tensor`,
using the same fixed redundant frame as the completed target. -/
theorem pairedFiniteFrameRelativeC2Target_sameMatrix
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedPlus variedMinus : SmoothGeneralLorentzMetric period hPeriod)
    (hPlus : variedPlus.tensor = geometry.plusMetric.tensor + plusVariation)
    (hMinus : variedMinus.tensor = geometry.minusMetric.tensor + minusVariation)
    (hVariation :
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation) ∈
        pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod) (row column : Fin frame.count) :
    (((pairedFiniteFrameRelativeC2Target period hPeriod geometry frame
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric plusVariation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric minusVariation)).1
        row column).1 point).1 =
      finiteFrameEndomorphismMatrixAt period hPeriod frame geometry.plusMetric point
        ((inverseMetricSharp period hPeriod variedPlus point).comp (variedMinus.tensor.tensor point))
        row column := by
  have hC2 := pairedFiniteFrameRelativeC2Target_eq_smooth period hPeriod geometry frame
    plusVariation minusVariation variedPlus variedMinus hPlus hMinus hVariation
  have hValue := congrArg (fun matrix : C2FiniteMatrix period hPeriod frame.count =>
    ((matrix row column).1 point).1) hC2
  exact hValue.trans (smoothPairedFiniteFrameRelativeMatrix_entry_apply period hPeriod geometry frame
    variedPlus variedMinus row column point)

def pairedFiniteFrameRelativeC2Delta (variation : Model) : Corner :=
  pairedFiniteFrameRelativeC2Target period hPeriod geometry frame variation - square root

theorem pairedFiniteFrameRelativeC2Delta_contDiffOn :
    ContDiffOn Real ∞ (pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame)
      (pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame) :=
  (pairedFiniteFrameRelativeC2Target_contDiffOn period hPeriod geometry frame).sub contDiffOn_const

theorem pairedFiniteFrameRelativeC2Delta_zero :
    pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame 0 = 0 := by
  unfold pairedFiniteFrameRelativeC2Delta
  rw [pairedFiniteFrameRelativeC2Target_zero, sub_self]

variable (hRegular : ∀ point, Function.Bijective
  (intrinsicCandidateASylvesterAt period hPeriod geometry point))

local notation "branch" =>
  globalCandidateAC2FiniteFrameLocalRootBranch period hPeriod geometry frame hRegular

def pairedFiniteFrameMetricC2RootDomain : Set Model :=
  pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame ∩
    pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame ⁻¹' (branch).domain

theorem pairedFiniteFrameMetricC2RootDomain_isOpen :
    IsOpen (pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular) :=
  (pairedFiniteFrameRelativeC2Delta_contDiffOn period hPeriod geometry frame).continuousOn.isOpen_inter_preimage
    (pairedFiniteFrameRelativeC2Domain_isOpen period hPeriod geometry frame)
      (branch).domain_isOpen

theorem zero_mem_pairedFiniteFrameMetricC2RootDomain :
    (0 : Model) ∈ pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular := by
  refine ⟨zero_mem_pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame, ?_⟩
  change pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame 0 ∈ (branch).domain
  rw [pairedFiniteFrameRelativeC2Delta_zero]
  exact (branch).zero_mem_domain

def pairedFiniteFrameMetricC2Root (variation : Model) : Corner :=
  (branch).branch (pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame variation)

theorem pairedFiniteFrameMetricC2Root_contDiffOn :
    ContDiffOn Real 2 (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular)
      (pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular) := by
  have hDelta := (pairedFiniteFrameRelativeC2Delta_contDiffOn period hPeriod geometry frame).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  exact (branch).branch_contDiffOn.comp (hDelta.mono Set.inter_subset_left)
    (fun _ hPoint => hPoint.2)

theorem pairedFiniteFrameMetricC2Root_zero :
    pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular 0 = root := by
  unfold pairedFiniteFrameMetricC2Root
  rw [pairedFiniteFrameRelativeC2Delta_zero,
    globalCandidateAC2FiniteFrameLocalRootBranch_zero]

theorem pairedFiniteFrameMetricC2Root_square
    (variation : Model)
    (hVariation : variation ∈
      pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular) :
    square (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular variation) =
      pairedFiniteFrameRelativeC2Target period hPeriod geometry frame variation := by
  have hSquare := (branch).branch_rightInverse
    (pairedFiniteFrameRelativeC2Delta period hPeriod geometry frame variation) hVariation.2
  change _ = square root +
    (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame variation - square root)
    at hSquare
  exact hSquare.trans (by abel)

end
end P0EFTJanusFiniteFramePairedRelativeC2Root4D
end JanusFormal
