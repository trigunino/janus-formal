import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

/-!
# Global-frame obstruction and local regularization on D8

The reflection generator reverses the determinant of a lifted tangent frame.
Its determinant would therefore be a continuous, nowhere-zero,
anti-periodic real function, which cannot exist.  The correct replacement is
the canonical family of smooth local frames from tangent trivializations,
together with a smooth partition of unity subordinate to their domains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalFrameNoGo4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Set MeasureTheory Bundle Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- Determinant data forced on the lift of a hypothetical global frame by the
orientation-reversing mapping-torus generator. -/
structure AntiPeriodicFrameDeterminant where
  determinant : Real → Real
  continuous : Continuous determinant
  nowhereZero : ∀ time, determinant time ≠ 0
  antiPeriodic : ∀ time, determinant (time + period) = -determinant time

/-- A continuous nowhere-zero determinant cannot reverse sign after one
period.  This is the determinant-line obstruction to a global D8 frame. -/
theorem no_antiPeriodicFrameDeterminant :
    IsEmpty (AntiPeriodicFrameDeterminant period) := by
  constructor
  intro data
  have hAtPeriod : data.determinant period = -data.determinant 0 := by
    simpa using data.antiPeriodic 0
  rcases lt_or_gt_of_ne (data.nowhereZero 0).symm with hPositive | hNegative
  · have hBetween : data.determinant period ≤ 0 ∧ 0 ≤ data.determinant 0 := by
      constructor <;> linarith
    rcases intermediate_value_univ period 0 data.continuous hBetween with
      ⟨time, hTime⟩
    exact data.nowhereZero time hTime
  · have hBetween : data.determinant 0 ≤ 0 ∧ 0 ≤ data.determinant period := by
      constructor <;> linarith
    rcases intermediate_value_univ 0 period data.continuous hBetween with
      ⟨time, hTime⟩
    exact data.nowhereZero time hTime

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private def coverCoordinateBasis : Basis (Fin 4) Real CoverCoordinates := by
  let basis := Module.finBasis Real CoverCoordinates
  have hDimension : Module.finrank Real CoverCoordinates = 4 := by
    simp [CoverCoordinates]
  simpa [hDimension] using basis

private abbrev tangentTrivialization
    (anchor : EffectiveQuotient period hPeriod) :=
  trivializationAt CoverCoordinates (TangentFiber period hPeriod) anchor

/-- Canonical local tangent frame supplied by the tangent trivialization. -/
def localTangentFrame
    (anchor : EffectiveQuotient period hPeriod) :
    Fin 4 → (point : EffectiveQuotient period hPeriod) →
      TangentFiber period hPeriod point :=
  (tangentTrivialization period hPeriod anchor).localFrame coverCoordinateBasis

def localTangentFrameDomain
    (anchor : EffectiveQuotient period hPeriod) : Set (EffectiveQuotient period hPeriod) :=
  (tangentTrivialization period hPeriod anchor).baseSet

theorem localTangentFrameDomain_open
    (anchor : EffectiveQuotient period hPeriod) :
    IsOpen (localTangentFrameDomain period hPeriod anchor) :=
  (tangentTrivialization period hPeriod anchor).open_baseSet

theorem anchor_mem_localTangentFrameDomain
    (anchor : EffectiveQuotient period hPeriod) :
    anchor ∈ localTangentFrameDomain period hPeriod anchor :=
  FiberBundle.mem_baseSet_trivializationAt' anchor

theorem localTangentFrame_isLocalFrameOn
    (anchor : EffectiveQuotient period hPeriod) :
    IsLocalFrameOn coverModelWithCorners CoverCoordinates ω
      (localTangentFrame period hPeriod anchor)
      (localTangentFrameDomain period hPeriod anchor) :=
  (tangentTrivialization period hPeriod anchor).isLocalFrameOn_localFrame_baseSet
    coverModelWithCorners ω coverCoordinateBasis

/-- Smooth partitions subordinate to the canonical tangent-frame cover exist
on compact D8. -/
theorem exists_localFramePartition :
    ∃ partition : SmoothPartitionOfUnity
        (EffectiveQuotient period hPeriod) coverModelWithCorners
        (EffectiveQuotient period hPeriod) univ,
      partition.IsSubordinate (localTangentFrameDomain period hPeriod) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate coverModelWithCorners
    isClosed_univ (localTangentFrameDomain period hPeriod)
    (localTangentFrameDomain_open period hPeriod)
  intro point _
  exact mem_iUnion_of_mem point
    (anchor_mem_localTangentFrameDomain period hPeriod point)

/-- Nonempty local replacement for the impossible global-frame regularity
class, carrying the existing smooth positive diagonal branch. -/
structure LocalFrameRegularization where
  partition : SmoothPartitionOfUnity
    (EffectiveQuotient period hPeriod) coverModelWithCorners
    (EffectiveQuotient period hPeriod) univ
  subordinate :
    partition.IsSubordinate (localTangentFrameDomain period hPeriod)
  diagonal : SmoothPositiveDiagonalMetricPair period hPeriod

def flatLocalFrameRegularization :
    LocalFrameRegularization period hPeriod := by
  let partition := Classical.choose
    (exists_localFramePartition period hPeriod)
  exact
    { partition := partition
      subordinate := Classical.choose_spec
        (exists_localFramePartition period hPeriod)
      diagonal := flatPositiveMetricPair period hPeriod }

theorem localFrameRegularization_nonempty :
    Nonempty (LocalFrameRegularization period hPeriod) :=
  ⟨flatLocalFrameRegularization period hPeriod⟩

private abbrev RawCoefficientSpace := Fin 4 → Real
private abbrev CoefficientSpace := EuclideanSpace Real (Fin 4)
private abbrev CoefficientCovector := CoefficientSpace →L[Real] Real

private def coefficientToRaw :
    CoefficientSpace ≃L[Real] RawCoefficientSpace :=
  PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 4 => Real)

private def modelCoordinateEquiv :
    CoverCoordinates ≃L[Real] CoefficientSpace :=
  coverCoordinateBasis.equivFun.toContinuousLinearEquiv.trans
    coefficientToRaw.symm

private theorem signature_ne_zero (index : Fin 4) : signature index ≠ 0 := by
  fin_cases index <;> norm_num [signature]

/-- Invertible diagonal signature scaling on local frame coefficients. -/
def diagonalSignatureScale
    (magnitudes : RawCoefficientSpace)
    (hPositive : ∀ index, 0 < magnitudes index) :
    CoefficientSpace ≃L[Real] CoefficientSpace :=
  coefficientToRaw.trans
    ((ContinuousLinearEquiv.piCongrRight (fun index =>
      ContinuousLinearEquiv.smulLeft
        (Units.mk0 (signature index * magnitudes index)
          (mul_ne_zero (signature_ne_zero index)
            (ne_of_gt (hPositive index)))))).trans coefficientToRaw.symm)

/-- Musical equivalence of the existing positive diagonal Lorentz
coefficients in the model frame. -/
def diagonalModelMusical
    (magnitudes : RawCoefficientSpace)
    (hPositive : ∀ index, 0 < magnitudes index) :
    CoverCoordinates ≃L[Real] (CoverCoordinates →L[Real] Real) :=
  modelCoordinateEquiv.trans
    ((diagonalSignatureScale magnitudes hPositive).trans
      ((InnerProductSpace.toDual Real CoefficientSpace).toContinuousLinearEquiv.trans
        (modelCoordinateEquiv.symm.arrowCongr
          (ContinuousLinearEquiv.refl Real Real))))

/-- Tangent coordinates supplied by one canonical local frame patch. -/
def localTangentCoordinateEquiv
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point ≃L[Real] CoverCoordinates :=
  (tangentTrivialization period hPeriod anchor).continuousLinearEquivAt
    Real point hPoint

/-- Change of coordinates between two canonical tangent-frame patches. -/
def localFrameTransition
    (first second point : EffectiveQuotient period hPeriod)
    (hFirst : point ∈ localTangentFrameDomain period hPeriod first)
    (hSecond : point ∈ localTangentFrameDomain period hPeriod second) :
    CoverCoordinates ≃L[Real] CoverCoordinates :=
  (localTangentCoordinateEquiv period hPeriod first point hFirst).symm.trans
    (localTangentCoordinateEquiv period hPeriod second point hSecond)

theorem localFrameTransition_coordinates
    (first second point : EffectiveQuotient period hPeriod)
    (hFirst : point ∈ localTangentFrameDomain period hPeriod first)
    (hSecond : point ∈ localTangentFrameDomain period hPeriod second)
    (vector : TangentFiber period hPeriod point) :
    localFrameTransition period hPeriod first second point hFirst hSecond
        (localTangentCoordinateEquiv period hPeriod first point hFirst vector) =
      localTangentCoordinateEquiv period hPeriod second point hSecond vector := by
  simp [localFrameTransition]

/-- Intrinsic local Lorentz musical map obtained by pulling the existing
diagonal coefficients through the canonical tangent trivialization. -/
def localDiagonalMusical
    (regularization : LocalFrameRegularization period hPeriod)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point ≃L[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
  let coordinates := localTangentCoordinateEquiv period hPeriod anchor point hPoint
  let modelMusical := diagonalModelMusical
    (regularization.diagonal.plusMagnitude point)
    (regularization.diagonal.plus_pos point)
  coordinates.trans
    (modelMusical.trans (coordinates.symm.arrowCongr
      (ContinuousLinearEquiv.refl Real Real)))

/-- The local sharp is definitionally the inverse of the same local metric. -/
def localDiagonalSharp
    (regularization : LocalFrameRegularization period hPeriod)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    (TangentFiber period hPeriod point →L[Real] Real) ≃L[Real]
      TangentFiber period hPeriod point :=
  (localDiagonalMusical period hPeriod regularization anchor point hPoint).symm

/-- Covariant rank-two tensor represented by the local musical equivalence. -/
def localDiagonalTensor
    (regularization : LocalFrameRegularization period hPeriod)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor) :
    TangentFiber period hPeriod point →L[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
  (localDiagonalMusical period hPeriod regularization anchor point hPoint).toContinuousLinearMap

/-- Absolute Lorentz determinant density in the same local diagonal frame. -/
def localDiagonalVolumeCoefficient
    (regularization : LocalFrameRegularization period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  Real.sqrt (∏ index : Fin 4,
    regularization.diagonal.plusMagnitude point index)

theorem localDiagonalVolumeCoefficient_pos
    (regularization : LocalFrameRegularization period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 < localDiagonalVolumeCoefficient period hPeriod regularization point := by
  apply Real.sqrt_pos.2
  exact Finset.prod_pos fun index _ => regularization.diagonal.plus_pos point index

@[simp]
theorem localDiagonalMusical_sharp
    (regularization : LocalFrameRegularization period hPeriod)
    (anchor point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈ localTangentFrameDomain period hPeriod anchor)
    (covector : TangentFiber period hPeriod point →L[Real] Real) :
    localDiagonalMusical period hPeriod regularization anchor point hPoint
        (localDiagonalSharp period hPeriod regularization anchor point hPoint
          covector) = covector := by
  simp [localDiagonalSharp]

end

end P0EFTJanusMappingTorusLocalFrameNoGo4D
end JanusFormal
