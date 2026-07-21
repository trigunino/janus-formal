import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

/-!
# Local Frechet-gradient to intrinsic-differential bridge

The scalar pulled back by a genuine smooth holonomic coordinate map has the
same directional derivatives as the intrinsic manifold differential evaluated
on the coordinate frame.  This is the direct manifold chain rule; no local
Euler or integration-by-parts hypothesis is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The Frechet derivative of the pulled-back scalar in a coordinate basis
direction is the intrinsic scalar differential on the corresponding genuine
tangent-frame vector.  `SmoothHolonomicFrameChart4.coordinateMap` is total,
so no additional domain-membership hypothesis is needed here. -/
theorem localScalarGradient_eq_scalarDifferential_frame
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) :
    localScalarGradient period hPeriod field patch coordinate index =
      scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
        (patch.frame coordinate index) := by
  let direction : Vector4 := Pi.single index (1 : Real)
  have hChain := mfderiv_comp_apply coordinate
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp))
    direction
  have hChainReal :
      NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv (modelWithCornersSelf Real Vector4) 𝓘(Real, Real)
            (field.toFun ∘ patch.coordinateMap) coordinate direction) =
        NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv coverModelWithCorners 𝓘(Real, Real) field.toFun
            (patch.coordinateMap coordinate)
            (mfderiv (modelWithCornersSelf Real Vector4)
              coverModelWithCorners patch.coordinateMap coordinate direction)) :=
    congrArg
      (NormedSpace.fromTangentSpace
        (field.toFun (patch.coordinateMap coordinate))) hChain
  have hLeft :
      localScalarGradient period hPeriod field patch coordinate index =
        NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv (modelWithCornersSelf Real Vector4) 𝓘(Real, Real)
            (field.toFun ∘ patch.coordinateMap) coordinate direction) := by
    change fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate direction = _
    rw [mfderiv_eq_fderiv]
    rfl
  have hRight :
      NormedSpace.fromTangentSpace
          (field.toFun (patch.coordinateMap coordinate))
          (mfderiv coverModelWithCorners 𝓘(Real, Real) field.toFun
            (patch.coordinateMap coordinate)
            (mfderiv (modelWithCornersSelf Real Vector4)
              coverModelWithCorners patch.coordinateMap coordinate direction)) =
        scalarDifferential period hPeriod field (patch.coordinateMap coordinate)
          (patch.frame coordinate index) := by
    rw [patch.frame_eq_coordinateDerivative coordinate index]
    rfl
  exact hLeft.trans (hChainReal.trans hRight)

/-- If a member of any global smooth generating family agrees at a chart
image point with a scalar multiple of one coordinate-frame vector, its graph
derivative is that scalar multiple of the local Frechet gradient.  The vector
equality is the precise pointwise compatibility hypothesis. -/
theorem frameDerivative_eq_weight_mul_localScalarGradient_of_vectorAt_eq
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (frameIndex : Fin frame.count)
    (coordinateIndex : Index4) (weight : Real)
    (hVector :
      frame.vectorAt (patch.coordinateMap coordinate) frameIndex =
        weight • patch.frame coordinate coordinateIndex) :
    frameDerivative period hPeriod Real frame field
        (patch.coordinateMap coordinate) frameIndex =
      weight *
        localScalarGradient period hPeriod field patch coordinate
          coordinateIndex := by
  rw [frameDerivative_eq_mfderiv]
  change scalarDifferential period hPeriod field
      (patch.coordinateMap coordinate)
      (frame.vectorAt (patch.coordinateMap coordinate) frameIndex) = _
  rw [hVector, map_smul]
  simp only [smul_eq_mul]
  rw [← localScalarGradient_eq_scalarDifferential_frame
    period hPeriod field patch coordinate coordinateIndex]

private abbrev fixedTangentTrivialization
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  trivializationAt CoverCoordinates
    (TangentSpace coverModelWithCorners) patch.1

private def finiteGeneratorModelBasis :
    Module.Basis FiniteTangentGeneratorBasisIndex Real CoverCoordinates :=
  Module.finBasis Real CoverCoordinates

/-- The model vector used by one member of the finite tangent-generator
basis. -/
def finiteGeneratorModelBasisVector
    (basisIndex : FiniteTangentGeneratorBasisIndex) : CoverCoordinates :=
  finiteGeneratorModelBasis basisIndex

/-- The open patch used by one finite generator is exactly the source of the
quotient chart at its fixed anchor. -/
theorem finiteTangentGeneratorOpenPatch_eq_chartAt_source
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    finiteTangentGeneratorOpenPatch period hPeriod patch =
      (chartAt CoverModel patch.1).source := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On its genuine open patch, the unweighted local vector used by the
canonical finite generating family is the derivative of the inverse fixed
chart applied to the corresponding model-basis vector. -/
theorem finiteTangentGeneratorLocalVector_eq_chartAt_inverseDerivative
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex)
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∈
      finiteTangentGeneratorOpenPatch period hPeriod patch) :
    finiteTangentGeneratorLocalVector period hPeriod patch basisIndex point =
      mfderivWithin (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners
        (extChartAt coverModelWithCorners patch.1).symm
        (Set.range coverModelWithCorners)
        (extChartAt coverModelWithCorners patch.1 point)
        (finiteGeneratorModelBasisVector basisIndex) := by
  have hChart : point ∈ (chartAt CoverModel patch.1).source := by
    rw [← finiteTangentGeneratorOpenPatch_eq_chartAt_source
      period hPeriod patch]
    exact hPoint
  have hBase : point ∈
      (fixedTangentTrivialization period hPeriod patch).baseSet := by
    simpa [fixedTangentTrivialization] using hChart
  change
    (fixedTangentTrivialization period hPeriod patch).localFrame
        finiteGeneratorModelBasis basisIndex point = _
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _
    finiteGeneratorModelBasis hBase]
  change
    (fixedTangentTrivialization period hPeriod patch).symmL Real point
        (finiteGeneratorModelBasisVector basisIndex) = _
  rw [TangentBundle.symmL_trivializationAt hChart]
  rfl

/-- Concrete specialization to the implemented finite frame.  The only
remaining datum is that a supplied total holonomic patch has the same frame
vector as the derivative of the inverse fixed chart at the point in question.
The fixed-chart derivative itself is proved above rather than assumed. -/
theorem finiteFrameDerivative_eq_weight_mul_localScalarGradient_of_chartAt
    (field : SmoothScalarField period hPeriod)
    (generatorIndex : FiniteTangentGeneratorIndex period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (coordinateIndex : Index4)
    (hPoint : patch.coordinateMap coordinate ∈
      finiteTangentGeneratorOpenPatch period hPeriod generatorIndex.1)
    (hFrame :
      patch.frame coordinate coordinateIndex =
        mfderivWithin (modelWithCornersSelf Real CoverCoordinates)
          coverModelWithCorners
          (extChartAt coverModelWithCorners generatorIndex.1.1).symm
          (Set.range coverModelWithCorners)
          (extChartAt coverModelWithCorners generatorIndex.1.1
            (patch.coordinateMap coordinate))
          (finiteGeneratorModelBasisVector generatorIndex.2)) :
    frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field
        (patch.coordinateMap coordinate)
        (finiteTangentGeneratorIndexEquivFin period hPeriod generatorIndex) =
      finiteTangentGeneratorWeight period hPeriod generatorIndex.1
          (patch.coordinateMap coordinate) *
        localScalarGradient period hPeriod field patch coordinate
          coordinateIndex := by
  apply frameDerivative_eq_weight_mul_localScalarGradient_of_vectorAt_eq
    period hPeriod (finiteSmoothTangentFrame period hPeriod) field patch
      coordinate
      (finiteTangentGeneratorIndexEquivFin period hPeriod generatorIndex)
      coordinateIndex
      (finiteTangentGeneratorWeight period hPeriod generatorIndex.1
        (patch.coordinateMap coordinate))
  rw [finiteSmoothTangentFrame_vectorAt_generator]
  rw [finiteTangentGeneratorLocalVector_eq_chartAt_inverseDerivative
    period hPeriod generatorIndex.1 generatorIndex.2
      (patch.coordinateMap coordinate) hPoint]
  rw [← hFrame]

/-- The intrinsic scalar differential of any tangent vector is the finite
sum of its coefficients in a genuine holonomic frame times the corresponding
local Frechet gradients. -/
theorem scalarDifferential_eq_sum_frameCoordinate_mul_localScalarGradient
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (vector : TangentSpace coverModelWithCorners
      (patch.coordinateMap coordinate)) :
    scalarDifferential period hPeriod field
        (patch.coordinateMap coordinate) vector =
      ∑ index : Index4,
        (patch.frame coordinate).repr vector index *
          localScalarGradient period hPeriod field patch coordinate index := by
  conv_lhs =>
    rw [← (patch.frame coordinate).sum_repr vector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [← localScalarGradient_eq_scalarDifferential_frame
    period hPeriod field patch coordinate index]

/-- The implemented finite-frame derivative needs no one-vector alignment
with a holonomic patch: the fixed local vector is expanded in the complete
coordinate basis of that patch. -/
theorem finiteFrameDerivative_eq_weight_mul_sum_localScalarGradient
    (field : SmoothScalarField period hPeriod)
    (generatorIndex : FiniteTangentGeneratorIndex period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field
        (patch.coordinateMap coordinate)
        (finiteTangentGeneratorIndexEquivFin period hPeriod generatorIndex) =
      finiteTangentGeneratorWeight period hPeriod generatorIndex.1
          (patch.coordinateMap coordinate) *
        ∑ index : Index4,
          (patch.frame coordinate).repr
              (finiteTangentGeneratorLocalVector period hPeriod
                generatorIndex.1 generatorIndex.2
                (patch.coordinateMap coordinate)) index *
            localScalarGradient period hPeriod field patch coordinate index := by
  rw [frameDerivative_eq_mfderiv]
  change scalarDifferential period hPeriod field
      (patch.coordinateMap coordinate)
      ((finiteSmoothTangentFrame period hPeriod).vectorAt
        (patch.coordinateMap coordinate)
        (finiteTangentGeneratorIndexEquivFin period hPeriod generatorIndex)) = _
  rw [finiteSmoothTangentFrame_vectorAt_generator, map_smul]
  simp only [smul_eq_mul]
  rw [scalarDifferential_eq_sum_frameCoordinate_mul_localScalarGradient
    period hPeriod field patch coordinate]

/-- Every point of the actual quotient admits one of the already constructed
total holonomic patches, and on that patch each canonical finite-frame graph
derivative has the exact finite local-gradient expansion above. -/
theorem exists_holonomicPatch_finiteFrameDerivative_eq_localGradientSum
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (generatorIndex : FiniteTangentGeneratorIndex period hPeriod) :
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      patch.coordinateMap coordinate = point ∧
      frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point
          (finiteTangentGeneratorIndexEquivFin period hPeriod generatorIndex) =
        finiteTangentGeneratorWeight period hPeriod generatorIndex.1 point *
          ∑ index : Index4,
            (patch.frame coordinate).repr
                (finiteTangentGeneratorLocalVector period hPeriod
                  generatorIndex.1 generatorIndex.2 point) index *
              localScalarGradient period hPeriod field patch coordinate index := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  refine ⟨patch, coordinate, hCoordinate, ?_⟩
  subst point
  exact finiteFrameDerivative_eq_weight_mul_sum_localScalarGradient
    period hPeriod field generatorIndex patch coordinate

end

end P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D
end JanusFormal
