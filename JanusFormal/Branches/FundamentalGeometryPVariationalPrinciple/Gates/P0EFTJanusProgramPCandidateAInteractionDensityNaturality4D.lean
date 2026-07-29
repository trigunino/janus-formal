import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Pointwise naturality of the Candidate-A interaction density

This gate isolates the geometric core of the interaction-block
diffeomorphism proof.  If the plus metric is pulled back by a tangent
equivalence and the Candidate-A square root is transported by conjugation,
then the exact determinant/root/spectral interaction density is unchanged in
the correspondingly transported basis.

The theorem is pointwise.  Constructing a smooth pulled
`GlobalCandidateAGeometry`, including its `rootOperator`, remains separate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAInteractionDensityNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Conjugating an endomorphism and transporting its basis by the same linear
equivalence leaves its coefficient matrix literally unchanged. -/
theorem toMatrix_conjugate_transportedBasis
    {source target : Type*}
    [AddCommGroup source] [Module Real source]
    [AddCommGroup target] [Module Real target]
    (equivalence : source ≃ₗ[Real] target)
    (basis : Module.Basis (Fin 4) Real target)
    (endomorphism : target →ₗ[Real] target) :
    LinearMap.toMatrix
        (basis.map equivalence.symm) (basis.map equivalence.symm)
        (equivalence.symm.toLinearMap.comp
          (endomorphism.comp equivalence.toLinearMap)) =
      LinearMap.toMatrix basis basis endomorphism := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext vector
  simp

/-- Exact pointwise naturality of the full Candidate-A interaction density.
The source basis is pulled back by the inverse tangent equivalence, while the
metric and square root obey their genuine tensor/endomorphism pullback laws. -/
theorem globalCandidateAInteractionDensityAt_pullback
    (sourceGeometry targetGeometry :
      GlobalCandidateAGeometry period hPeriod)
    {sourcePoint targetPoint : EffectiveQuotient period hPeriod}
    (equivalence :
      TangentFiber period hPeriod sourcePoint ≃L[Real]
        TangentFiber period hPeriod targetPoint)
    (targetBasis :
      Module.Basis (Fin 4) Real
        (TangentFiber period hPeriod targetPoint))
    (hMetric :
      targetGeometry.plusMetric.musical sourcePoint =
        pullbackMusical period hPeriod equivalence
          (sourceGeometry.plusMetric.musical targetPoint))
    (hRoot :
      targetGeometry.rootAt sourcePoint =
        equivalence.symm.toContinuousLinearMap.comp
          ((sourceGeometry.rootAt targetPoint).comp
            equivalence.toContinuousLinearMap))
    (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    GlobalCandidateAGeometry.interactionDensityAt period hPeriod
        targetGeometry interactionScale coefficients sourcePoint
        (targetBasis.map equivalence.toLinearEquiv.symm) =
      GlobalCandidateAGeometry.interactionDensityAt period hPeriod
        sourceGeometry interactionScale coefficients targetPoint targetBasis := by
  have hVolume :
      metricVolumeDensity period hPeriod targetGeometry.plusMetric sourcePoint
          (targetBasis.map equivalence.toLinearEquiv.symm) =
        metricVolumeDensity period hPeriod sourceGeometry.plusMetric targetPoint
          targetBasis := by
    rw [metricVolumeDensity_eq_fiber, metricVolumeDensity_eq_fiber, hMetric]
    calc
      fiberMetricVolumeDensity period hPeriod
          (pullbackMusical period hPeriod equivalence
            (sourceGeometry.plusMetric.musical targetPoint))
          (targetBasis.map equivalence.toLinearEquiv.symm) =
        fiberMetricVolumeDensity period hPeriod
          (sourceGeometry.plusMetric.musical targetPoint)
          (fun index =>
            equivalence
              ((targetBasis.map equivalence.toLinearEquiv.symm) index)) :=
        fiberMetricVolumeDensity_pullback period hPeriod equivalence
          (sourceGeometry.plusMetric.musical targetPoint)
          (fun index =>
            (targetBasis.map equivalence.toLinearEquiv.symm) index)
      _ = fiberMetricVolumeDensity period hPeriod
          (sourceGeometry.plusMetric.musical targetPoint) targetBasis := by
        congr 1
        funext index
        simp
  have hRootMatrix :
      GlobalCandidateAGeometry.rootMatrixAt period hPeriod targetGeometry
          sourcePoint (targetBasis.map equivalence.toLinearEquiv.symm) =
        GlobalCandidateAGeometry.rootMatrixAt period hPeriod sourceGeometry
          targetPoint targetBasis := by
    unfold GlobalCandidateAGeometry.rootMatrixAt
    rw [hRoot]
    exact toMatrix_conjugate_transportedBasis
      equivalence.toLinearEquiv targetBasis
        (sourceGeometry.rootAt targetPoint).toLinearMap
  unfold GlobalCandidateAGeometry.interactionDensityAt
  rw [hVolume, hRootMatrix]

/-- Geometric data that reduce smooth interaction-density transport to the
actual metric/root pullback laws and the transported regular frame. -/
structure GlobalCandidateAInteractionDiffeomorphismGeometryTransport
    {sourceConfiguration targetConfiguration :
      GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (diffeomorphism :
      P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D.SpacetimeDiffeomorphism
        period hPeriod)
    (source :
      GlobalCandidateAActionData period hPeriod sourceConfiguration couplings
        NonNullFace NullFace)
    (target :
      GlobalCandidateAActionData period hPeriod targetConfiguration couplings
        NonNullFace NullFace) : Prop where
  plusMetricMusical : ∀ point,
    targetConfiguration.geometry.plusMetric.musical point =
      pullbackMusical period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (sourceConfiguration.geometry.plusMetric.musical
          (diffeomorphism point))
  rootAt : ∀ point,
    targetConfiguration.geometry.rootAt point =
      ((diffeomorphismDerivative period hPeriod diffeomorphism point).symm.toContinuousLinearMap).comp
        ((sourceConfiguration.geometry.rootAt (diffeomorphism point)).comp
          (diffeomorphismDerivative period hPeriod diffeomorphism point).toContinuousLinearMap)
  regularBasis : ∀ point,
    regularMetricBasisAt period hPeriod target.plusGravity.metric point =
      (regularMetricBasisAt period hPeriod source.plusGravity.metric
        (diffeomorphism point)).map
          (diffeomorphismDerivative period hPeriod diffeomorphism point).toLinearEquiv.symm

/-- The geometric transport certificate gives exactly the smooth density
identity required by the integrated interaction-block theorem. -/
theorem globalCandidateAInteractionDensity_pullback
    {sourceConfiguration targetConfiguration :
      GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (diffeomorphism :
      P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D.SpacetimeDiffeomorphism
        period hPeriod)
    (source :
      GlobalCandidateAActionData period hPeriod sourceConfiguration couplings
        NonNullFace NullFace)
    (target :
      GlobalCandidateAActionData period hPeriod targetConfiguration couplings
        NonNullFace NullFace)
    (transport :
      GlobalCandidateAInteractionDiffeomorphismGeometryTransport period hPeriod
        diffeomorphism source target) :
    target.interactionDensity =
      P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D.pullbackSmoothField
        period hPeriod Real diffeomorphism source.interactionDensity := by
  ext point
  rw [target.interactionDensity_eq point]
  simp only [
    P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D.pullbackSmoothField_apply,
    source.interactionDensity_eq (diffeomorphism point),
    transport.regularBasis point]
  exact globalCandidateAInteractionDensityAt_pullback period hPeriod
    sourceConfiguration.geometry targetConfiguration.geometry
    (diffeomorphismDerivative period hPeriod diffeomorphism point)
    (regularMetricBasisAt period hPeriod source.plusGravity.metric
      (diffeomorphism point))
    (transport.plusMetricMusical point) (transport.rootAt point)
    couplings.interactionScale couplings.interactionCoefficients

end
end P0EFTJanusProgramPCandidateAInteractionDensityNaturality4D
end JanusFormal
