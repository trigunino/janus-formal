import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

/-!
# Exact Riemann tensor of a smooth varied metric

The exact smooth Christoffel coefficient and derivative bridges reconstruct
the intrinsic local Riemann vector of the genuine affine metric.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothRiemann4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Reconstruct the genuine varied Levi--Civita derivative from its completed
regular-frame Christoffel coefficients. -/
theorem regularGeneralMetricC0Christoffel_smooth_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    (∑ upper : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          upper first second (patch.coordinateMap coordinate) •
        pulledRegularFrameVector period hPeriod metric patch upper coordinate) =
      candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
        period hPeriod metric variedMetric patch first second coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch first second coordinate
  simp_rw [regularGeneralMetricC0Christoffel_smooth_apply period hPeriod metric
    tensor variedMetric hVaried hVariation patch coordinate]
  calc
    (∑ upper : Fin 4,
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
          connection upper •
        pulledRegularFrameVector period hPeriod metric patch upper coordinate) =
        ∑ upper : Fin 4, basis.repr connection upper • basis upper := by
      apply Finset.sum_congr rfl
      intro upper _
      congr 1
      exact (pulledRegularFrameBasis_apply period hPeriod metric patch
        coordinate upper).symm
    _ = connection := basis.sum_repr connection

private theorem fderiv_variedRegularFrameLocalCovariantDerivative_reconstruction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    fderiv Real
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second)
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
        ∑ upper : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              upper first second (patch.coordinateMap coordinate) •
            fderiv Real
              (pulledRegularFrameVector period hPeriod metric patch upper)
              coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let coefficient (upper : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0Christoffel period hPeriod metric variation upper
      first second (patch.coordinateMap current)
  let frame (upper : Fin 4) : CoordinateVector → CoordinateVector :=
    pulledRegularFrameVector period hPeriod metric patch upper
  let term (upper : Fin 4) : CoordinateVector → CoordinateVector := fun current =>
    coefficient upper current • frame upper current
  have hCoefficient (upper : Fin 4) :
      DifferentiableAt Real (coefficient upper) coordinate :=
    regularGeneralMetricC0Christoffel_smooth_local_differentiableAt period
      hPeriod metric tensor hVariation patch coordinate upper first second
  have hFrame (upper : Fin 4) :
      DifferentiableAt Real (frame upper) coordinate :=
    pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate upper
  have hTerm (upper : Fin 4) :
      DifferentiableAt Real (term upper) coordinate :=
    (hCoefficient upper).smul (hFrame upper)
  have hTermDerivative (upper : Fin 4) :
      fderiv Real (term upper) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        coefficient upper coordinate •
            fderiv Real (frame upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) +
          fderiv Real (coefficient upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) • frame upper coordinate := by
    have hProduct := fderiv_smul (hCoefficient upper) (hFrame upper)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hProduct
    change fderiv Real (coefficient upper • frame upper) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hFunction :
      candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second =
        fun current => ∑ upper : Fin 4, term upper current := by
    funext current
    exact (regularGeneralMetricC0Christoffel_smooth_reconstructs period hPeriod
      metric tensor variedMetric hVaried hVariation patch current first
        second).symm
  rw [hFunction]
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun upper _ => hTerm upper)
  have hApplied := congrArg
    (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
      derivativeMap
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) hSum
  rw [hApplied]
  simp only [sum_apply]
  calc
    (∑ upper : Fin 4,
      fderiv Real (term upper) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) =
        ∑ upper : Fin 4,
          (coefficient upper coordinate •
              fderiv Real (frame upper) coordinate
                (pulledRegularFrameVector period hPeriod metric patch derivative
                  coordinate) +
            fderiv Real (coefficient upper) coordinate
                (pulledRegularFrameVector period hPeriod metric patch derivative
                  coordinate) • frame upper coordinate) := by
      apply Finset.sum_congr rfl
      intro upper _
      exact hTermDerivative upper
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [show ∀ upper : Fin 4,
          fderiv Real (coefficient upper) coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) =
            regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
              variation derivative upper first second
                (patch.coordinateMap coordinate) by
        intro upper
        exact regularGeneralMetricC0Christoffel_smooth_local_fderiv period
          hPeriod metric tensor hVariation patch coordinate derivative upper
            first second]
      dsimp only [coefficient, frame]
      abel

private theorem regularFrameSmoothChristoffelProduct_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                  metric.metric tensor)
                contracted first second (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                  metric.metric tensor)
                upper derivative contracted (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      ∑ contracted : Fin 4,
        regularGeneralMetricC0Christoffel period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              contracted first second (patch.coordinateMap coordinate) •
          candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch derivative contracted
              coordinate := by
  simp_rw [← regularGeneralMetricC0Christoffel_smooth_reconstructs period
    hPeriod metric tensor variedMetric hVaried hVariation patch coordinate
      derivative]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem regularFrameSmoothSecondCovariantDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second : Fin 4) :
    (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
        (∑ upper : Fin 4,
          (∑ contracted : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod metric
                  (smoothToGeneralMetricRelativeC2Core period hPeriod
                    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                    metric.metric tensor)
                  contracted first second (patch.coordinateMap coordinate) *
              regularGeneralMetricC0Christoffel period hPeriod metric
                  (smoothToGeneralMetricRelativeC2Core period hPeriod
                    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                    metric.metric tensor)
                  upper derivative contracted (patch.coordinateMap coordinate)) •
            pulledRegularFrameVector period hPeriod metric patch upper
              coordinate) =
      localCovariantDerivativeVectorField period hPeriod variedMetric patch
        (pulledRegularFrameVector period hPeriod metric patch derivative)
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second) coordinate := by
  unfold localCovariantDerivativeVectorField
  rw [fderiv_variedRegularFrameLocalCovariantDerivative_reconstruction period
    hPeriod metric tensor variedMetric hVaried hVariation patch coordinate
      derivative first second]
  rw [regularFrameSmoothChristoffelProduct_reconstructs period hPeriod metric
    tensor variedMetric hVaried hVariation patch coordinate derivative first
      second]
  rw [← regularGeneralMetricC0Christoffel_smooth_reconstructs period hPeriod
    metric tensor variedMetric hVaried hVariation patch coordinate first second]
  change _ =
    (∑ upper : Fin 4,
        regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            derivative upper first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) +
      (∑ contracted : Fin 4,
        regularGeneralMetricC0Christoffel period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              contracted first second (patch.coordinateMap coordinate) •
          fderiv Real
            (pulledRegularFrameVector period hPeriod metric patch contracted)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate)) +
      localLeviCivitaChristoffelBilinearMap period hPeriod variedMetric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)
        (∑ contracted : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                  metric.metric tensor)
                contracted first second (patch.coordinateMap coordinate) •
            pulledRegularFrameVector period hPeriod metric patch contracted
              coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector,
    smul_add]
  rw [Finset.sum_add_distrib]
  abel

private theorem regularFrameSmoothStructureChristoffelProduct_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
                contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                  metric.metric tensor)
                upper contracted lower (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch contracted lower
              coordinate := by
  simp_rw [← regularGeneralMetricC0Christoffel_smooth_reconstructs period
    hPeriod metric tensor variedMetric hVaried hVariation patch coordinate]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem
    regularFrameSmoothBracketCovariantDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    (∑ upper : Fin 4,
        (∑ contracted : Fin 4,
          regularFrameStructureCoefficient period hPeriod metric first second
                contracted (patch.coordinateMap coordinate) *
            regularGeneralMetricC0Christoffel period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                  metric.metric tensor)
                upper contracted lower (patch.coordinateMap coordinate)) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      localCovariantDerivativeVectorField period hPeriod variedMetric patch
        (VectorField.lieBracket Real
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch second))
        (pulledRegularFrameVector period hPeriod metric patch lower)
        coordinate := by
  rw [regularFrameSmoothStructureChristoffelProduct_reconstructs period hPeriod
    metric tensor variedMetric hVaried hVariation patch coordinate first second
      lower]
  unfold localCovariantDerivativeVectorField
  rw [regularFrameLocalLieBracket_eq_sum period hPeriod metric patch coordinate
    first second]
  rw [map_sum]
  change _ = _ +
    localLeviCivitaChristoffelBilinearMap period hPeriod variedMetric patch
      coordinate
      (∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch contracted
            coordinate)
      (pulledRegularFrameVector period hPeriod metric patch lower coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) •
        candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch contracted lower coordinate) =
    (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) •
        fderiv Real
          (pulledRegularFrameVector period hPeriod metric patch lower)
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch contracted
            coordinate)) +
      ∑ contracted : Fin 4,
        regularFrameStructureCoefficient period hPeriod metric first second
              contracted (patch.coordinateMap coordinate) •
          localLeviCivitaChristoffelApply period hPeriod variedMetric patch
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch contracted
              coordinate)
            (pulledRegularFrameVector period hPeriod metric patch lower
              coordinate)
  simp_rw [candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector,
    smul_add]
  rw [Finset.sum_add_distrib]

/-- The completed nonholonomic Riemann coefficients reconstruct the intrinsic
Riemann vector of the genuine smooth varied metric. -/
theorem regularGeneralMetricC0Riemann_smooth_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (lower first second : Fin 4) :
    (∑ upper : Fin 4,
        regularGeneralMetricC0Riemann period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              upper lower first second (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) =
      localLeviCivitaRiemannVector period hPeriod variedMetric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let frame (upper : Fin 4) :=
    pulledRegularFrameVector period hPeriod metric patch upper coordinate
  let firstDerivative := ∑ upper : Fin 4,
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric variation
        first upper second lower (patch.coordinateMap coordinate) • frame upper
  let secondDerivative := ∑ upper : Fin 4,
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric variation
        second upper first lower (patch.coordinateMap coordinate) • frame upper
  let firstProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric variation
            contracted second lower (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric variation upper
            first contracted (patch.coordinateMap coordinate)) • frame upper
  let secondProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularGeneralMetricC0Christoffel period hPeriod metric variation
            contracted first lower (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric variation upper
            second contracted (patch.coordinateMap coordinate)) • frame upper
  let bracketProduct := ∑ upper : Fin 4,
    (∑ contracted : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
            contracted (patch.coordinateMap coordinate) *
        regularGeneralMetricC0Christoffel period hPeriod metric variation upper
            contracted lower (patch.coordinateMap coordinate)) • frame upper
  have hExpansion :
      (∑ upper : Fin 4,
        regularGeneralMetricC0Riemann period hPeriod metric variation upper
              lower first second (patch.coordinateMap coordinate) • frame upper) =
        (firstDerivative + firstProduct) -
          (secondDerivative + secondProduct) - bracketProduct := by
    unfold regularGeneralMetricC0Riemann
    dsimp only [firstDerivative, secondDerivative, firstProduct, secondProduct,
      bracketProduct]
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      regularFrameStructureCoefficientContinuous_apply, sub_smul, add_smul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_smul]
    abel
  rw [hExpansion]
  have hFirstCovariant :
      firstDerivative + firstProduct =
        localCovariantDerivativeVectorField period hPeriod variedMetric patch
          (pulledRegularFrameVector period hPeriod metric patch first)
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch second lower) coordinate := by
    exact regularFrameSmoothSecondCovariantDerivative_reconstructs period
      hPeriod metric tensor variedMetric hVaried hVariation patch coordinate
        first second lower
  have hSecondCovariant :
      secondDerivative + secondProduct =
        localCovariantDerivativeVectorField period hPeriod variedMetric patch
          (pulledRegularFrameVector period hPeriod metric patch second)
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch first lower) coordinate := by
    exact regularFrameSmoothSecondCovariantDerivative_reconstructs period
      hPeriod metric tensor variedMetric hVaried hVariation patch coordinate
        second first lower
  have hBracketCovariant :
      bracketProduct =
        localCovariantDerivativeVectorField period hPeriod variedMetric patch
          (VectorField.lieBracket Real
            (pulledRegularFrameVector period hPeriod metric patch first)
            (pulledRegularFrameVector period hPeriod metric patch second))
          (pulledRegularFrameVector period hPeriod metric patch lower)
          coordinate := by
    exact regularFrameSmoothBracketCovariantDerivative_reconstructs period
      hPeriod metric tensor variedMetric hVaried hVariation patch coordinate
        first second lower
  rw [hFirstCovariant, hSecondCovariant, hBracketCovariant]
  have hFirstFunction :
      candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first lower =
        localCovariantDerivativeVectorField period hPeriod variedMetric patch
          (pulledRegularFrameVector period hPeriod metric patch first)
          (pulledRegularFrameVector period hPeriod metric patch lower) := rfl
  have hSecondFunction :
      candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch second lower =
        localCovariantDerivativeVectorField period hPeriod variedMetric patch
          (pulledRegularFrameVector period hPeriod metric patch second)
          (pulledRegularFrameVector period hPeriod metric patch lower) := rfl
  rw [hFirstFunction, hSecondFunction]
  exact localCovariantDerivativeVectorField_curvature period hPeriod variedMetric
    patch coordinate
    (pulledRegularFrameVector period hPeriod metric patch first)
    (pulledRegularFrameVector period hPeriod metric patch second)
    (pulledRegularFrameVector period hPeriod metric patch lower)
    (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate first)
    (pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate second)
    (pulledRegularFrameVector_contDiff period hPeriod metric patch lower)

/-- Component form of the exact smooth nonzero Riemann reconstruction. -/
theorem regularGeneralMetricC0Riemann_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper lower first second : Fin 4) :
    regularGeneralMetricC0Riemann period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        upper lower first second (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (localLeviCivitaRiemannVector period hPeriod variedMetric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch first
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate)) upper := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  have hReconstruction := congrArg (fun vector => basis.repr vector upper)
    (regularGeneralMetricC0Riemann_smooth_reconstructs period hPeriod metric
      tensor variedMetric hVaried hVariation patch coordinate lower first second)
  rw [map_sum] at hReconstruction
  simp_rw [map_smul] at hReconstruction
  change (∑ index : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            index lower first second (patch.coordinateMap coordinate) *
        basis.repr
          (pulledRegularFrameVector period hPeriod metric patch index
            coordinate) upper) =
    basis.repr
      (localLeviCivitaRiemannVector period hPeriod variedMetric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate))
      upper at hReconstruction
  have hCoordinate (index : Fin 4) :
      basis.repr
          (pulledRegularFrameVector period hPeriod metric patch index coordinate)
          upper = if index = upper then 1 else 0 := by
    rw [← pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      index]
    exact basis.repr_self_apply index upper
  simp_rw [hCoordinate] at hReconstruction
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hReconstruction

/-- Gate marker: the completed Riemann tensor is the intrinsic Riemann tensor
of every admissible smooth affine metric. -/
theorem regular_general_metric_c2_smooth_riemann_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper lower first second : Fin 4) :
    regularGeneralMetricC0Riemann period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        upper lower first second (patch.coordinateMap coordinate) =
      (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (localLeviCivitaRiemannVector period hPeriod variedMetric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch first
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch lower
            coordinate)) upper := by
  exact regularGeneralMetricC0Riemann_smooth_apply period hPeriod metric tensor
    variedMetric hVaried hVariation patch coordinate upper lower first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothRiemann4D
end JanusFormal
