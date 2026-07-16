import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiRelativeRootOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiInteractionDensityVariation4D

/-!
# Candidate-A variation on the explicit Minkowski root domain

The inverse-function square-root chart is differentiated at every point of
its explicit target.  The key step recovers Sylvester invertibility throughout
the chart source from the uniform `ApproximatesLinearOn` estimate used to
construct `localSquareChart`; the derivative of its `symm` is then composed
with the genuine relative-metric map.

Consequently the determinant measure, matrix spectral potential, and complete
Candidate-A density have actual Frechet derivatives at every point of
`minkowskiRelativeRootOpenDomain`.  No extra determinant subdomain is needed:
invertibility of `gPlus` is already part of that domain.  A PT-safe open
subdomain additionally requires the exchanged metric pair to belong to the
same chart and carries a differentiable two-sector exchange-invariant sum.

This is a finite-dimensional local identity-component chart, not a global
Lorentzian principal-root theorem or a spacetime functional variation.
-/

namespace JanusFormal
namespace P0EFTJanusMinkowskiInteractionDensityOpenDomain4D

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology NNReal
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMetricInverseRelativeRootFrechet
open P0EFTJanusMinkowskiRelativeRootBranch4D
open P0EFTJanusMinkowskiRelativeRootOpenDomain4D
open P0EFTJanusMinkowskiInteractionDensityVariation4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

abbrev Matrix4 := P0EFTJanusLorentzLocalRootBranch4D.Matrix4
abbrev MetricPair := P0EFTJanusMinkowskiRelativeRootBranch4D.MetricPair

attribute [local instance]
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4AddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4TopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4Module
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairTopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairModule

abbrev OpenPairScalarHasFDerivAt
    (function : MetricPair → Real)
    (derivative : MetricPair →L[Real] Real)
    (point : MetricPair) : Prop :=
  @HasFDerivAt Real _ MetricPair
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toAddCommGroup
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace.toModule
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Real Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function derivative point

theorem identityRootSource_approximates :
    ApproximatesLinearOn matrixSquare
      (twiceEquiv : Matrix4 →L[Real] Matrix4) identityRootSource
      (‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖₊⁻¹ / 2) := by
  unfold identityRootSource localSquareChart
  exact (Classical.choose_spec
    (matrixSquare_hasStrictFDerivAt_equiv (1 : Matrix4)
      identitySylvesterWitness).approximates_deriv_on_open_nhds).2.2

theorem sylvester_sub_twice_norm_le
    {root : Matrix4} (hRoot : root ∈ identityRootSource) :
    ‖sylvesterMap root - (twiceEquiv : Matrix4 →L[Real] Matrix4)‖ ≤
      (‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖₊⁻¹ / 2 : NNReal) := by
  have hNeighbourhood : identityRootSource ∈ 𝓝 root :=
    identityRootSource_isOpen.mem_nhds hRoot
  have hLipschitz := identityRootSource_approximates.lipschitzOnWith
  have hBound := norm_fderiv_le_of_lipschitzOn Real hNeighbourhood hLipschitz
  have hResidual := (matrixSquare_hasStrictFDerivAt root).hasFDerivAt.sub
    (twiceEquiv : Matrix4 →L[Real] Matrix4).hasFDerivAt
  rw [hResidual.fderiv] at hBound
  exact hBound

def sylvesterCorrection (root : Matrix4) : Matrix4 →L[Real] Matrix4 :=
  (twiceEquiv.symm : Matrix4 →L[Real] Matrix4).comp
    (sylvesterMap root - (twiceEquiv : Matrix4 →L[Real] Matrix4))

theorem sylvesterCorrection_norm_lt_one
    {root : Matrix4} (hRoot : root ∈ identityRootSource) :
    ‖sylvesterCorrection root‖ < 1 := by
  have hN : 0 < ‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖ :=
    ContinuousLinearEquiv.nnnorm_symm_pos twiceEquiv
  calc
    ‖sylvesterCorrection root‖ ≤
        ‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖ *
          ‖sylvesterMap root - (twiceEquiv : Matrix4 →L[Real] Matrix4)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖ *
          (‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖₊⁻¹ / 2 : NNReal) :=
      mul_le_mul_of_nonneg_left (sylvester_sub_twice_norm_le hRoot)
        (norm_nonneg _)
    _ = (1 / 2 : Real) := by
      rw [NNReal.coe_div, NNReal.coe_inv]
      change ‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖ *
        (‖(twiceEquiv.symm : Matrix4 →L[Real] Matrix4)‖⁻¹ / 2) = 1 / 2
      field_simp [hN.ne']
    _ < 1 := by norm_num

theorem sylvesterMap_isUnit_on_identityRootSource
    {root : Matrix4} (hRoot : root ∈ identityRootSource) :
    IsUnit (sylvesterMap root) := by
  have hCorrection : IsUnit (1 + sylvesterCorrection root) := by
    have h := isUnit_one_sub_of_norm_lt_one
      (x := -sylvesterCorrection root) (by
        simpa using sylvesterCorrection_norm_lt_one hRoot)
    simpa only [sub_neg_eq_add] using h
  have hTwice : IsUnit (twiceEquiv : Matrix4 →L[Real] Matrix4) :=
    ⟨ContinuousLinearEquiv.toUnit twiceEquiv, rfl⟩
  have hFactor :
      sylvesterMap root =
        (twiceEquiv : Matrix4 →L[Real] Matrix4) *
          (1 + sylvesterCorrection root) := by
    apply ContinuousLinearMap.ext
    intro variation
    change sylvesterMap root variation =
      twiceEquiv (variation + twiceEquiv.symm
        (sylvesterMap root variation - twiceEquiv variation))
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
    abel
  rw [hFactor]
  exact hTwice.mul hCorrection

noncomputable def sylvesterWitnessOnIdentityRootSource
    (root : Matrix4) (hRoot : root ∈ identityRootSource) :
    SylvesterEquivWitness root := by
  let hUnit := sylvesterMap_isUnit_on_identityRootSource hRoot
  exact
    { equiv := ContinuousLinearEquiv.ofUnit hUnit.unit
      forward_eq := by
        change (↑hUnit.unit : Matrix4 →L[Real] Matrix4) = sylvesterMap root
        exact hUnit.unit_spec }

def openDomainRootDerivative
    (input : MetricPair) (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    MetricPair →L[Real] Matrix4 :=
  ((sylvesterWitnessOnIdentityRootSource
      (minkowskiRelativeRootBranch input)
      (minkowskiRelativeRootBranch_mem_source hInput)).equiv.symm :
      Matrix4 →L[Real] Matrix4).comp
    (frobeniusRelativeMetricDerivative input)

theorem minkowskiRelativeRootBranch_eq_chartSymm :
    minkowskiRelativeRootBranch =
      (localSquareChart (1 : Matrix4) identitySylvesterWitness).symm ∘
        relativeMetricTarget :=
  rfl

theorem minkowskiRelativeRootChart_hasFDerivAt_on_openDomain
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    HasFDerivAt
      ((localSquareChart (1 : Matrix4) identitySylvesterWitness).symm ∘
        relativeMetricTarget)
      (openDomainRootDerivative input hInput) input := by
  let chart := localSquareChart (1 : Matrix4) identitySylvesterWitness
  let target := relativeMetricTarget input
  have hTarget : target ∈ chart.target := hInput.2
  let witness := sylvesterWitnessOnIdentityRootSource
    (minkowskiRelativeRootBranch input)
    (minkowskiRelativeRootBranch_mem_source hInput)
  have hForward : HasFDerivAt chart
      (witness.equiv : Matrix4 →L[Real] Matrix4)
      (minkowskiRelativeRootBranch input) := by
    exact (matrixSquare_hasStrictFDerivAt_equiv
      (minkowskiRelativeRootBranch input) witness).hasFDerivAt
  have hOuter := chart.hasFDerivAt_symm hTarget hForward
  have hInner := relativeMetricTarget_hasFDerivAt_frobenius input hInput.1
  have hComposite := hOuter.comp input hInner
  simpa only [openDomainRootDerivative, chart, target, witness,
    minkowskiRelativeRootBranch, identityLocalRootBranch, localRootBranch,
    HasStrictFDerivAt.localInverse_def] using hComposite

theorem minkowskiRelativeRootBranch_differentiableAt_on_openDomain
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    DifferentiableAt Real minkowskiRelativeRootBranch input := by
  rw [minkowskiRelativeRootBranch_eq_chartSymm]
  exact
    (minkowskiRelativeRootChart_hasFDerivAt_on_openDomain hInput).differentiableAt

def openDomainPlusVolumeDerivative
    (input : MetricPair) : MetricPair →L[Real] Real :=
  (1 / (2 * Real.sqrt |Matrix.det input.1|)) •
    ((SignType.sign (Matrix.det input.1) : Real) •
      ((determinantDerivative input.1).comp
        (ContinuousLinearMap.fst Real Matrix4 Matrix4)))

theorem plus_det_ne_zero_on_openDomain
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    Matrix.det input.1 ≠ 0 := by
  have hPlus : IsUnit input.1 := hInput.1
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det input.1).mp hPlus)

theorem minkowskiPlusVolume_hasFDerivAt_on_openDomain
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    OpenPairScalarHasFDerivAt minkowskiPlusVolume
      (openDomainPlusVolumeDerivative input) input := by
  have hProjection : HasFDerivAt (fun pair : MetricPair => pair.1)
      (ContinuousLinearMap.fst Real Matrix4 Matrix4) input :=
    (ContinuousLinearMap.fst Real Matrix4 Matrix4).hasFDerivAt
  have hDeterminant := determinant_hasFDerivAt input.1
  unfold FrobeniusHasFDerivAt at hDeterminant
  have hDeterminantPair := hDeterminant.comp input hProjection
  have hNonzero := plus_det_ne_zero_on_openDomain hInput
  exact (hDeterminantPair.abs hNonzero).sqrt (abs_ne_zero.mpr hNonzero)

def openDomainRootPotentialDerivative
    (coefficients : PotentialCoefficients) (input : MetricPair)
    (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    MetricPair →L[Real] Real :=
  (matrixSpectralPotentialDerivative coefficients
      (minkowskiRelativeRootBranch input)).comp
    (openDomainRootDerivative input hInput)

theorem minkowskiRootPotential_hasFDerivAt_on_openDomain
    (coefficients : PotentialCoefficients) {input : MetricPair}
    (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    OpenPairScalarHasFDerivAt (minkowskiRootPotential coefficients)
      (openDomainRootPotentialDerivative coefficients input hInput) input := by
  have hPotential := matrixSpectralPotential_hasFDerivAt coefficients
    (minkowskiRelativeRootBranch input)
  unfold FrobeniusHasFDerivAt at hPotential
  have hRoot := minkowskiRelativeRootChart_hasFDerivAt_on_openDomain hInput
  have hComposite := hPotential.comp input hRoot
  unfold OpenPairScalarHasFDerivAt minkowskiRootPotential
    openDomainRootPotentialDerivative
  exact hComposite

def openDomainCandidateADerivative
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    MetricPair →L[Real] Real :=
  (-interactionScale * minkowskiPlusVolume input) •
      openDomainRootPotentialDerivative coefficients input hInput +
    minkowskiRootPotential coefficients input •
      ((-interactionScale) • openDomainPlusVolumeDerivative input)

theorem minkowskiCandidateAInteractionDensity_hasFDerivAt_on_openDomain
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    OpenPairScalarHasFDerivAt
      (minkowskiCandidateAInteractionDensity interactionScale coefficients)
      (openDomainCandidateADerivative interactionScale coefficients input hInput)
      input := by
  exact
    ((minkowskiPlusVolume_hasFDerivAt_on_openDomain hInput).const_mul
      (-interactionScale)).mul
      (minkowskiRootPotential_hasFDerivAt_on_openDomain coefficients hInput)

/-- Continuous exchange of the two independent metric slots. -/
def metricPairExchange : MetricPair ≃L[Real] MetricPair :=
  ContinuousLinearEquiv.prodComm Real Matrix4 Matrix4

@[simp] theorem metricPairExchange_apply (input : MetricPair) :
    metricPairExchange input = (input.2, input.1) :=
  rfl

@[simp] theorem metricPairExchange_involutive (input : MetricPair) :
    metricPairExchange (metricPairExchange input) = input := by
  rcases input with ⟨plus, minus⟩
  rfl

/-- PT-safe part of the chart: both metric orderings belong to the explicit
root domain. -/
def ptPairedRootOpenDomain : Set MetricPair :=
  minkowskiRelativeRootOpenDomain ∩
    metricPairExchange ⁻¹' minkowskiRelativeRootOpenDomain

theorem ptPairedRootOpenDomain_isOpen : IsOpen ptPairedRootOpenDomain := by
  exact minkowskiRelativeRootOpenDomain_isOpen.inter
    (minkowskiRelativeRootOpenDomain_isOpen.preimage
      metricPairExchange.continuous)

theorem minkowskiMetricPair_mem_ptPairedRootOpenDomain :
    minkowskiMetricPair ∈ ptPairedRootOpenDomain := by
  refine ⟨minkowskiMetricPair_mem_openDomain, ?_⟩
  simpa [metricPairExchange, minkowskiMetricPair] using
    minkowskiMetricPair_mem_openDomain

theorem ptPairedRootOpenDomain_exchange_iff (input : MetricPair) :
    metricPairExchange input ∈ ptPairedRootOpenDomain ↔
      input ∈ ptPairedRootOpenDomain := by
  simp only [ptPairedRootOpenDomain, Set.mem_inter_iff, Set.mem_preimage,
    metricPairExchange_involutive]
  exact and_comm

/-- Candidate-A density whose plus slot is the exchanged minus metric. -/
def exchangedCandidateAInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) : Real :=
  minkowskiCandidateAInteractionDensity interactionScale coefficients
    (metricPairExchange input)

def exchangedCandidateADerivative
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) (hInput : input ∈ ptPairedRootOpenDomain) :
    MetricPair →L[Real] Real :=
  (openDomainCandidateADerivative interactionScale coefficients
      (metricPairExchange input) hInput.2).comp
    (metricPairExchange : MetricPair →L[Real] MetricPair)

theorem exchangedCandidateAInteractionDensity_hasFDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    {input : MetricPair} (hInput : input ∈ ptPairedRootOpenDomain) :
    OpenPairScalarHasFDerivAt
      (exchangedCandidateAInteractionDensity interactionScale coefficients)
      (exchangedCandidateADerivative interactionScale coefficients input hInput)
      input := by
  have hOuter :=
    minkowskiCandidateAInteractionDensity_hasFDerivAt_on_openDomain
      interactionScale coefficients hInput.2
  have hComposite := hOuter.comp input
    (metricPairExchange : MetricPair →L[Real] MetricPair).hasFDerivAt
  unfold OpenPairScalarHasFDerivAt exchangedCandidateAInteractionDensity
    exchangedCandidateADerivative
  exact hComposite

/-- Sum of the two exchanged Candidate-A sectors with common coefficients. -/
def ptPairedCandidateAInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) : Real :=
  minkowskiCandidateAInteractionDensity interactionScale coefficients input +
    exchangedCandidateAInteractionDensity interactionScale coefficients input

def ptPairedCandidateADerivative
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) (hInput : input ∈ ptPairedRootOpenDomain) :
    MetricPair →L[Real] Real :=
  openDomainCandidateADerivative interactionScale coefficients input hInput.1 +
    exchangedCandidateADerivative interactionScale coefficients input hInput

theorem ptPairedCandidateAInteractionDensity_hasFDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    {input : MetricPair} (hInput : input ∈ ptPairedRootOpenDomain) :
    OpenPairScalarHasFDerivAt
      (ptPairedCandidateAInteractionDensity interactionScale coefficients)
      (ptPairedCandidateADerivative interactionScale coefficients input hInput)
      input := by
  have hPlus :=
    minkowskiCandidateAInteractionDensity_hasFDerivAt_on_openDomain
      interactionScale coefficients hInput.1
  have hMinus := exchangedCandidateAInteractionDensity_hasFDerivAt
    interactionScale coefficients hInput
  unfold OpenPairScalarHasFDerivAt at hPlus hMinus ⊢
  unfold ptPairedCandidateAInteractionDensity ptPairedCandidateADerivative
  exact hPlus.add hMinus

theorem ptPairedCandidateAInteractionDensity_exchange
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : MetricPair) :
    ptPairedCandidateAInteractionDensity interactionScale coefficients
        (metricPairExchange input) =
      ptPairedCandidateAInteractionDensity interactionScale coefficients input := by
  simp only [ptPairedCandidateAInteractionDensity,
    exchangedCandidateAInteractionDensity, metricPairExchange_involutive]
  exact add_comm _ _

end
end P0EFTJanusMinkowskiInteractionDensityOpenDomain4D
end JanusFormal
