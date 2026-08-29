import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearizedEinsteinBianchiSymbol
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols

/-!
# Candidate-A diagonal diffeomorphism kinetic-adjoint bridge

The two Einstein--Hilbert coefficients already present in the covariant action
weight the two metric kinetic pairings.  The formal adjoint of the genuine
diagonal gauge generator with respect to that direct-sum pairing is therefore
the corresponding weighted sum of the two de Donder conditions.

This file proves that statement at the four-dimensional principal-symbol
level, constructs the resulting global smooth gauge condition and
Faddeev--Popov map, and proves the exact spatial ellipticity criterion.  It
does not identify the completed global adjoint domain or replace the remaining
Green--Stokes analysis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusLinearizedEinsteinBianchiSymbol
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

/-! ## Action-derived kinetic weights -/

/-- Coefficient multiplying one Einstein--Hilbert kinetic block in the
already defined covariant action. -/
def einsteinHilbertKineticWeight
    (couplings : EinsteinHilbertCouplings) : Real :=
  1 / (2 * couplings.gravitationalCoupling)

@[simp]
theorem einsteinHilbertKineticWeight_ne_zero
    (couplings : EinsteinHilbertCouplings) :
    einsteinHilbertKineticWeight couplings ≠ 0 := by
  exact div_ne_zero one_ne_zero
    (mul_ne_zero (by norm_num) couplings.gravitationalCoupling_ne_zero)

/-- Plus-sector kinetic weight read from the global Candidate-A action. -/
def candidateAPlusEinsteinKineticWeight
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  einsteinHilbertKineticWeight couplings.plusEinstein

/-- Minus-sector kinetic weight read from the global Candidate-A action. -/
def candidateAMinusEinsteinKineticWeight
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  einsteinHilbertKineticWeight couplings.minusEinstein

@[simp]
theorem candidateAPlusEinsteinKineticWeight_ne_zero
    (couplings : GlobalCandidateAActionCouplings) :
    candidateAPlusEinsteinKineticWeight couplings ≠ 0 :=
  einsteinHilbertKineticWeight_ne_zero couplings.plusEinstein

@[simp]
theorem candidateAMinusEinsteinKineticWeight_ne_zero
    (couplings : GlobalCandidateAActionCouplings) :
    candidateAMinusEinsteinKineticWeight couplings ≠ 0 :=
  einsteinHilbertKineticWeight_ne_zero couplings.minusEinstein

theorem candidateAEinsteinKineticWeights_eq_of_couplings_eq
    (couplings : GlobalCandidateAActionCouplings)
    (hEqual : couplings.plusEinstein.gravitationalCoupling =
      couplings.minusEinstein.gravitationalCoupling) :
    candidateAPlusEinsteinKineticWeight couplings =
      candidateAMinusEinsteinKineticWeight couplings := by
  simp [candidateAPlusEinsteinKineticWeight,
    candidateAMinusEinsteinKineticWeight,
    einsteinHilbertKineticWeight, hEqual]

/-! ## Four-dimensional kinetic-adjoint identity -/

/-- Lorentzian pairing of two covectors in the fixed principal-symbol chart. -/
def minkowskiCovectorPairing
    (first second : Covector4) : Real :=
  Finset.univ.sum fun index =>
    etaSign index * first index * second index

/-- Full contraction of two symmetric covariant perturbations. -/
def minkowskiSymmetricTensorPairing
    (first second : SymmetricPerturbation) : Real :=
  Finset.univ.sum fun row =>
    Finset.univ.sum fun column =>
      etaSign row * etaSign column *
        first.tensor row column * second.tensor row column

/-- DeWitt pairing whose gauge-generator adjoint is de Donder. -/
def einsteinDeWittPairing
    (first second : SymmetricPerturbation) : Real :=
  minkowskiSymmetricTensorPairing first second -
    (1 / 2 : Real) * minkowskiTrace first * minkowskiTrace second

/-- Four-dimensional de Donder principal symbol. -/
def linearizedDeDonderSymbol
    (covector : Covector4) (perturbation : SymmetricPerturbation) :
    Covector4 :=
  fun index => momentumContraction covector perturbation index -
    (1 / 2 : Real) * covector index * minkowskiTrace perturbation

/-- Exact formal-adjoint identity for one Einstein kinetic block. -/
theorem einsteinDeWitt_pureGauge_adjoint
    (covector gaugeParameter : Covector4)
    (perturbation : SymmetricPerturbation) :
    einsteinDeWittPairing
        (pureGaugePerturbation covector gaugeParameter) perturbation =
      2 * minkowskiCovectorPairing gaugeParameter
        (linearizedDeDonderSymbol covector perturbation) := by
  have h01 := perturbation.apply_comm 0 1
  have h02 := perturbation.apply_comm 0 2
  have h03 := perturbation.apply_comm 0 3
  have h12 := perturbation.apply_comm 1 2
  have h13 := perturbation.apply_comm 1 3
  have h23 := perturbation.apply_comm 2 3
  simp [einsteinDeWittPairing, minkowskiSymmetricTensorPairing,
    minkowskiCovectorPairing, linearizedDeDonderSymbol,
    momentumContraction, minkowskiTrace, pureGaugePerturbation_apply,
    raiseCovector, etaSign, sum_fin_four]
  rw [h01, h02, h03, h12, h13, h23]
  ring

/-- Einstein-weighted direct-sum pairing of the diagonal generator with the
two Candidate-A perturbations. -/
def candidateADiagonalKineticPairing
    (couplings : GlobalCandidateAActionCouplings)
    (covector gaugeParameter : Covector4)
    (plusPerturbation minusPerturbation : SymmetricPerturbation) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      einsteinDeWittPairing
        (pureGaugePerturbation covector gaugeParameter) plusPerturbation +
    candidateAMinusEinsteinKineticWeight couplings *
      einsteinDeWittPairing
        (pureGaugePerturbation covector gaugeParameter) minusPerturbation

/-- The single de Donder condition selected by the kinetic adjoint. -/
def candidateADiagonalKineticDeDonderSymbol
    (couplings : GlobalCandidateAActionCouplings)
    (covector : Covector4)
    (plusPerturbation minusPerturbation : SymmetricPerturbation) : Covector4 :=
  fun index =>
    candidateAPlusEinsteinKineticWeight couplings *
        linearizedDeDonderSymbol covector plusPerturbation index +
      candidateAMinusEinsteinKineticWeight couplings *
        linearizedDeDonderSymbol covector minusPerturbation index

/-- The action coefficients and the diagonal generator force the weighted
de Donder sum as their formal adjoint. -/
theorem candidateADiagonalKineticPairing_adjoint
    (couplings : GlobalCandidateAActionCouplings)
    (covector gaugeParameter : Covector4)
    (plusPerturbation minusPerturbation : SymmetricPerturbation) :
    candidateADiagonalKineticPairing couplings covector gaugeParameter
        plusPerturbation minusPerturbation =
      2 * minkowskiCovectorPairing gaugeParameter
        (candidateADiagonalKineticDeDonderSymbol couplings covector
          plusPerturbation minusPerturbation) := by
  rw [candidateADiagonalKineticPairing,
    einsteinDeWitt_pureGauge_adjoint,
    einsteinDeWitt_pureGauge_adjoint]
  simp [minkowskiCovectorPairing,
    candidateADiagonalKineticDeDonderSymbol, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- No different scalar weights can represent the same kinetic adjoint on all
two-sector gauge-condition components. -/
theorem candidateADiagonalKineticWeights_unique
    (couplings : GlobalCandidateAActionCouplings)
    (plusWeight minusWeight : Real)
    (hAdjoint : ∀ plusCondition minusCondition : Real,
      plusWeight * plusCondition + minusWeight * minusCondition =
        candidateAPlusEinsteinKineticWeight couplings * plusCondition +
          candidateAMinusEinsteinKineticWeight couplings * minusCondition) :
    plusWeight = candidateAPlusEinsteinKineticWeight couplings /\
      minusWeight = candidateAMinusEinsteinKineticWeight couplings := by
  constructor
  · simpa using hAdjoint 1 0
  · simpa using hAdjoint 0 1

/-! ## Global smooth operator selected by the same weights -/

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev deDonderBackground :=
  generalMetricDivergenceBackground period hPeriod

/-- Genuine diagonal diffeomorphism generator on the two metric sectors. -/
def globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod where
  toFun := fun ghost sector =>
    globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod (metric sector) ghost
  map_add' first second := by
    funext sector
    exact (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod (metric sector)).map_add first second
  map_smul' scalar ghost := by
    funext sector
    exact (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod (metric sector)).map_smul scalar ghost

@[simp]
theorem globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (sector : Sector) :
    globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric ghost sector =
      globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod (metric sector) ghost :=
  rfl

/-- Global weighted sum of the two genuine de Donder conditions. -/
def globalCandidateADiagonalKineticGaugeConditionLinearMap
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod) where
  toFun := fun perturbation =>
    candidateAPlusEinsteinKineticWeight couplings •
        globalGeneralMetricDeDonderLinearMap
          period hPeriod (metric .plus) (perturbation .plus) +
      candidateAMinusEinsteinKineticWeight couplings •
        globalGeneralMetricDeDonderLinearMap
          period hPeriod (metric .minus) (perturbation .minus)
  map_add' first second := by
    simp only [Pi.add_apply, map_add]
    module
  map_smul' scalar perturbation := by
    change
      candidateAPlusEinsteinKineticWeight couplings •
          globalGeneralMetricDeDonderLinearMap period hPeriod (metric .plus)
            (scalar • perturbation .plus) +
        candidateAMinusEinsteinKineticWeight couplings •
          globalGeneralMetricDeDonderLinearMap period hPeriod (metric .minus)
            (scalar • perturbation .minus) =
      scalar •
        (candidateAPlusEinsteinKineticWeight couplings •
            globalGeneralMetricDeDonderLinearMap period hPeriod (metric .plus)
              (perturbation .plus) +
          candidateAMinusEinsteinKineticWeight couplings •
            globalGeneralMetricDeDonderLinearMap period hPeriod (metric .minus)
              (perturbation .minus))
    rw [(globalGeneralMetricDeDonderLinearMap
      period hPeriod (metric .plus)).map_smul,
      (globalGeneralMetricDeDonderLinearMap
        period hPeriod (metric .minus)).map_smul]
    module

@[simp]
theorem globalCandidateADiagonalKineticGaugeConditionLinearMap_apply
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod) :
    globalCandidateADiagonalKineticGaugeConditionLinearMap
        period hPeriod couplings metric perturbation =
      candidateAPlusEinsteinKineticWeight couplings •
          globalGeneralMetricDeDonder period hPeriod
            (metric .plus) (perturbation .plus) +
        candidateAMinusEinsteinKineticWeight couplings •
          globalGeneralMetricDeDonder period hPeriod
            (metric .minus) (perturbation .minus) :=
  rfl

/-- The single global FP operator obtained by composing the kinetic-adjoint
condition with the genuine diagonal generator. -/
def globalCandidateADiagonalKineticFaddeevPopovLinearMap
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod) :=
  (globalCandidateADiagonalKineticGaugeConditionLinearMap
      period hPeriod couplings metric).comp
    (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod metric)

@[simp]
theorem globalCandidateADiagonalKineticFaddeevPopovLinearMap_apply
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    globalCandidateADiagonalKineticFaddeevPopovLinearMap
        period hPeriod couplings metric ghost =
      candidateAPlusEinsteinKineticWeight couplings •
          globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
            period hPeriod (metric .plus) ghost +
        candidateAMinusEinsteinKineticWeight couplings •
          globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
            period hPeriod (metric .minus) ghost :=
  rfl

/-! ## Spatial principal-symbol criterion -/

/-- Spatial symbol of the selected diagonal FP operator. -/
def candidateADiagonalKineticFaddeevPopovSpatialSymbol
    (couplings : GlobalCandidateAActionCouplings)
    (covector ghost : TangentVector3) : TangentVector3 :=
  addTangent
    (scaleTangent (candidateAPlusEinsteinKineticWeight couplings)
      (deDonderSymbol covector (symGradientSymbol covector ghost)))
    (scaleTangent (candidateAMinusEinsteinKineticWeight couplings)
      (deDonderSymbol covector (symGradientSymbol covector ghost)))

theorem candidateADiagonalKineticFaddeevPopovSpatialSymbol_eq
    (couplings : GlobalCandidateAActionCouplings)
    (covector ghost : TangentVector3) :
    candidateADiagonalKineticFaddeevPopovSpatialSymbol
        couplings covector ghost =
      scaleTangent
        ((candidateAPlusEinsteinKineticWeight couplings +
            candidateAMinusEinsteinKineticWeight couplings) *
          normSquared covector) ghost := by
  rw [candidateADiagonalKineticFaddeevPopovSpatialSymbol,
    de_donder_sym_gradient]
  ext <;> simp [addTangent, scaleTangent] <;> ring

/-- Cancellation of the two action-derived weights annihilates the selected
diagonal FP principal symbol. -/
theorem candidateADiagonalKineticFaddeevPopovSpatialSymbol_eq_zero_of_totalWeight_eq_zero
    (couplings : GlobalCandidateAActionCouplings)
    (covector ghost : TangentVector3)
    (hTotalWeight : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0) :
    candidateADiagonalKineticFaddeevPopovSpatialSymbol
      couplings covector ghost = zeroTangent := by
  rw [candidateADiagonalKineticFaddeevPopovSpatialSymbol_eq, hTotalWeight]
  simp [scaleTangent, zeroTangent]

/-- Away from cancellation of the two action-derived kinetic weights, the
selected diagonal FP symbol is elliptic. -/
theorem candidateADiagonalKineticFaddeevPopovSpatialSymbol_kernel_trivial
    (couplings : GlobalCandidateAActionCouplings)
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (hTotalWeight : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings ≠ 0)
    (ghost : TangentVector3)
    (hKernel : candidateADiagonalKineticFaddeevPopovSpatialSymbol
      couplings covector ghost = zeroTangent) :
    ghost = zeroTangent := by
  rw [candidateADiagonalKineticFaddeevPopovSpatialSymbol_eq] at hKernel
  exact scale_tangent_eq_zero
    ((candidateAPlusEinsteinKineticWeight couplings +
        candidateAMinusEinsteinKineticWeight couplings) *
      normSquared covector)
    (mul_ne_zero hTotalWeight
      (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)))
    ghost hKernel

end

end P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
end JanusFormal
