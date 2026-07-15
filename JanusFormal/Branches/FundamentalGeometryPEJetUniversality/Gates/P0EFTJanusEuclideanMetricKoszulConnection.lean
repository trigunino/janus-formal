import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanImmersionConnectionJetExtraction

namespace JanusFormal
namespace P0EFTJanusEuclideanMetricKoszulConnection

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusEuclideanImmersionConnectionJetExtraction

universe u v y

/-- Continuous bilinear metric coefficient on one Euclidean model. -/
abbrev ContinuousMetricTensor
    (Model : Type u) [NormedAddCommGroup Model] [NormedSpace ℝ Model] :=
  Model →L[ℝ] Model →L[ℝ] ℝ

/-- Constant-coordinate Koszul right-hand side for a varying metric. -/
def metricKoszulRhs
    {Model : Type u}
    [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
    (metric : Model → ContinuousMetricTensor Model)
    (base first second test : Model) : ℝ :=
  fderiv ℝ metric base first second test +
    fderiv ℝ metric base second first test -
    fderiv ℝ metric base test first second

/-- Smooth Euclidean metric together with its uniquely characterized
Levi-Civita/Koszul connection coefficient.  The connection is bundled as a
continuous bilinear map and is constrained pointwise by the exact Koszul
identity, rather than supplied as an unrelated coefficient. -/
structure SmoothEuclideanKoszulConnectionData
    (Model : Type u)
    [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
    [FiniteDimensional ℝ Model] where
  metric : Model → ContinuousMetricTensor Model
  connection : Model → ContinuousTangentialQuadratic Model
  metric_contDiff : ContDiff ℝ ∞ metric
  connection_contDiff : ContDiff ℝ ∞ connection
  metric_symmetric :
    ∀ base first second,
      metric base first second = metric base second first
  metricDerivative_symmetric :
    ∀ base direction first second,
      fderiv ℝ metric base direction first second =
        fderiv ℝ metric base direction second first
  metric_nondegenerate :
    ∀ base left right,
      (∀ test, metric base left test = metric base right test) →
        left = right
  connection_koszul :
    ∀ base first second test,
      2 * metric base (connection base first second) test =
        metricKoszulRhs metric base first second test

variable {Model : Type u}
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [FiniteDimensional ℝ Model]

/-- The Koszul identity forces the supplied connection coefficient to be
symmetric in its two vector arguments. -/
theorem SmoothEuclideanKoszulConnectionData.connection_symmetric
    (data : SmoothEuclideanKoszulConnectionData Model) :
    ∀ base first second,
      data.connection base first second =
        data.connection base second first := by
  intro base first second
  apply data.metric_nondegenerate base
  intro test
  have hForward := data.connection_koszul base first second test
  have hReverse := data.connection_koszul base second first test
  dsimp [metricKoszulRhs] at hForward hReverse
  rw [data.metricDerivative_symmetric base test first second] at hForward
  linarith

/-- Nondegeneracy and the Koszul formula make the continuous connection family
unique. -/
theorem SmoothEuclideanKoszulConnectionData.connection_unique
    (data : SmoothEuclideanKoszulConnectionData Model)
    (candidate : Model → ContinuousTangentialQuadratic Model)
    (hCandidate :
      ∀ base first second test,
        2 * data.metric base (candidate base first second) test =
          metricKoszulRhs data.metric base first second test) :
    candidate = data.connection := by
  funext base
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  apply data.metric_nondegenerate base
  intro test
  have hLeft := hCandidate base first second test
  have hRight := data.connection_koszul base first second test
  linarith

variable {Tangent : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Ambient]

/-- Continuous dependence of right precomposition on the bilinear map. -/
def precompRFamilyCLM :
    (Tangent →L[ℝ] (Ambient →L[ℝ] Ambient)) →L[ℝ]
      (Tangent →L[ℝ] ((Tangent →L[ℝ] Ambient) →L[ℝ]
        (Tangent →L[ℝ] Ambient))) :=
  (ContinuousLinearMap.compL ℝ Tangent
    (Ambient →L[ℝ] Ambient)
    ((Tangent →L[ℝ] Ambient) →L[ℝ] (Tangent →L[ℝ] Ambient)))
      (ContinuousLinearMap.compL ℝ Tangent Ambient Ambient)

/-- Bundled flip used to evaluate the common pullback derivative in the second
ambient slot. -/
def flipPullbackCLM :
    (Tangent →L[ℝ] ((Tangent →L[ℝ] Ambient) →L[ℝ]
      (Tangent →L[ℝ] Ambient))) →L[ℝ]
      ((Tangent →L[ℝ] Ambient) →L[ℝ]
        (Tangent →L[ℝ] (Tangent →L[ℝ] Ambient))) :=
  (LinearIsometryEquiv.toLinearIsometry
    (ContinuousLinearMap.flipₗᵢ ℝ Tangent
      (Tangent →L[ℝ] Ambient) (Tangent →L[ℝ] Ambient))).toContinuousLinearMap

/-- Pull a continuous ambient bilinear connection coefficient back through the
first derivative of an immersion. -/
def pullbackAmbientConnection
    (ambientConnection : Ambient → ContinuousTangentialQuadratic Ambient)
    (immersion : Tangent → Ambient)
    (derivative : Tangent → Tangent →L[ℝ] Ambient) :
    Tangent → ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  fun base =>
    flipPullbackCLM (Tangent := Tangent) (Ambient := Ambient)
      (precompRFamilyCLM (Tangent := Tangent) (Ambient := Ambient)
        ((ambientConnection (immersion base)).comp (derivative base)))
      (derivative base)

@[simp]
theorem pullbackAmbientConnection_apply
    (ambientConnection : Ambient → ContinuousTangentialQuadratic Ambient)
    (immersion : Tangent → Ambient)
    (derivative : Tangent → Tangent →L[ℝ] Ambient)
    (base first second : Tangent) :
    pullbackAmbientConnection ambientConnection immersion derivative base
        first second =
      ambientConnection (immersion base)
        (derivative base first) (derivative base second) := by
  rfl

/-- Pullback preserves smooth dependence of a connection coefficient. -/
theorem pullbackAmbientConnection_contDiff
    (ambientConnection : Ambient → ContinuousTangentialQuadratic Ambient)
    (immersion : Tangent → Ambient)
    (derivative : Tangent → Tangent →L[ℝ] Ambient)
    (hAmbientConnection : ContDiff ℝ ∞ ambientConnection)
    (hImmersion : ContDiff ℝ ∞ immersion)
    (hDerivative : ContDiff ℝ ∞ derivative) :
    ContDiff ℝ ∞
      (pullbackAmbientConnection ambientConnection immersion derivative) := by
  apply contDiff_clm_apply_iff.mpr
  intro first
  apply contDiff_clm_apply_iff.mpr
  intro second
  change ContDiff ℝ ∞ (fun base =>
    ambientConnection (immersion base)
      (derivative base first) (derivative base second))
  fun_prop

/-- Pullback preserves torsion-free symmetry. -/
theorem pullbackAmbientConnection_symmetric
    (ambientConnection : Ambient → ContinuousTangentialQuadratic Ambient)
    (immersion : Tangent → Ambient)
    (derivative : Tangent → Tangent →L[ℝ] Ambient)
    (hSymmetric :
      ∀ base first second,
        ambientConnection base first second =
          ambientConnection base second first) :
    ∀ base first second,
      pullbackAmbientConnection ambientConnection immersion derivative base
          first second =
        pullbackAmbientConnection ambientConnection immersion derivative base
          second first := by
  intro base first second
  simp only [pullbackAmbientConnection_apply]
  exact hSymmetric (immersion base)
    (derivative base first) (derivative base second)

/-- Actual Euclidean immersion and gauge-potential data whose source and ambient
connection coefficients are tied to metric Koszul structures. -/
structure EuclideanMetricImmersionConnectionData where
  immersion : Tangent → Ambient
  gaugePotential : Tangent → ContinuousConnectionValue Tangent
  sourceMetricConnection : SmoothEuclideanKoszulConnectionData Tangent
  ambientMetricConnection : SmoothEuclideanKoszulConnectionData Ambient
  physicalNormalAmbient : Tangent → Ambient
  immersion_contDiff : ContDiff ℝ ∞ immersion
  gaugePotential_contDiff : ContDiff ℝ ∞ gaugePotential
  physicalNormalAmbient_contDiff : ContDiff ℝ ∞ physicalNormalAmbient

/-- Actual first derivative of the metric immersion. -/
def EuclideanMetricImmersionConnectionData.firstDerivative
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → Tangent →L[ℝ] Ambient :=
  fderiv ℝ data.immersion

theorem EuclideanMetricImmersionConnectionData.firstDerivative_contDiff
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContDiff ℝ ∞ data.firstDerivative := by
  simpa [EuclideanMetricImmersionConnectionData.firstDerivative] using
    data.immersion_contDiff.fderiv_right (m := ∞) (by simp)

/-- Ambient Levi-Civita coefficient pulled back along the actual immersion. -/
def EuclideanMetricImmersionConnectionData.ambientConnection
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  pullbackAmbientConnection data.ambientMetricConnection.connection
    data.immersion data.firstDerivative

theorem EuclideanMetricImmersionConnectionData.ambientConnection_contDiff
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContDiff ℝ ∞ data.ambientConnection := by
  exact pullbackAmbientConnection_contDiff
    data.ambientMetricConnection.connection data.immersion data.firstDerivative
    data.ambientMetricConnection.connection_contDiff data.immersion_contDiff
    data.firstDerivative_contDiff

theorem EuclideanMetricImmersionConnectionData.ambientConnection_symmetric
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ∀ base first second,
      data.ambientConnection base first second =
        data.ambientConnection base second first := by
  exact pullbackAmbientConnection_symmetric
    data.ambientMetricConnection.connection data.immersion data.firstDerivative
    data.ambientMetricConnection.connection_symmetric

/-- Metric/Koszul data automatically instantiate the already-validated actual
immersion/connection extraction interface. -/
def EuclideanMetricImmersionConnectionData.toEuclideanImmersionConnectionJetData
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient)) :
    EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient) where
  immersion := data.immersion
  gaugePotential := data.gaugePotential
  ambientConnection := data.ambientConnection
  sourceConnection := data.sourceMetricConnection.connection
  physicalNormalAmbient := data.physicalNormalAmbient
  immersion_contDiff := data.immersion_contDiff
  gaugePotential_contDiff := data.gaugePotential_contDiff
  ambientConnection_contDiff := data.ambientConnection_contDiff
  sourceConnection_contDiff := data.sourceMetricConnection.connection_contDiff
  physicalNormalAmbient_contDiff := data.physicalNormalAmbient_contDiff
  ambientConnection_symmetric := data.ambientConnection_symmetric
  sourceConnection_symmetric := data.sourceMetricConnection.connection_symmetric

@[simp]
theorem EuclideanMetricImmersionConnectionData.toJet_sourceConnection_apply
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient))
    (base first second : Tangent) :
    data.toEuclideanImmersionConnectionJetData.sourceConnection base first second =
      data.sourceMetricConnection.connection base first second := by
  rfl

@[simp]
theorem EuclideanMetricImmersionConnectionData.toJet_ambientConnection_apply
    (data : EuclideanMetricImmersionConnectionData
      (Tangent := Tangent) (Ambient := Ambient))
    (base first second : Tangent) :
    data.toEuclideanImmersionConnectionJetData.ambientConnection base
        first second =
      data.ambientMetricConnection.connection (data.immersion base)
        (fderiv ℝ data.immersion base first)
        (fderiv ℝ data.immersion base second) := by
  rfl

variable {Normal : Type*}
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Normal]
variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Metric-derived connection data together with projected-seed geometry. -/
structure EuclideanMetricProjectedSeedImmersionData where
  coefficients : EuclideanMetricImmersionConnectionData
    (Tangent := Tangent) (Ambient := Ambient)
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  basisData : PointwiseNormalBasisData Tangent Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  immersion_fderiv_eq_tangentSynthesis :
    ∀ base,
      coefficients.firstDerivative base =
        tangentFrameSynthesisCLM tangentBasis basisData base

/-- Forget the metric provenance and enter the validated Euclidean extraction
pipeline. -/
def EuclideanMetricProjectedSeedImmersionData.toEuclideanProjectedSeedImmersionData
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    EuclideanProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ) where
  coefficients := data.coefficients.toEuclideanImmersionConnectionJetData
  tangentBasis := data.tangentBasis
  tangentBasis_orthonormal := data.tangentBasis_orthonormal
  normalBasis := data.normalBasis
  normalBasis_orthonormal := data.normalBasis_orthonormal
  basisData := data.basisData
  ambientDimension := data.ambientDimension
  immersion_fderiv_eq_tangentSynthesis :=
    data.immersion_fderiv_eq_tangentSynthesis

/-- Global physical operator obtained from actual derivatives and metric Koszul
connections. -/
def EuclideanMetricProjectedSeedImmersionData.physicalOperator
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    Tangent → Tangent →L[ℝ] Tangent :=
  data.toEuclideanProjectedSeedImmersionData.physicalOperator

/-- The metric-derived physical shape operator is globally smooth. -/
theorem EuclideanMetricProjectedSeedImmersionData.physicalOperator_contDiff
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator :=
  data.toEuclideanProjectedSeedImmersionData.physicalOperator_contDiff

/-- Audit boundary after tying both connection coefficients to exact metric
Koszul identities. -/
structure EuclideanMetricKoszulConnectionStatus where
  smoothSourceMetricSupplied : Prop
  smoothAmbientMetricSupplied : Prop
  sourceKoszulConnectionCharacterized : Prop
  ambientKoszulConnectionCharacterized : Prop
  sourceConnectionUniquenessProved : Prop
  ambientConnectionUniquenessProved : Prop
  torsionFreeSymmetryProved : Prop
  ambientConnectionPulledBackAlongImmersion : Prop
  pullbackSmoothnessProved : Prop
  actualJetExtractionInstantiated : Prop
  globalPhysicalOperatorSmooth : Prop
  koszulConnectionExistenceConstructedFromMetric : Prop
  globalSpinCConnectionPotentialConstructed : Prop

/-- Full closure of the metric/Koszul connection stage. -/
def euclideanMetricKoszulConnectionClosed
    (s : EuclideanMetricKoszulConnectionStatus) : Prop :=
  s.smoothSourceMetricSupplied ∧
  s.smoothAmbientMetricSupplied ∧
  s.sourceKoszulConnectionCharacterized ∧
  s.ambientKoszulConnectionCharacterized ∧
  s.sourceConnectionUniquenessProved ∧
  s.ambientConnectionUniquenessProved ∧
  s.torsionFreeSymmetryProved ∧
  s.ambientConnectionPulledBackAlongImmersion ∧
  s.pullbackSmoothnessProved ∧
  s.actualJetExtractionInstantiated ∧
  s.globalPhysicalOperatorSmooth ∧
  s.koszulConnectionExistenceConstructedFromMetric ∧
  s.globalSpinCConnectionPotentialConstructed

/-- Omitting constructive Koszul existence still blocks this stage, even when
uniqueness and the downstream descent interfaces are available. -/
theorem missing_koszul_existence_blocks_closure
    (s : EuclideanMetricKoszulConnectionStatus)
    (hMissing : Not s.koszulConnectionExistenceConstructedFromMetric) :
    Not (euclideanMetricKoszulConnectionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusEuclideanMetricKoszulConnection
end JanusFormal
