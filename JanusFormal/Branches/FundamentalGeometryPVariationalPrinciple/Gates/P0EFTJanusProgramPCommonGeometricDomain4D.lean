import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge

/-!
# Common geometric domain for the current Program-P frontier

This gate ties one smooth independent-field configuration on the effective
mapping-torus quotient to its induced positive-diagonal metrics/principal root,
the positive LL energy-domain data used by the strong operator, and the exact
smooth throat trace used as boundary data.  The same period also indexes one
D7/D10 spectral package, while D9 fields and their principal symbol are fed
directly from the stored configuration and its existing variation type.

It does not identify the Program-P action Hessian with the D7/D9/D10 operators,
does not supply a general-Lorentz metric domain, and does not claim equality of
their eventual Fredholm or regulator domains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCommonGeometricDomain4D

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCliffordDiracPrincipalSymbol
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- One typed domain shared by the present geometric, LL-operator and smooth
Dirichlet-boundary constructions.  The three coherence fields prevent the
stored packages from referring to different configurations. -/
structure ProgramPCommonGeometricDomain4D where
  configuration : IndependentFields period hPeriod
  induced : InducedFields period hPeriod
  operatorData : PositiveLLH1Data period hPeriod
  d10Completion : D10SpectralCompletion
  boundary : IndependentBoundaryData period hPeriod
  induced_coherent : induced = induce period hPeriod configuration
  operator_coherent : operatorData.fields = configuration
  boundary_coherent :
    independentBoundaryTrace period hPeriod configuration = boundary

/-- Construct the common package from exactly the data already required by
the positive LL operator.  Metric/root and boundary packages are not extra
choices. -/
def ProgramPCommonGeometricDomain4D.ofOperatorData
    (operatorData : PositiveLLH1Data period hPeriod)
    (d10Completion : D10SpectralCompletion) :
    ProgramPCommonGeometricDomain4D period hPeriod where
  configuration := operatorData.fields
  induced := induce period hPeriod operatorData.fields
  operatorData := operatorData
  d10Completion := d10Completion
  boundary := independentBoundaryTrace period hPeriod operatorData.fields
  induced_coherent := rfl
  operator_coherent := rfl
  boundary_coherent := rfl

/-- Positive diagonal metric pair carried by the common configuration. -/
def ProgramPCommonGeometricDomain4D.admissibleMetrics
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    SmoothPositiveDiagonalMetricPair period hPeriod :=
  domain.configuration.metrics

/-- Principal root field induced from the very same metric pair. -/
def ProgramPCommonGeometricDomain4D.principalRoot
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :=
  domain.induced.principalRoot

/-- The genuine completed LL energy domain indexed by the stored operator
data. -/
abbrev ProgramPCommonGeometricDomain4D.llOperatorDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :=
  LLH1Space period hPeriod domain.operatorData

/-- The Program-P variation type used directly by the existing D9 bridge. -/
abbrev ProgramPCommonGeometricDomain4D.d9VariationDomain
    (_domain : ProgramPCommonGeometricDomain4D period hPeriod) :=
  IndependentFieldVariation period hPeriod

/-- D9 local field obtained without replacing the stored global
configuration.  The existing residual completion remains an explicit input. -/
def ProgramPCommonGeometricDomain4D.d9Field
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : domain.d9VariationDomain)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor) : CompleteLocalField Spinor :=
  P0EFTJanusD9D10ExactFieldContentBridge4D.d9LocalField period hPeriod
    domain.configuration variation sector column point completion

/-- Existing D9 gauge-fixed principal symbol acting on the field supplied by
the common configuration. -/
def ProgramPCommonGeometricDomain4D.d9PrincipalSymbol
    {Spinor : Type*} [Zero Spinor] [SMul Real Spinor]
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : domain.d9VariationDomain)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor)
    (clifford : CliffordSymbolData Spinor)
    (covector : TangentVector3) : CompleteLocalField Spinor :=
  completePrincipalSymbol clifford covector
    (ProgramPCommonGeometricDomain4D.d9Field period hPeriod domain variation
      sector column point completion)

/-- The single spectral datum used by both the D7 heat operator and D10
finite regulator.  Its circle period is derived from this domain's mapping
torus period. -/
def ProgramPCommonGeometricDomain4D.d7d10SpectralData
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProductThroatSpectralData :=
  d10SpectralData period hPeriod domain.d10Completion

/-- Existing D7 compact circle heat block on the common D7/D10 spectral
datum. -/
def ProgramPCommonGeometricDomain4D.d7HeatOperator
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (time : HeatTime) (choice : NormalRootChoice) :=
  d7CircleHeatOperator domain.d7d10SpectralData time choice

/-- Existing finite D10 regulator spectrum on exactly the datum used by the
D7 accessor. -/
def ProgramPCommonGeometricDomain4D.d10FiniteRegulator
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (sphereCutoff circleCutoff : Nat) :=
  d10RegulatorSpectrum domain.d7d10SpectralData unitRootChirality
    sphereCutoff circleCutoff

@[simp]
theorem ProgramPCommonGeometricDomain4D.d7d10_circlePeriod
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    domain.d7d10SpectralData.circlePeriod = |period| :=
  rfl

@[simp]
theorem ProgramPCommonGeometricDomain4D.d9Field_metricPerturbation
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : domain.d9VariationDomain)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor) :
    (ProgramPCommonGeometricDomain4D.d9Field period hPeriod domain variation
      sector column point completion).bosonic.metricPerturbation =
      d9MetricPerturbation period hPeriod domain.configuration variation
        sector point :=
  rfl

/-- The tangent space still missing from the common domain.  It extends the
actual `IndependentFieldVariation`; the extra slots are genuine geometric
normal, tangent-ghost and global symmetric-tensor fields, rather than local
numbers inserted after projection to D9. -/
structure ProgramPCompleteVariation4D where
  independent : IndependentFieldVariation period hPeriod
  normalDisplacement : Sector -> SmoothNormalDisplacement period hPeriod
  diffeomorphismGhost : Sector -> CInfinityThroatGhost period hPeriod
  fullMetricPerturbation :
    Sector -> SmoothSymmetricCovariantTwoTensor period hPeriod

/-- Canonical local scalar coordinate of the genuine normal displacement. -/
def ProgramPCompleteVariation4D.normalModeAt
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : Real :=
  preferredNormalMode period hPeriod
    (variation.normalDisplacement sector) point

/-- Canonical D9 tangent coordinates of the genuine smooth throat ghost. -/
def ProgramPCompleteVariation4D.diffeomorphismGhostAt
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : TangentVector3 :=
  throatTangentToD9 ((variation.diffeomorphismGhost sector) point)

/-- Six D9 spatial coefficients of the genuine global symmetric tensor in
the automatically selected holonomic chart through the throat point. -/
def ProgramPCompleteVariation4D.metricPerturbationAt
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : SymmetricTensor3 :=
  d9FullMetricProjection
    (d9TensorChartMetricVariation period hPeriod
      (variation.fullMetricPerturbation sector)
      (selectedD9ThroatHolonomicPatch period hPeriod point)
      (selectedD9ThroatHolonomicCoordinate period hPeriod point))

/-- Global D10 mode label retaining the literal sphere-multiplicity index
which `ProductDiracMode` itself does not store. -/
structure ProgramPD10Mode4D (data : ProductThroatSpectralData) where
  separatedMode : ProductDiracMode
  sphereMultiplicityIndex :
    Fin (sphereMultiplicity data separatedMode.sphereLevel)

/-- The finite regulator mode embedded without dropping its degeneracy
label. -/
def truncatedProgramPD10Mode4D
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    ProgramPD10Mode4D data where
  separatedMode := truncatedD10Mode mode
  sphereMultiplicityIndex := mode.2.1

/-- Square-summable real Hessian coordinates indexed by the complete,
multiplicity-aware D10 labels.  The real coefficient field matches the real
action tangent; complex spinor-mode completion remains part of constructing
an eventual inhabitant rather than being smuggled into a real Hessian. -/
abbrev ProgramPD10ModeHilbert4D (data : ProductThroatSpectralData) :=
  lp (fun _ : ProgramPD10Mode4D data => Real) 2

/-- Maximal diagonal Hessian domain in the multiplicity-aware D10
coordinates.  This is the concrete Fredholm-domain target required below. -/
def programPD10FredholmModeDomain4D (data : ProductThroatSpectralData) :
    Set (ProgramPD10ModeHilbert4D data) :=
  { coefficients | Memℓp
      (fun mode =>
        productDiracEigenvalueSquared data mode.separatedMode *
          coefficients mode)
      2 }

/-- Tangent directions which preserve the exact boundary datum of the common
domain along their full Program-P curve. -/
def programPBoundaryTangentDomain4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    Set (ProgramPCompleteVariation4D period hPeriod) :=
  { variation | forall parameter : Real,
      SatisfiesIndependentBoundary period hPeriod domain.boundary
        (independentFieldCurve period hPeriod domain.configuration
          variation.independent parameter) }

/-- Strengthened residual contract for a single Program-P/D9/D10 theory.

Every logical field below is a concrete equality, derivative statement,
injectivity/surjectivity statement or domain equivalence.  In particular, the
contract cannot be inhabited by assigning `True` to unnamed agreement
propositions. -/
structure RemainingProgramPD7D9D10DomainAgreement4D
    (Spinor : Type*)
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  extendVariation :
    IndependentFieldVariation period hPeriod ->
      ProgramPCompleteVariation4D period hPeriod
  extendVariation_independent :
    forall variation,
      (extendVariation variation).independent = variation

  tangentZero : ProgramPCompleteVariation4D period hPeriod
  tangentAdd :
    ProgramPCompleteVariation4D period hPeriod ->
      ProgramPCompleteVariation4D period hPeriod ->
        ProgramPCompleteVariation4D period hPeriod
  tangentSMul :
    Real -> ProgramPCompleteVariation4D period hPeriod ->
      ProgramPCompleteVariation4D period hPeriod
  tangent_add_assoc :
    forall first second third,
      tangentAdd (tangentAdd first second) third =
        tangentAdd first (tangentAdd second third)
  tangent_add_comm :
    forall first second, tangentAdd first second = tangentAdd second first
  tangent_zero_add :
    forall variation, tangentAdd tangentZero variation = variation
  tangent_add_zero :
    forall variation, tangentAdd variation tangentZero = variation
  tangent_add_neg :
    forall variation,
      tangentAdd variation (tangentSMul (-1) variation) = tangentZero
  tangent_one_smul :
    forall variation, tangentSMul 1 variation = variation
  tangent_mul_smul :
    forall first second variation,
      tangentSMul (first * second) variation =
        tangentSMul first (tangentSMul second variation)
  tangent_smul_add :
    forall scalar first second,
      tangentSMul scalar (tangentAdd first second) =
        tangentAdd (tangentSMul scalar first) (tangentSMul scalar second)
  tangent_add_smul :
    forall first second variation,
      tangentSMul (first + second) variation =
        tangentAdd (tangentSMul first variation) (tangentSMul second variation)
  tangent_zero_smul :
    forall variation, tangentSMul 0 variation = tangentZero
  tangent_smul_zero :
    forall scalar, tangentSMul scalar tangentZero = tangentZero
  tangentNormal_zero :
    forall sector point,
      tangentZero.normalModeAt period hPeriod sector point = 0
  tangentNormal_add :
    forall first second sector point,
      (tangentAdd first second).normalModeAt period hPeriod sector point =
        first.normalModeAt period hPeriod sector point +
          second.normalModeAt period hPeriod sector point
  tangentNormal_smul :
    forall scalar variation sector point,
      (tangentSMul scalar variation).normalModeAt period hPeriod sector point =
        scalar * variation.normalModeAt period hPeriod sector point
  tangentGhost_zero :
    forall sector point,
      tangentZero.diffeomorphismGhostAt period hPeriod sector point = zeroTangent
  tangentGhost_add :
    forall first second sector point,
      (tangentAdd first second).diffeomorphismGhostAt
          period hPeriod sector point =
        addTangent
          (first.diffeomorphismGhostAt period hPeriod sector point)
          (second.diffeomorphismGhostAt period hPeriod sector point)
  tangentGhost_smul :
    forall scalar variation sector point,
      (tangentSMul scalar variation).diffeomorphismGhostAt
          period hPeriod sector point =
        scaleTangent scalar
          (variation.diffeomorphismGhostAt period hPeriod sector point)
  tangentMetric_zero :
    forall sector point,
      tangentZero.metricPerturbationAt period hPeriod sector point = zeroSymmetric
  tangentMetric_add :
    forall first second sector point,
      (tangentAdd first second).metricPerturbationAt period hPeriod sector point =
        addSymmetric
          (first.metricPerturbationAt period hPeriod sector point)
          (second.metricPerturbationAt period hPeriod sector point)
  tangentMetric_smul :
    forall scalar variation sector point,
      (tangentSMul scalar variation).metricPerturbationAt
          period hPeriod sector point =
        scaleSymmetric scalar
          (variation.metricPerturbationAt period hPeriod sector point)

  ActionConfiguration : Type*
  configurationFields :
    ActionConfiguration -> IndependentFields period hPeriod
  baseConfiguration : ActionConfiguration
  baseConfiguration_fields :
    configurationFields baseConfiguration = domain.configuration
  action : ActionConfiguration -> Real
  actionCurve :
    ActionConfiguration -> ProgramPCompleteVariation4D period hPeriod ->
      Real -> ActionConfiguration
  actionCurve_zero :
    forall configuration variation,
      actionCurve configuration variation 0 = configuration
  actionCurve_tangentZero :
    forall configuration parameter,
      actionCurve configuration tangentZero parameter = configuration
  actionCurve_tangentAdd :
    forall configuration first second parameter,
      actionCurve configuration (tangentAdd first second) parameter =
        actionCurve (actionCurve configuration first parameter) second parameter
  actionCurve_tangentSMul :
    forall configuration scalar variation parameter,
      actionCurve configuration (tangentSMul scalar variation) parameter =
        actionCurve configuration variation (scalar * parameter)
  actionCurve_independentFields :
    forall configuration variation parameter,
      configurationFields (actionCurve configuration variation parameter) =
        independentFieldCurve period hPeriod
          (configurationFields configuration) variation.independent parameter
  actionFirstVariation :
    ActionConfiguration -> ProgramPCompleteVariation4D period hPeriod -> Real
  actionFirstVariation_hasDerivAt :
    forall configuration variation,
      HasDerivAt
        (fun parameter => action (actionCurve configuration variation parameter))
        (actionFirstVariation configuration variation) 0
  actionHessian :
    ActionConfiguration -> ProgramPCompleteVariation4D period hPeriod ->
      ProgramPCompleteVariation4D period hPeriod -> Real
  actionHessian_hasDerivAt :
    forall configuration first second,
      HasDerivAt
        (fun parameter =>
          actionFirstVariation (actionCurve configuration second parameter) first)
        (actionHessian configuration first second) 0
  actionHessian_symmetric :
    forall configuration first second,
      actionHessian configuration first second =
        actionHessian configuration second first

  matterSpinorIdentification : MatterFiber ≃ Spinor
  actionTangentD9Field :
    ProgramPCompleteVariation4D period hPeriod -> Sector -> Fin 2 ->
      EffectiveThroat period hPeriod -> CompleteLocalField Spinor
  actionTangentD9Field_normalMode :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).bosonic.normalMode =
        variation.normalModeAt period hPeriod sector point
  actionTangentD9Field_gaugeOneForm :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).bosonic.gaugeOneForm =
        d9GaugeOneForm period hPeriod variation.independent sector column point
  actionTangentD9Field_metricPerturbation :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).bosonic.metricPerturbation =
        variation.metricPerturbationAt period hPeriod sector point
  actionTangentD9Field_u1Ghost :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).ghosts.u1Ghost =
        d9U1Ghost period hPeriod variation.independent sector column point
  actionTangentD9Field_diffeomorphismGhost :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).ghosts.diffeomorphismGhost =
        variation.diffeomorphismGhostAt period hPeriod sector point
  actionTangentD9Field_spinor :
    forall variation sector column point,
      (actionTangentD9Field variation sector column point).spinor =
        matterSpinorIdentification
          (d9MatterCoefficient period hPeriod variation.independent sector point)
  fullMetricProjection_surjective :
    forall sector point,
      Function.Surjective
        (fun variation : ProgramPCompleteVariation4D period hPeriod =>
          variation.metricPerturbationAt period hPeriod sector point)

  modeCoordinateEquiv :
    ProgramPCompleteVariation4D period hPeriod ≃
      ProgramPD10ModeHilbert4D domain.d7d10SpectralData
  modeCoordinate_zero :
    modeCoordinateEquiv tangentZero = 0
  modeCoordinate_add :
    forall first second,
      modeCoordinateEquiv (tangentAdd first second) =
        modeCoordinateEquiv first + modeCoordinateEquiv second
  modeCoordinate_smul :
    forall scalar variation,
      modeCoordinateEquiv (tangentSMul scalar variation) =
        scalar • modeCoordinateEquiv variation
  tangentNorm : ProgramPCompleteVariation4D period hPeriod -> Real
  tangentNorm_nonnegative :
    forall variation, 0 ≤ tangentNorm variation
  tangentNorm_eq_zero_iff :
    forall variation, tangentNorm variation = 0 ↔ variation = tangentZero
  tangentNorm_smul :
    forall scalar variation,
      tangentNorm (tangentSMul scalar variation) =
        |scalar| * tangentNorm variation
  tangentNorm_triangle :
    forall first second,
      tangentNorm (tangentAdd first second) ≤
        tangentNorm first + tangentNorm second
  modeCoordinate_isometry :
    forall variation,
      tangentNorm variation = ‖modeCoordinateEquiv variation‖
  modeCoordinate_distance :
    forall first second,
      tangentNorm (tangentAdd first (tangentSMul (-1) second)) =
        ‖modeCoordinateEquiv first - modeCoordinateEquiv second‖
  modeTangent :
    ProgramPD10Mode4D domain.d7d10SpectralData ->
      ProgramPCompleteVariation4D period hPeriod
  modeTangent_injective : Function.Injective modeTangent
  modeCoordinate_same :
    forall mode,
      modeCoordinateEquiv (modeTangent mode) mode = 1
  modeCoordinate_ne :
    forall first second, first ≠ second ->
      modeCoordinateEquiv (modeTangent first) second = 0
  modeTangent_span_dense :
    Dense
      ((Submodule.span Real
        (Set.range (fun mode => modeCoordinateEquiv (modeTangent mode))) :
          Set (ProgramPD10ModeHilbert4D domain.d7d10SpectralData)))
  modeCoordinate_complete :
    forall sequence : Nat -> ProgramPCompleteVariation4D period hPeriod,
      CauchySeq (fun index => modeCoordinateEquiv (sequence index)) ->
        exists limit : ProgramPCompleteVariation4D period hPeriod,
          Filter.Tendsto (fun index => modeCoordinateEquiv (sequence index))
            Filter.atTop (nhds (modeCoordinateEquiv limit))

  tangentPairing :
    ProgramPCompleteVariation4D period hPeriod ->
      ProgramPCompleteVariation4D period hPeriod -> Real
  tangentPairing_symmetric :
    forall first second,
      tangentPairing first second = tangentPairing second first
  tangentPairing_eq_modeCoordinate :
    forall mode variation,
      tangentPairing (modeTangent mode) variation =
        modeCoordinateEquiv variation mode
  hessian_spectral_pairing_agreement :
    forall mode variation,
      actionHessian baseConfiguration (modeTangent mode) variation =
        productDiracEigenvalueSquared domain.d7d10SpectralData
            mode.separatedMode *
          tangentPairing (modeTangent mode) variation

  fredholmDomain : Set (ProgramPCompleteVariation4D period hPeriod)
  fredholmDomain_eq_boundaryDomain :
    fredholmDomain = programPBoundaryTangentDomain4D period hPeriod domain
  fredholmDomain_modeAgreement :
    forall variation,
      variation ∈ fredholmDomain ↔
        modeCoordinateEquiv variation ∈
          programPD10FredholmModeDomain4D domain.d7d10SpectralData

  regulator_hessian_spectrum_agreement :
    forall sphereCutoff circleCutoff
      (mode : TruncatedD10Mode domain.d7d10SpectralData
        sphereCutoff circleCutoff),
      actionHessian baseConfiguration
          (modeTangent (truncatedProgramPD10Mode4D mode))
          (modeTangent (truncatedProgramPD10Mode4D mode)) =
        (ProgramPCommonGeometricDomain4D.d10FiniteRegulator period hPeriod
          domain sphereCutoff circleCutoff).eigenvalueSq mode
  regulator_exactMultiplicity :
    forall sphereCutoff circleCutoff,
      Function.Injective
        (fun mode : TruncatedD10Mode domain.d7d10SpectralData
            sphereCutoff circleCutoff =>
          modeTangent (truncatedProgramPD10Mode4D mode))

@[simp]
theorem ProgramPCommonGeometricDomain4D.induced_eq
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    domain.induced = induce period hPeriod domain.configuration :=
  domain.induced_coherent

@[simp]
theorem ProgramPCommonGeometricDomain4D.operator_fields_eq
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    domain.operatorData.fields = domain.configuration :=
  domain.operator_coherent

@[simp]
theorem ProgramPCommonGeometricDomain4D.boundary_eq_trace
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    domain.boundary =
      independentBoundaryTrace period hPeriod domain.configuration :=
  domain.boundary_coherent.symm

/-- The metric projection lands pointwise in the same positive diagonal
Lorentz domain used by the global principal-root construction. -/
theorem ProgramPCommonGeometricDomain4D.metricPair_mem_admissibleDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    coefficientPairAt period hPeriod domain.admissibleMetrics point ∈
      globalDiagonalLorentzDomain :=
  coefficientPairAt_mem_domain period hPeriod domain.admissibleMetrics point

/-- Stored root and metric projections obey the exact relative-root square
equation because both come from `configuration`. -/
theorem ProgramPCommonGeometricDomain4D.principalRoot_square
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ProgramPCommonGeometricDomain4D.principalRoot period hPeriod domain point *
        ProgramPCommonGeometricDomain4D.principalRoot period hPeriod domain point =
      lorentzMetricInverse
          (domain.configuration.metrics.plusMagnitude point) *
        domain.induced.minusMetric point := by
  change domain.induced.principalRoot point * domain.induced.principalRoot point = _
  rw [domain.induced_coherent]
  exact induced_root_square period hPeriod domain.configuration point

/-- The stored boundary package is exactly satisfied by the stored global
configuration. -/
theorem ProgramPCommonGeometricDomain4D.satisfies_boundary
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    SatisfiesIndependentBoundary period hPeriod domain.boundary
      domain.configuration :=
  domain.boundary_coherent

/-- Flat positive metrics and zero coefficient fields, with the LL density
replaced by the positive constant one. -/
def canonicalPositiveOperatorFields : IndependentFields period hPeriod :=
  { zeroMatchedIndependentFields period hPeriod with
    llMeasure := constantSmoothThroatField period hPeriod Real 1 }

@[simp]
theorem canonicalPositiveOperatorFields_llMeasure
    (point : EffectiveThroat period hPeriod) :
    (canonicalPositiveOperatorFields period hPeriod).llMeasure point = 1 :=
  rfl

/-- Canonical operator-domain data on the same compact effective throat. -/
def canonicalPositiveLLH1Data : PositiveLLH1Data period hPeriod where
  fields := canonicalPositiveOperatorFields period hPeriod
  mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  finiteMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  openPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  llMeasure_pos := by
    intro point
    simp

/-- Explicit nonempty D10 geometric completion; its circle period is still
forced by the common mapping-torus period through `d10SpectralData`. -/
def canonicalD10SpectralCompletion : D10SpectralCompletion where
  sphereRadius := 1
  sphereRadiusPositive := by norm_num
  monopoleCharge := 0

/-- A concrete common domain assembled entirely from canonical witnesses
already present on the effective quotient and throat. -/
def canonicalProgramPCommonGeometricDomain4D :
    ProgramPCommonGeometricDomain4D period hPeriod :=
  ProgramPCommonGeometricDomain4D.ofOperatorData period hPeriod
    (canonicalPositiveLLH1Data period hPeriod)
    canonicalD10SpectralCompletion

theorem programPCommonGeometricDomain4D_nonempty :
    Nonempty (ProgramPCommonGeometricDomain4D period hPeriod) :=
  ⟨canonicalProgramPCommonGeometricDomain4D period hPeriod⟩

end

end P0EFTJanusProgramPCommonGeometricDomain4D
end JanusFormal
