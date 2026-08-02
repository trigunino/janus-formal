import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

/-!
# Candidate-A diagonal diffeomorphism BRST off-shell graph

This gate reuses the two already completed mono-metric BRST graphs, but takes
the closure only of the smooth image where both sectors share the same
`c/cbar/B` triple.  The action-derived Einstein weights therefore couple two
metric perturbations to one genuine diagonal diffeomorphism complex.

No second diffeomorphism triplet and no new analytic axiom are introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-! ## Shared smooth BRST core -/

@[ext]
structure GlobalCandidateADiagonalDiffeomorphismBRSTState where
  metricPerturbation : GlobalMetricPerturbationPair period hPeriod
  nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod

def globalCandidateADiagonalDiffeomorphismBRSTStateEquiv :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ≃
      GlobalMetricPerturbationPair period hPeriod ×
        GlobalDiffeomorphismNonminimalFields period hPeriod where
  toFun state := (state.metricPerturbation, state.nonminimal)
  invFun state := ⟨state.1, state.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance globalCandidateADiagonalDiffeomorphismBRSTStateAddCommGroup :
    AddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :=
  Equiv.addCommGroup
    (globalCandidateADiagonalDiffeomorphismBRSTStateEquiv period hPeriod)

instance globalCandidateADiagonalDiffeomorphismBRSTStateModule :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :=
  Equiv.module Real
    (globalCandidateADiagonalDiffeomorphismBRSTStateEquiv period hPeriod)

def zeroGlobalCandidateADiagonalDiffeomorphismBRSTState :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation := 0
  nonminimal := zeroGlobalDiffeomorphismNonminimalFields period hPeriod

/-- Restriction to one of the two existing mono-metric BRST cores.  The
nonminimal component is deliberately unchanged in both restrictions. -/
def globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
    (sector : Sector) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismBRSTState period hPeriod where
  toFun state :=
    { metricPerturbation := state.metricPerturbation sector
      nonminimal := state.nonminimal }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem globalCandidateADiagonalDiffeomorphismSectorState_metric
    (sector : Sector)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
      period hPeriod sector state).metricPerturbation =
        state.metricPerturbation sector :=
  rfl

@[simp]
theorem globalCandidateADiagonalDiffeomorphismSectorState_nonminimal
    (sector : Sector)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
      period hPeriod sector state).nonminimal = state.nonminimal :=
  rfl

/-- One diagonal real-linearized BRST differential:
`s h_s = L_c g_s`, `s c = 0`, `s cbar = B`, `s B = 0`. -/
def globalCandidateADiagonalDiffeomorphismBRST
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation :=
    globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod metric state.nonminimal.ghost
  nonminimal :=
    globalDiffeomorphismNonminimalBRST
      period hPeriod state.nonminimal

theorem globalCandidateADiagonalDiffeomorphismBRST_sector
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (sector : Sector)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
        period hPeriod sector
        (globalCandidateADiagonalDiffeomorphismBRST
          period hPeriod metric state) =
      globalDiffeomorphismBRST period hPeriod (metric sector)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod sector state) :=
  rfl

theorem globalCandidateADiagonalDiffeomorphismBRST_square_zero
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric
        (globalCandidateADiagonalDiffeomorphismBRST
          period hPeriod metric state) =
      zeroGlobalCandidateADiagonalDiffeomorphismBRSTState
        period hPeriod := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · change
      globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
          period hPeriod metric
          (zeroGlobalDiffeomorphismGhostField period hPeriod) = 0
    exact
      (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric).map_zero
  · exact globalDiffeomorphismNonminimalBRST_square_zero
      period hPeriod state.nonminimal

/-- The BRST derivative of the action-selected weighted condition is exactly
the already constructed weighted diagonal FP operator. -/
theorem globalCandidateADiagonalKineticGaugeCondition_BRST
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalKineticGaugeConditionLinearMap
        period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismBRST
          period hPeriod metric state).metricPerturbation =
      globalCandidateADiagonalKineticFaddeevPopovLinearMap
        period hPeriod couplings metric state.nonminimal.ghost :=
  rfl

/-! ## The weighted gauge fermion on the shared core -/

/-- Sum of the two mono-metric gauge fermions, with the Einstein kinetic
weights and the same antighost/Nakanishi--Lautrup fields in both terms. -/
def globalCandidateADiagonalDiffeomorphismGaugeFermion
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermion period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus state) +
    candidateAMinusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermion period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus state)

/-- Graded BRST variation of the shared weighted gauge fermion. -/
def globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus state) +
    candidateAMinusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus state)

def globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermionBRSTMixedAction
        period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus first)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus second) +
    candidateAMinusEinsteinKineticWeight couplings *
      globalDiffeomorphismGaugeFermionBRSTMixedAction
        period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus first)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus second)

theorem globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_formula
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings metric state =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
        period hPeriod couplings metric state state := by
  unfold globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
  rw [globalDiffeomorphismGaugeFermionBRSTVariation_formula,
    globalDiffeomorphismGaugeFermionBRSTVariation_formula]

def globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) : Real :=
  globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
      period hPeriod couplings metric first second +
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
      period hPeriod couplings metric second first

/-! ## Closed diagonal image inside the two existing graphs -/

def GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  WithLp 2
    (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .plus) ×
      GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .minus))

local instance (priority := 10000) diagonalAmbientNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) := by
  unfold GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
  infer_instance

/- The mono-metric file keeps these calculus instances local.  Reconstruct
the same canonical instance chain here before taking the diagonal product. -/
local instance monoDeDonderBaseGraphNormedSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod baseMetric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderGraphHilbert
      period hPeriod baseMetric)).toNormedSpace

local instance monoDeDonderBaseGraphModule
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod baseMetric) :=
  (monoDeDonderBaseGraphNormedSpace period hPeriod baseMetric).toModule

local instance monoDeDonderBaseGraphCompleteSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod baseMetric) :=
  globalGeneralMetricDeDonderGraphCompleteSpace
    period hPeriod baseMetric

local instance monoDeDonderPairingAmbientNormedSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod baseMetric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphAmbient
      period hPeriod baseMetric)).toNormedSpace

local instance monoDeDonderPairingAmbientModule
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod baseMetric) :=
  (monoDeDonderPairingAmbientNormedSpace
    period hPeriod baseMetric).toModule

local instance monoMetricPairingGraphNormedSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod baseMetric) :=
  Submodule.normedSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod baseMetric)

local instance monoMetricPairingGraphModule
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod baseMetric) :=
  Submodule.module
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod baseMetric)

local instance monoMetricPairingGraphInnerProductSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod baseMetric) :=
  Submodule.innerProductSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod baseMetric)

local instance monoMetricPairingGraphCompleteSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod baseMetric) :=
  globalGeneralMetricDeDonderPairingGraphCompleteSpace
    period hPeriod baseMetric

local instance (priority := 10000) monoOffShellAmbientInnerProductSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismOffShellAmbient
        period hPeriod baseMetric) :=
  @WithLp.instProdInnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod baseMetric)
    (GlobalDiffeomorphismOffShellFeatureTail period hPeriod)
    inferInstance inferInstance
    (monoMetricPairingGraphInnerProductSpace
      period hPeriod baseMetric)
    inferInstance inferInstance

local instance (priority := 10000) monoOffShellAmbientNormedSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismOffShellAmbient
        period hPeriod baseMetric) :=
  (monoOffShellAmbientInnerProductSpace
    period hPeriod baseMetric).toNormedSpace

local instance (priority := 10000) monoOffShellGraphNormedSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod baseMetric) :=
  @Submodule.normedSpace Real Real
    inferInstance inferInstance inferInstance
    (GlobalDiffeomorphismOffShellAmbient period hPeriod baseMetric)
    inferInstance
    (monoOffShellAmbientNormedSpace period hPeriod baseMetric)
    inferInstance inferInstance
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod baseMetric)

local instance (priority := 10000) monoOffShellGraphModule
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod baseMetric) :=
  Submodule.module
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod baseMetric)

local instance (priority := 10000) monoOffShellGraphInnerProductSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod baseMetric) :=
  @Submodule.innerProductSpace Real
    (GlobalDiffeomorphismOffShellAmbient period hPeriod baseMetric)
    inferInstance inferInstance
    (monoOffShellAmbientInnerProductSpace period hPeriod baseMetric)
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod baseMetric)

local instance monoOffShellGraphCompleteSpace
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod baseMetric) :=
  globalDiffeomorphismOffShellGraphCompleteSpace
    period hPeriod baseMetric

local instance (priority := 10000) diagonalAmbientInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) :=
  @WithLp.instProdInnerProductSpace Real
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .plus))
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .minus))
    inferInstance inferInstance
    (monoOffShellGraphInnerProductSpace
      period hPeriod (metric .plus))
    inferInstance
    (monoOffShellGraphInnerProductSpace
      period hPeriod (metric .minus))

local instance (priority := 10000) diagonalAmbientNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) :=
  (diagonalAmbientInnerProductSpace period hPeriod metric).toNormedSpace

local instance (priority := 10000) diagonalAmbientModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) :=
  (diagonalAmbientNormedSpace period hPeriod metric).toModule

local instance diagonalAmbientCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) := by
  unfold GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
  exact @WithLp.instProdCompleteSpace 2
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .plus))
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .minus))
    inferInstance inferInstance
    (monoOffShellGraphCompleteSpace period hPeriod (metric .plus))
    (monoOffShellGraphCompleteSpace period hPeriod (metric .minus))

def globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric where
  toFun := fun state => WithLp.toLp 2
    (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus state),
      globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus state))
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rw [(globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus).map_add]
      exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .plus)).map_add _ _
    · rw [(globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus).map_add]
      exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .minus)).map_add _ _
  map_smul' scalar state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rw [(globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus).map_smul]
      exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .plus)).map_smul _ _
    · rw [(globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus).map_smul]
      exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .minus)).map_smul _ _

def globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric) :=
  @Submodule.topologicalClosure Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
      period hPeriod metric)
    inferInstance inferInstance inferInstance
    (diagonalAmbientModule period hPeriod metric)
    inferInstance inferInstance
    (LinearMap.range
      (globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
        period hPeriod metric))

def GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
    period hPeriod metric

@[implicit_reducible]
def diagonalGraphNormedAddCommGroupValue
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) := by
  unfold GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
  infer_instance

local instance (priority := 10000) diagonalGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  Submodule.normedSpace
    (globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

local instance (priority := 10000) diagonalGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  Submodule.module
    (globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

local instance (priority := 10001) diagonalGraphContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) := by
  infer_instance

local instance (priority := 10000) diagonalGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  Submodule.innerProductSpace
    (globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

def globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric where
  toFun state :=
    ⟨globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
        period hPeriod metric state,
      (LinearMap.range
        (globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
            period hPeriod metric) state)⟩
  map_add' first second := Subtype.ext
    ((globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar state := Subtype.ext
    ((globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric).map_smul scalar state)

theorem globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hPlusGraph :
      globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod (metric .plus)
          (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
            period hPeriod .plus first) =
        globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod (metric .plus)
          (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
            period hPeriod .plus second) :=
    congrArg (fun value :
      GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric => WithLp.fst value) hAmbient
  have hMinusGraph :
      globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod (metric .minus)
          (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
            period hPeriod .minus first) =
        globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod (metric .minus)
          (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
            period hPeriod .minus second) :=
    congrArg (fun value :
      GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric => WithLp.snd value) hAmbient
  have hPlus :=
    globalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod (metric .plus) hPlusGraph
  have hMinus :=
    globalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod (metric .minus) hMinusGraph
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · funext sector
    cases sector with
    | plus => exact congrArg GlobalDiffeomorphismBRSTState.metricPerturbation hPlus
    | minus => exact congrArg GlobalDiffeomorphismBRSTState.metricPerturbation hMinus
  · exact congrArg GlobalDiffeomorphismBRSTState.nonminimal hPlus

theorem globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
    globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
  let graph :=
    globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
            period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
            period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨state, rfl⟩, rfl⟩
      exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact
        ⟨globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
            period hPeriod metric state,
          ⟨state, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
          period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric))
  rw [hRange]

@[implicit_reducible]
def globalCandidateADiagonalDiffeomorphismOffShellGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) := by
  unfold GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
    globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateADiagonalDiffeomorphismOffShellAmbientLinearMap
        period hPeriod metric))

local instance diagonalGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  globalCandidateADiagonalDiffeomorphismOffShellGraphCompleteSpace
    period hPeriod metric

/-! ## Sector and weighted feature projections -/

def globalCandidateADiagonalDiffeomorphismOffShellAmbientProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellAmbient
        period hPeriod metric :=
  (globalCandidateADiagonalDiffeomorphismOffShellGraphSubmodule
    period hPeriod metric).subtypeL

def globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .plus) :=
  (WithLp.fstL 2 Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .plus))
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .minus))).comp
    (globalCandidateADiagonalDiffeomorphismOffShellAmbientProjection
      period hPeriod metric)

def globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .minus) :=
  (WithLp.sndL 2 Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .plus))
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod (metric .minus))).comp
    (globalCandidateADiagonalDiffeomorphismOffShellAmbientProjection
      period hPeriod metric)

@[simp]
theorem globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
        period hPeriod metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .plus state) :=
  rfl

@[simp]
theorem globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
        period hPeriod metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap
          period hPeriod .minus state) :=
  rfl

private def globalCandidateADiagonalDiffeomorphismPlusDeDonderProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalDiffeomorphismOffShellDeDonderProjection
    period hPeriod (metric .plus)).comp
      (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
        period hPeriod metric)

private def globalCandidateADiagonalDiffeomorphismMinusDeDonderProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalDiffeomorphismOffShellDeDonderProjection
    period hPeriod (metric .minus)).comp
      (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
        period hPeriod metric)

/-- The completed graph projection representing the unique weighted diagonal
de Donder condition. -/
def globalCandidateADiagonalKineticDeDonderProjection
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  candidateAPlusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismPlusDeDonderProjection
        period hPeriod metric +
    candidateAMinusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismMinusDeDonderProjection
        period hPeriod metric

@[simp]
theorem globalCandidateADiagonalKineticDeDonderProjection_smooth
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalKineticDeDonderProjection
        period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalSmoothCovectorFrameL2LinearMap period hPeriod
        (globalCandidateADiagonalKineticGaugeConditionLinearMap
          period hPeriod couplings metric state.metricPerturbation) := by
  change
    candidateAPlusEinsteinKineticWeight couplings •
        globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod (metric .plus) (state.metricPerturbation .plus) +
      candidateAMinusEinsteinKineticWeight couplings •
        globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod (metric .minus) (state.metricPerturbation .minus) =
      globalSmoothCovectorFrameL2LinearMap period hPeriod
        (candidateAPlusEinsteinKineticWeight couplings •
            globalGeneralMetricDeDonderLinearMap
              period hPeriod (metric .plus) (state.metricPerturbation .plus) +
          candidateAMinusEinsteinKineticWeight couplings •
            globalGeneralMetricDeDonderLinearMap
              period hPeriod (metric .minus) (state.metricPerturbation .minus))
  rw [(globalSmoothCovectorFrameL2LinearMap period hPeriod).map_add,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_smul,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_smul]
  rfl

private def globalCandidateADiagonalDiffeomorphismPlusFPProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalDiffeomorphismOffShellFPProjection
    period hPeriod (metric .plus)).comp
      (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
        period hPeriod metric)

private def globalCandidateADiagonalDiffeomorphismMinusFPProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalDiffeomorphismOffShellFPProjection
    period hPeriod (metric .minus)).comp
      (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
        period hPeriod metric)

/-- Completed weighted FP projection on the same one-triplet graph. -/
def globalCandidateADiagonalKineticFPProjection
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  candidateAPlusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismPlusFPProjection
        period hPeriod metric +
    candidateAMinusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismMinusFPProjection
        period hPeriod metric

@[simp]
theorem globalCandidateADiagonalKineticFPProjection_smooth
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalKineticFPProjection
        period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalSmoothCovectorFrameL2LinearMap period hPeriod
        (globalCandidateADiagonalKineticFaddeevPopovLinearMap
          period hPeriod couplings metric state.nonminimal.ghost) := by
  change
    candidateAPlusEinsteinKineticWeight couplings •
        globalDiffeomorphismFPL2LinearMap
          period hPeriod (metric .plus) state.nonminimal.ghost +
      candidateAMinusEinsteinKineticWeight couplings •
        globalDiffeomorphismFPL2LinearMap
          period hPeriod (metric .minus) state.nonminimal.ghost =
      globalSmoothCovectorFrameL2LinearMap period hPeriod
        (candidateAPlusEinsteinKineticWeight couplings •
            globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
              period hPeriod (metric .plus) state.nonminimal.ghost +
          candidateAMinusEinsteinKineticWeight couplings •
            globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
              period hPeriod (metric .minus) state.nonminimal.ghost)
  rw [(globalSmoothCovectorFrameL2LinearMap period hPeriod).map_add,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_smul,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_smul]
  rfl

/-! ## Weighted bounded Hessian and Riesz representative -/

private def realBilinearPullback
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (bilinear : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F) : E →L[Real] E →L[Real] Real :=
  bilinear.bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' := E) (F' := E) projection projection

private def globalCandidateADiagonalDiffeomorphismPlusHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric →L[Real] Real :=
  @realBilinearPullback
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .plus))
    inferInstance (diagonalGraphNormedSpace period hPeriod metric)
    inferInstance
    (monoOffShellGraphNormedSpace period hPeriod (metric .plus))
    (globalDiffeomorphismOffShellHessian
      period hPeriod (metric .plus))
    (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
      period hPeriod metric)

private def globalCandidateADiagonalDiffeomorphismMinusHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric →L[Real] Real :=
  @realBilinearPullback
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    (GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod (metric .minus))
    inferInstance (diagonalGraphNormedSpace period hPeriod metric)
    inferInstance
    (monoOffShellGraphNormedSpace period hPeriod (metric .minus))
    (globalDiffeomorphismOffShellHessian
      period hPeriod (metric .minus))
    (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
      period hPeriod metric)

/-- Action-weighted pullback of the two mono-metric off-shell Hessians to the
closed one-triplet diagonal graph. -/
def globalCandidateADiagonalDiffeomorphismOffShellHessian
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric →L[Real] Real :=
  candidateAPlusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismPlusHessian
        period hPeriod metric +
    candidateAMinusEinsteinKineticWeight couplings •
      globalCandidateADiagonalDiffeomorphismMinusHessian
        period hPeriod metric

@[simp]
theorem globalCandidateADiagonalDiffeomorphismOffShellHessian_apply
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric first second =
      candidateAPlusEinsteinKineticWeight couplings *
          globalDiffeomorphismOffShellHessian
            period hPeriod (metric .plus)
            (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
              period hPeriod metric first)
            (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
              period hPeriod metric second) +
        candidateAMinusEinsteinKineticWeight couplings *
          globalDiffeomorphismOffShellHessian
            period hPeriod (metric .minus)
            (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
              period hPeriod metric first)
            (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
              period hPeriod metric second) :=
  rfl

theorem globalCandidateADiagonalDiffeomorphismOffShellHessian_comm
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric first second =
      globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric second first := by
  have hPlus := globalDiffeomorphismOffShellHessian_comm
    period hPeriod (metric .plus)
    (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
      period hPeriod metric first)
    (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
      period hPeriod metric second)
  have hMinus := globalDiffeomorphismOffShellHessian_comm
    period hPeriod (metric .minus)
    (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
      period hPeriod metric first)
    (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
      period hPeriod metric second)
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_apply,
    hPlus, hMinus]

theorem globalCandidateADiagonalDiffeomorphismOffShellHessian_smooth_eq_BRST
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric first)
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
        period hPeriod couplings metric first second := by
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
  simp only [
    globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]
  rw [globalDiffeomorphismOffShellHessian_smooth_eq_BRST,
    globalDiffeomorphismOffShellHessian_smooth_eq_BRST]
  unfold
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTMixedAction
    globalDiffeomorphismGaugeFermionBRSTPolarizationAction
  ring

private def realPullbackRiesz
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (projection : E →L[Real] F) (operator : F →L[Real] F) :
    E →L[Real] E :=
  projection.adjoint.comp (operator.comp projection)

private theorem realPullbackRiesz_pairing
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (projection : E →L[Real] F) (operator : F →L[Real] F)
    (first second : E) :
    inner Real (realPullbackRiesz projection operator first) second =
      inner Real (operator (projection first)) (projection second) := by
  unfold realPullbackRiesz
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply]

def globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric :=
  candidateAPlusEinsteinKineticWeight couplings •
      @realPullbackRiesz
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric)
        (GlobalDiffeomorphismOffShellGraphHilbert
          period hPeriod (metric .plus))
        inferInstance
        (diagonalGraphInnerProductSpace period hPeriod metric)
        (diagonalGraphCompleteSpace period hPeriod metric)
        inferInstance
        (monoOffShellGraphInnerProductSpace period hPeriod (metric .plus))
        (monoOffShellGraphCompleteSpace period hPeriod (metric .plus))
        (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection
          period hPeriod metric)
        (globalDiffeomorphismOffShellRieszOperator
          period hPeriod (metric .plus)) +
    candidateAMinusEinsteinKineticWeight couplings •
      @realPullbackRiesz
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric)
        (GlobalDiffeomorphismOffShellGraphHilbert
          period hPeriod (metric .minus))
        inferInstance
        (diagonalGraphInnerProductSpace period hPeriod metric)
        (diagonalGraphCompleteSpace period hPeriod metric)
        inferInstance
        (monoOffShellGraphInnerProductSpace period hPeriod (metric .minus))
        (monoOffShellGraphCompleteSpace period hPeriod (metric .minus))
        (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection
          period hPeriod metric)
        (globalDiffeomorphismOffShellRieszOperator
          period hPeriod (metric .minus))

private theorem diagonalGraph_inner_smul_left
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :
    inner Real (scalar • first) second =
      scalar * inner Real first second :=
  @real_inner_smul_left
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    inferInstance
    (diagonalGraphInnerProductSpace period hPeriod metric)
    first second scalar

theorem globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :
    inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
          period hPeriod couplings metric first) second =
      globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric first second := by
  unfold globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
  simp only [add_apply, smul_apply, inner_add_left]
  rw [diagonalGraph_inner_smul_left,
    diagonalGraph_inner_smul_left]
  rw [realPullbackRiesz_pairing, realPullbackRiesz_pairing,
    globalDiffeomorphismOffShellRieszOperator_pairing,
    globalDiffeomorphismOffShellRieszOperator_pairing,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]

theorem globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_symmetric
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :
    inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
          period hPeriod couplings metric first) second =
      inner Real first
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
          period hPeriod couplings metric second) := by
  rw [globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_comm,
    ← globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing]
  exact real_inner_comm _ _

/-! ## Quadratic C2 action -/

def globalCandidateADiagonalDiffeomorphismOffShellGraphAction
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) : Real :=
  (1 / 2 : Real) *
    globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric state state

private theorem realSymmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem realSymmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalCandidateADiagonalDiffeomorphismOffShellGraphAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    HasFDerivAt
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction
        period hPeriod couplings metric)
      (globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric state) state :=
  realSymmetricQuadratic_hasFDerivAt
    (globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric)
    (globalCandidateADiagonalDiffeomorphismOffShellHessian_comm
      period hPeriod couplings metric) state

theorem globalCandidateADiagonalDiffeomorphismOffShellGraphAction_contDiff
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction
        period hPeriod couplings metric) :=
  realSymmetricQuadratic_contDiff
    (globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric)

theorem globalCandidateADiagonalDiffeomorphismOffShellGraphAction_contDiff_two
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction
        period hPeriod couplings metric) :=
  (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_contDiff
    period hPeriod couplings metric).of_le (by simp)

theorem globalCandidateADiagonalDiffeomorphismOffShellGraphAction_smooth_eq_BRST
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction
        period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings metric state := by
  unfold globalCandidateADiagonalDiffeomorphismOffShellGraphAction
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_smooth_eq_BRST]
  unfold
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
  rw [globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_formula]
  ring

/-! ## Faithful typed raccord -/

def globalCandidateADiagonalDiffeomorphismOffShellGraphTypedCoreLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod metric ×
        GlobalTypedNonminimalFields period hPeriod) where
  toFun state :=
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric state,
      globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod state.nonminimal)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric).map_add first second
    · exact
        (globalDiffeomorphismNonminimalTypedInclusionLinearMap
          period hPeriod).map_add first.nonminimal second.nonminimal
  map_smul' scalar state := by
    apply Prod.ext
    · exact
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric).map_smul scalar state
    · exact
        (globalDiffeomorphismNonminimalTypedInclusionLinearMap
          period hPeriod).map_smul scalar state.nonminimal

@[simp]
theorem globalCandidateADiagonalDiffeomorphismOffShellGraphTypedCore_diffeomorphism
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    (globalCandidateADiagonalDiffeomorphismOffShellGraphTypedCoreLinearMap
      period hPeriod metric state).2.diffeomorphism = state.nonminimal :=
  rfl

theorem globalCandidateADiagonalDiffeomorphismOffShellGraphTypedCoreLinearMap_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalCandidateADiagonalDiffeomorphismOffShellGraphTypedCoreLinearMap
        period hPeriod metric) := by
  intro first second hEqual
  apply
    globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod metric
  exact congrArg Prod.fst hEqual

end

end P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
end JanusFormal
