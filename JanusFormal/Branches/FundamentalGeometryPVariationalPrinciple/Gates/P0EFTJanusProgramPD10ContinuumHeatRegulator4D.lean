import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Continuum D10 heat regulator

The complete multiplicity-aware D10 mode space is reindexed by the product of
the two normal roots, the exact sphere degeneracy labels and all circle modes.
At every positive common heat time its Gaussian weight and chiral weight are
summable.  The physical PT involution preserves the squared spectrum, reverses
chirality and forces the full infinite chiral trace to vanish.  The net of all
finite spectral cutoffs therefore converges to zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD10ContinuumHeatRegulator4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge

/-- Product coordinates underlying the complete multiplicity-aware D10 modes. -/
abbrev ProgramPD10HeatCoordinate4D (data : ProductThroatSpectralData) :=
  NormalRootChoice × ProductThroatHeatMode data

/-- The complete D10 mode structure is exactly the product spectral index. -/
def programPD10HeatCoordinateEquiv
    (data : ProductThroatSpectralData) :
    ProgramPD10Mode4D data ≃ ProgramPD10HeatCoordinate4D data where
  toFun mode :=
    (mode.separatedMode.rootChoice,
      (⟨mode.separatedMode.sphereLevel, mode.sphereMultiplicityIndex⟩,
        mode.separatedMode.circleMode))
  invFun mode :=
    { separatedMode :=
        { sphereLevel := mode.2.1.1
          circleMode := mode.2.2
          rootChoice := mode.1 }
      sphereMultiplicityIndex := mode.2.1.2 }
  left_inv mode := by
    rcases mode with ⟨⟨level, circleMode, rootChoice⟩, multiplicityIndex⟩
    rfl
  right_inv mode := by
    rcases mode with ⟨rootChoice, ⟨⟨level, multiplicityIndex⟩, circleMode⟩⟩
    rfl

/-- The D7 root-dependent circle reindexing as an actual equivalence. -/
def programPModeEquiv (choice : NormalRootChoice) : Int ≃ Int :=
  match choice with
  | .positiveQuarter => Equiv.refl Int
  | .negativeQuarter => Equiv.neg Int

@[simp]
theorem programPModeEquiv_apply
    (choice : NormalRootChoice) (mode : Int) :
    programPModeEquiv choice mode = programPMode choice mode := by
  cases choice <;> rfl

theorem d7CircleHeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) (mode : Int) :
    0 ≤ d7CircleHeatWeight data time choice mode :=
  (Real.exp_pos _).le

/-- Each physical normal-root circle tower is summable after the exact D7
time rescaling and Fourier reindexing. -/
theorem d7CircleHeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) :
    Summable (d7CircleHeatWeight data time choice) := by
  have hReindexed :
      Summable (fun mode : Int =>
        circleOperatorHeatWeight (programPHeatTime data time)
          (programPFold choice) quarterTwist
          (programPModeEquiv choice mode)) :=
    (programPModeEquiv choice).summable_iff.mpr
      (circleOperatorHeatWeight_summable
        (programPHeatTime data time) (programPFold choice) quarterTwist)
  refine hReindexed.congr fun mode => ?_
  rw [programPModeEquiv_apply, circleOperatorHeatWeight_eq_heatWeight,
    programP_heatWeight_eq_d7_circleHeatWeight]

/-- Heat weight on one fixed normal root and every sphere/circle mode. -/
def programPD10RootHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) (mode : ProductThroatHeatMode data) : Real :=
  sphereModeHeatWeight data time mode.1 *
    d7CircleHeatWeight data time choice mode.2

theorem programPD10RootHeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) (mode : ProductThroatHeatMode data) :
    0 ≤ programPD10RootHeatWeight data time choice mode := by
  exact mul_nonneg
    (sphereModeHeatWeight_nonnegative data time mode.1)
    (d7CircleHeatWeight_nonnegative data time choice mode.2)

theorem programPD10RootHeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) :
    Summable (programPD10RootHeatWeight data time choice) := by
  apply (summable_prod_of_nonneg
    (programPD10RootHeatWeight_nonnegative data time choice)).2
  constructor
  · intro sphereMode
    exact (d7CircleHeatWeight_summable data time choice).mul_left
      (sphereModeHeatWeight data time sphereMode)
  · have hSphere := sphereModeHeatWeight_summable data time
    have hScaled := hSphere.mul_right
      (∑' circleMode : Int, d7CircleHeatWeight data time choice circleMode)
    exact hScaled.congr fun sphereMode => by
      unfold programPD10RootHeatWeight
      simp only [Prod.fst, Prod.snd]
      rw [tsum_mul_left]

/-- Heat weight in explicit product coordinates. -/
def programPD10CoordinateHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10HeatCoordinate4D data) : Real :=
  programPD10RootHeatWeight data time mode.1 mode.2

theorem programPD10CoordinateHeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10HeatCoordinate4D data) :
    0 ≤ programPD10CoordinateHeatWeight data time mode :=
  programPD10RootHeatWeight_nonnegative data time mode.1 mode.2

theorem programPD10CoordinateHeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Summable (programPD10CoordinateHeatWeight data time) := by
  apply (summable_prod_of_nonneg
    (programPD10CoordinateHeatWeight_nonnegative data time)).2
  exact ⟨programPD10RootHeatWeight_summable data time,
    Summable.of_finite⟩

/-- Actual positive-time Gaussian on the complete D10 spectrum. -/
def programPD10HeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) : Real :=
  Real.exp (-time.1 *
    productDiracEigenvalueSquared data mode.separatedMode)

theorem programPD10HeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    0 ≤ programPD10HeatWeight data time mode :=
  (Real.exp_pos _).le

theorem programPD10HeatWeight_eq_coordinate
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    programPD10HeatWeight data time mode =
      programPD10CoordinateHeatWeight data time
        (programPD10HeatCoordinateEquiv data mode) := by
  change
    Real.exp (-time.1 *
        (sphereEigenvalueSquared data mode.separatedMode.sphereLevel +
          circleEigenvalue data mode.separatedMode.rootChoice
            mode.separatedMode.circleMode ^ 2)) =
      Real.exp (-time.1 *
          sphereEigenvalueSquared data mode.separatedMode.sphereLevel) *
        Real.exp (-time.1 *
          circleEigenvalue data mode.separatedMode.rootChoice
            mode.separatedMode.circleMode ^ 2)
  rw [← Real.exp_add]
  congr 1
  ring

/-- The full multiplicity-aware D10 Gaussian is absolutely summable. -/
theorem programPD10HeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Summable (programPD10HeatWeight data time) := by
  have hReindexed :
      Summable (fun mode : ProgramPD10Mode4D data =>
        programPD10CoordinateHeatWeight data time
          (programPD10HeatCoordinateEquiv data mode)) :=
    (programPD10HeatCoordinateEquiv data).summable_iff.mpr
      (programPD10CoordinateHeatWeight_summable data time)
  exact hReindexed.congr fun mode =>
    (programPD10HeatWeight_eq_coordinate data time mode).symm

/-- Finite, positive-time even heat trace of the complete D10 spectrum. -/
def programPD10InfiniteHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime) : Real :=
  ∑' mode : ProgramPD10Mode4D data, programPD10HeatWeight data time mode

theorem programPD10InfiniteHeatTrace_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime) :
    0 ≤ programPD10InfiniteHeatTrace data time := by
  exact tsum_nonneg (programPD10HeatWeight_nonnegative data time)

/-- Even heat trace over an arbitrary finite D10 spectral cutoff. -/
def programPD10FiniteHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (cutoff : Finset (ProgramPD10Mode4D data)) : Real :=
  ∑ mode ∈ cutoff, programPD10HeatWeight data time mode

/-- Every cofinal finite-cutoff net converges to the same complete even heat
trace. -/
theorem programPD10FiniteHeatTrace_tendsto_infinite
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Filter.Tendsto (programPD10FiniteHeatTrace data time)
      Filter.atTop (nhds (programPD10InfiniteHeatTrace data time)) := by
  exact (programPD10HeatWeight_summable data time).hasSum

/-- External finite multiplicity and statistics sign on the continuum even
D10 heat trace. -/
def signedProgramPD10InfiniteHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (multiplicity : Nat) (statistics : FieldStatistics) : Real :=
  statisticsSign statistics * (multiplicity : Real) *
    programPD10InfiniteHeatTrace data time

/-- Physical PT on the complete D10 mode, retaining its degeneracy label. -/
def programPD10PT
    {data : ProductThroatSpectralData}
    (mode : ProgramPD10Mode4D data) : ProgramPD10Mode4D data where
  separatedMode := ptMode mode.separatedMode
  sphereMultiplicityIndex := mode.sphereMultiplicityIndex

@[simp]
theorem programPD10PT_involutive
    {data : ProductThroatSpectralData}
    (mode : ProgramPD10Mode4D data) :
    programPD10PT (programPD10PT mode) = mode := by
  rcases mode with ⟨⟨level, circleMode, rootChoice⟩, multiplicityIndex⟩
  simp [programPD10PT, ptMode, opposite_root_involutive]

/-- PT is a genuine permutation of the complete D10 mode space. -/
def programPD10PTEquiv (data : ProductThroatSpectralData) :
    ProgramPD10Mode4D data ≃ ProgramPD10Mode4D data where
  toFun := programPD10PT
  invFun := programPD10PT
  left_inv := programPD10PT_involutive
  right_inv := programPD10PT_involutive

theorem programPD10HeatWeight_pt
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProgramPD10Mode4D data) :
    programPD10HeatWeight data time (programPD10PT mode) =
      programPD10HeatWeight data time mode := by
  unfold programPD10HeatWeight programPD10PT
  rw [pt_preserves_squared_spectrum]

/-- Root chirality on the complete mode space. -/
def programPD10Chirality
    (chirality : RootChiralityAssignment)
    {data : ProductThroatSpectralData}
    (mode : ProgramPD10Mode4D data) : Real :=
  chirality.chirality mode.separatedMode.rootChoice

theorem programPD10Chirality_pt
    (chirality : RootChiralityAssignment)
    {data : ProductThroatSpectralData}
    (mode : ProgramPD10Mode4D data) :
    programPD10Chirality chirality (programPD10PT mode) =
      -programPD10Chirality chirality mode := by
  exact chirality.pt_odd mode.separatedMode.rootChoice

/-- One continuum D10 chiral heat contribution. -/
def programPD10ChiralHeatTerm
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (mode : ProgramPD10Mode4D data) : Real :=
  programPD10Chirality chirality mode *
    programPD10HeatWeight data time mode

theorem programPD10ChiralHeatTerm_pt
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (mode : ProgramPD10Mode4D data) :
    programPD10ChiralHeatTerm data time chirality (programPD10PT mode) =
      -programPD10ChiralHeatTerm data time chirality mode := by
  rw [programPD10ChiralHeatTerm, programPD10Chirality_pt,
    programPD10HeatWeight_pt]
  simp [programPD10ChiralHeatTerm]

/-- A uniform bound for the two supplied root chiralities. -/
def rootChiralityBound (chirality : RootChiralityAssignment) : Real :=
  |chirality.chirality .positiveQuarter| +
    |chirality.chirality .negativeQuarter|

theorem programPD10Chirality_abs_le_bound
    (chirality : RootChiralityAssignment)
    {data : ProductThroatSpectralData}
    (mode : ProgramPD10Mode4D data) :
    |programPD10Chirality chirality mode| ≤ rootChiralityBound chirality := by
  unfold programPD10Chirality rootChiralityBound
  cases mode.separatedMode.rootChoice
  · exact le_add_of_nonneg_right
      (abs_nonneg (chirality.chirality .negativeQuarter))
  · exact le_add_of_nonneg_left
      (abs_nonneg (chirality.chirality .positiveQuarter))

/-- Absolute summability of the continuum chiral heat series. -/
theorem programPD10ChiralHeatTerm_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment) :
    Summable (programPD10ChiralHeatTerm data time chirality) := by
  apply Summable.of_norm_bounded
    ((programPD10HeatWeight_summable data time).mul_left
      (rootChiralityBound chirality))
  intro mode
  rw [programPD10ChiralHeatTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
  exact mul_le_mul_of_nonneg_right
    (programPD10Chirality_abs_le_bound chirality mode)
    (programPD10HeatWeight_nonnegative data time mode)

/-- Infinite chiral heat trace of the actual complete D10 mode set. -/
def programPD10InfiniteChiralHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment) : Real :=
  ∑' mode : ProgramPD10Mode4D data,
    programPD10ChiralHeatTerm data time chirality mode

/-- The full continuum trace vanishes because physical PT is an isospectral,
chirality-reversing permutation of every complete D10 mode. -/
theorem programPD10InfiniteChiralHeatTrace_eq_zero
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment) :
    programPD10InfiniteChiralHeatTrace data time chirality = 0 := by
  have hReindex :
      programPD10InfiniteChiralHeatTrace data time chirality =
        ∑' mode : ProgramPD10Mode4D data,
          programPD10ChiralHeatTerm data time chirality
            (programPD10PT mode) := by
    exact ((programPD10PTEquiv data).tsum_eq
      (programPD10ChiralHeatTerm data time chirality)).symm
  have hNegative :
      (∑' mode : ProgramPD10Mode4D data,
        programPD10ChiralHeatTerm data time chirality
          (programPD10PT mode)) =
        -programPD10InfiniteChiralHeatTrace data time chirality := by
    simp only [programPD10ChiralHeatTerm_pt,
      programPD10InfiniteChiralHeatTrace, tsum_neg]
  linarith [hReindex.trans hNegative]

/-- Trace over an arbitrary finite subset of complete D10 modes. -/
def programPD10FiniteChiralHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (cutoff : Finset (ProgramPD10Mode4D data)) : Real :=
  ∑ mode ∈ cutoff, programPD10ChiralHeatTerm data time chirality mode

/-- The unconditional finite-cutoff net converges to the vanishing continuum
trace; no preferred enumeration or rectangular cutoff is assumed. -/
theorem programPD10FiniteChiralHeatTrace_tendsto_zero
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment) :
    Filter.Tendsto
      (programPD10FiniteChiralHeatTrace data time chirality)
      Filter.atTop (nhds 0) := by
  have hHasSum :=
    (programPD10ChiralHeatTerm_summable data time chirality).hasSum
  rw [← programPD10InfiniteChiralHeatTrace_eq_zero data time chirality]
  exact hHasSum

/-- Statistics and external finite multiplicity do not change cancellation. -/
def signedProgramPD10InfiniteChiralHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (multiplicity : Nat) (statistics : FieldStatistics) : Real :=
  statisticsSign statistics * (multiplicity : Real) *
    programPD10InfiniteChiralHeatTrace data time chirality

theorem signedProgramPD10InfiniteChiralHeatTrace_eq_zero
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (multiplicity : Nat) (statistics : FieldStatistics) :
    signedProgramPD10InfiniteChiralHeatTrace data time chirality
      multiplicity statistics = 0 := by
  rw [signedProgramPD10InfiniteChiralHeatTrace,
    programPD10InfiniteChiralHeatTrace_eq_zero]
  ring

/-- Positive heat time viewed by the older nonnegative-time finite regulator. -/
def heatTimeToRegulatorTime (time : HeatTime) : RegulatorTime :=
  ⟨time.1, time.2.le⟩

/-- The continuum Gaussian restricts exactly to the existing literal finite
D10 regulator spectrum. -/
theorem programPD10HeatWeight_truncated
    (data : ProductThroatSpectralData) (time : HeatTime)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat)
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    programPD10HeatWeight data time (truncatedProgramPD10Mode4D mode) =
      P0EFTJanusFiniteModeHeatKernelAnomalyRegulator.heatWeight
        (heatTimeToRegulatorTime time)
        ((d10RegulatorSpectrum data chirality sphereCutoff circleCutoff)
          |>.eigenvalueSq mode) := by
  rfl

/-- Unconditional all-level D10 regulator certificate. -/
structure ProgramPD10ContinuumHeatRegulatorCertificate4D
    (data : ProductThroatSpectralData) : Prop where
  heatSummable :
    ∀ time : HeatTime, Summable (programPD10HeatWeight data time)
  evenCutoffConvergence :
    ∀ time : HeatTime,
      Filter.Tendsto (programPD10FiniteHeatTrace data time)
        Filter.atTop (nhds (programPD10InfiniteHeatTrace data time))
  chiralSummable :
    ∀ (time : HeatTime) (chirality : RootChiralityAssignment),
      Summable (programPD10ChiralHeatTerm data time chirality)
  ptSpectrum :
    ∀ (time : HeatTime) (mode : ProgramPD10Mode4D data),
      programPD10HeatWeight data time (programPD10PT mode) =
        programPD10HeatWeight data time mode
  continuumCancellation :
    ∀ (time : HeatTime) (chirality : RootChiralityAssignment),
      programPD10InfiniteChiralHeatTrace data time chirality = 0
  cutoffConvergence :
    ∀ (time : HeatTime) (chirality : RootChiralityAssignment),
      Filter.Tendsto
        (programPD10FiniteChiralHeatTrace data time chirality)
        Filter.atTop (nhds 0)

def programPD10ContinuumHeatRegulatorCertificate4D
    (data : ProductThroatSpectralData) :
    ProgramPD10ContinuumHeatRegulatorCertificate4D data where
  heatSummable := programPD10HeatWeight_summable data
  evenCutoffConvergence :=
    programPD10FiniteHeatTrace_tendsto_infinite data
  chiralSummable := programPD10ChiralHeatTerm_summable data
  ptSpectrum := programPD10HeatWeight_pt data
  continuumCancellation :=
    programPD10InfiniteChiralHeatTrace_eq_zero data
  cutoffConvergence :=
    programPD10FiniteChiralHeatTrace_tendsto_zero data

end

end P0EFTJanusProgramPD10ContinuumHeatRegulator4D
end JanusFormal
