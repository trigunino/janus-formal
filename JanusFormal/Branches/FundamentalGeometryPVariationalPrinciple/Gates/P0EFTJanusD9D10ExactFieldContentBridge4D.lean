import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInducedFieldVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusD2ModeFamilyInflowBridge
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusFiniteModeFredholmDeterminantLine

/-!
# Exact D9/D10 field-content frontier

This gate maps the current global Program-P coefficient package to the slots
which it genuinely supplies in D9.  The diagonal metric velocity, one
tangential gauge column, one scalar ghost and one matter coefficient are taken
from the same global variation.  A normal displacement, a diffeomorphism ghost
and the matter-to-Spinor identification remain explicit inputs.  In
particular, the present diagonal metric sector cannot cover D9's off-diagonal
metric perturbations.

For D10, finite modes are literal truncations of `ProductDiracMode`, including
the exact sphere multiplicity.  Their circle length is the absolute value of
the same mapping-torus period, and the resulting squared spectrum is fed to
the existing heat regulator.  Sphere radius, monopole charge, chirality
assignment, mode expansion, Hessian agreement and boundary-domain agreement
are not inferred from the coefficient package.
-/

namespace JanusFormal
namespace P0EFTJanusD9D10ExactFieldContentBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

/-- The outer Program-P pair; this is deliberately distinct from a choice of
normal root or chirality. -/
inductive Sector where
  | plus
  | minus
  deriving DecidableEq, Repr, Fintype

def selectSector {Alpha : Type*} : Sector -> Alpha × Alpha -> Alpha
  | .plus, pair => pair.1
  | .minus, pair => pair.2

/-- Restrict the selected global gauge variation to the throat. -/
def selectedGaugeTrace
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : GaugeFiber :=
  throatTrace period hPeriod GaugeFiber
    (selectSector sector variation.gauge) point

/-- D9's tangential one-form is one explicitly selected column of the
four-dimensional Program-P gauge coefficient. -/
def d9GaugeOneForm
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) : TangentVector3 :=
  let coefficient := selectedGaugeTrace period hPeriod variation sector point
  { x := coefficient (1, column)
    y := coefficient (2, column)
    z := coefficient (3, column) }

/-- The selected scalar Program-P ghost supplies D9's U(1) ghost slot. -/
def d9U1Ghost
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) : Real :=
  throatTrace period hPeriod GhostFiber
    (selectSector sector variation.ghosts) point column

/-- The selected matter velocity restricted to the actual throat. -/
def d9MatterCoefficient
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : MatterFiber :=
  throatTrace period hPeriod MatterFiber
    (selectSector sector variation.matter) point

/-- Velocity of the selected induced metric, evaluated on the throat inside
the same D8 quotient. -/
def selectedMetricVelocity
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : Matrix4 :=
  lorentzMetric (selectSector sector
    (metricMagnitudeVelocityAt period hPeriod fields variation 0
      (fixedThroatQuotientInclusion period hPeriod point)))

/-- Spatial `3 × 3` restriction of the exact induced-metric velocity. -/
def d9MetricPerturbation
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    SymmetricTensor3 :=
  let velocity := selectedMetricVelocity period hPeriod fields variation sector point
  { xx := velocity 1 1
    yy := velocity 2 2
    zz := velocity 3 3
    xy := velocity 1 2
    xz := velocity 1 3
    yz := velocity 2 3 }

@[simp] theorem d9MetricPerturbation_xy
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (d9MetricPerturbation period hPeriod fields variation sector point).xy = 0 := by
  simp [d9MetricPerturbation, selectedMetricVelocity, lorentzMetric]

@[simp] theorem d9MetricPerturbation_xz
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (d9MetricPerturbation period hPeriod fields variation sector point).xz = 0 := by
  simp [d9MetricPerturbation, selectedMetricVelocity, lorentzMetric]

@[simp] theorem d9MetricPerturbation_yz
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (d9MetricPerturbation period hPeriod fields variation sector point).yz = 0 := by
  simp [d9MetricPerturbation, selectedMetricVelocity, lorentzMetric]

/-- An explicit D9 tensor outside the current Program-P diagonal image. -/
def unitXYMetricPerturbation : SymmetricTensor3 :=
  { xx := 0, yy := 0, zz := 0, xy := 1, xz := 0, yz := 0 }

/-- The current Program-P metric tangent space is strictly smaller than D9's
six-component symmetric-tensor slot. -/
theorem d9_metric_projection_not_surjective
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    Not (Function.Surjective
      (fun variation : IndependentFieldVariation period hPeriod =>
        d9MetricPerturbation period hPeriod fields variation sector point)) := by
  intro hSurjective
  obtain ⟨variation, hVariation⟩ := hSurjective unitXYMetricPerturbation
  have hXY := congrArg SymmetricTensor3.xy hVariation
  simp [unitXYMetricPerturbation] at hXY

/-- D9 data not identified by the present Program-P package.  An equivalence
is required rather than silently calling the real matter coefficient a SpinC
spinor. -/
structure D9ResidualCompletion (Spinor : Type*) where
  normalMode : Real
  diffeomorphismGhost : TangentVector3
  matterSpinorIdentification : MatterFiber ≃ Spinor

/-- Type-safe local D9 field assembled from the same Program-P variation and
the three explicit residual inputs. -/
def d9LocalField
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor) : CompleteLocalField Spinor :=
  { bosonic :=
      { normalMode := completion.normalMode
        gaugeOneForm := d9GaugeOneForm period hPeriod variation sector column point
        metricPerturbation :=
          d9MetricPerturbation period hPeriod fields variation sector point }
    ghosts :=
      { u1Ghost := d9U1Ghost period hPeriod variation sector column point
        diffeomorphismGhost := completion.diffeomorphismGhost }
    spinor := completion.matterSpinorIdentification
      (d9MatterCoefficient period hPeriod variation sector point) }

@[simp] theorem d9LocalField_gaugeOneForm
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor) :
    (d9LocalField period hPeriod fields variation sector column point
      completion).bosonic.gaugeOneForm =
        d9GaugeOneForm period hPeriod variation sector column point := rfl

@[simp] theorem d9LocalField_u1Ghost
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (completion : D9ResidualCompletion Spinor) :
    (d9LocalField period hPeriod fields variation sector column point
      completion).ghosts.u1Ghost =
        d9U1Ghost period hPeriod variation sector column point := rfl

/-- D10 geometric inputs not contained in `IndependentFields`.  The compact
circle length, however, is fixed by the same nonzero mapping-torus period. -/
structure D10SpectralCompletion where
  sphereRadius : Real
  sphereRadiusPositive : 0 < sphereRadius
  monopoleCharge : Int

def d10SpectralData (completion : D10SpectralCompletion) :
    ProductThroatSpectralData where
  sphereRadius := completion.sphereRadius
  circlePeriod := |period|
  sphereRadiusPositive := completion.sphereRadiusPositive
  circlePeriodPositive := abs_pos.mpr hPeriod
  monopoleCharge := completion.monopoleCharge

/-- Signed nonzero circle label used by D10's symmetric finite cutoff. -/
def cutoffCircleMode {cutoff : Nat} :
    P0EFTJanusFiniteModeFredholmDeterminantLine.CutoffMode cutoff -> Int
  | (mode, false) => Int.ofNat (mode.val + 1)
  | (mode, true) => -Int.ofNat (mode.val + 1)

@[simp] theorem cutoffCircleMode_pt {cutoff : Nat}
    (mode : P0EFTJanusFiniteModeFredholmDeterminantLine.CutoffMode cutoff) :
    cutoffCircleMode
        (P0EFTJanusFiniteModeFredholmDeterminantLine.ptMode mode) =
      -cutoffCircleMode mode := by
  rcases mode with ⟨mode, sign⟩
  cases sign <;>
    simp [cutoffCircleMode,
      P0EFTJanusFiniteModeFredholmDeterminantLine.ptMode]

/-- Literal finite D10 mode set, including every sphere degeneracy label. -/
abbrev TruncatedD10Mode
    (data : ProductThroatSpectralData)
    (sphereCutoff circleCutoff : Nat) :=
  Σ level : Fin sphereCutoff,
    Fin (sphereMultiplicity data level.val) ×
      (P0EFTJanusFiniteModeFredholmDeterminantLine.CutoffMode circleCutoff ×
        NormalRootChoice)

def truncatedD10Mode
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) : ProductDiracMode :=
  { sphereLevel := mode.1.val
    circleMode := cutoffCircleMode mode.2.2.1
    rootChoice := mode.2.2.2 }

def truncatedPT
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    TruncatedD10Mode data sphereCutoff circleCutoff :=
  ⟨mode.1, mode.2.1,
    (P0EFTJanusFiniteModeFredholmDeterminantLine.ptMode mode.2.2.1,
      oppositeRoot mode.2.2.2)⟩

@[simp] theorem truncatedD10Mode_pt
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    truncatedD10Mode (truncatedPT mode) =
      P0EFTJanusGlobalSeparatedDiracModel.ptMode (truncatedD10Mode mode) := by
  rcases mode with ⟨level, degeneracy, circleMode, root⟩
  cases root <;>
    simp [truncatedD10Mode, truncatedPT,
      P0EFTJanusGlobalSeparatedDiracModel.ptMode]

@[simp] theorem truncatedPT_involutive
    {data : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    truncatedPT (truncatedPT mode) = mode := by
  rcases mode with ⟨level, degeneracy, circleMode, root⟩
  cases circleMode with
  | mk frequency sign =>
      cases sign <;> cases root <;> rfl

/-- Chirality is extra regulator data; PT-oddness is the only property used. -/
structure RootChiralityAssignment where
  chirality : NormalRootChoice -> Real
  pt_odd : ∀ root, chirality (oppositeRoot root) = -chirality root

/-- A normalized explicit choice, not a derivation from Program-P matter. -/
def unitRootChirality : RootChiralityAssignment where
  chirality
    | .positiveQuarter => 1
    | .negativeQuarter => -1
  pt_odd := by intro root; cases root <;> norm_num [oppositeRoot]

/-- The actual D10 separated squared eigenvalue, with exact finite
multiplicities, packaged for the Program-P heat regulator. -/
def d10RegulatorSpectrum
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat) :
    FiniteChiralSpectrum (TruncatedD10Mode data sphereCutoff circleCutoff) where
  eigenvalueSq := fun mode =>
    productDiracEigenvalueSquared data (truncatedD10Mode mode)
  eigenvalueSq_nonnegative := fun mode =>
    le_of_lt (product_spectrum_has_positive_gap data (truncatedD10Mode mode))
  chirality := fun mode => chirality.chirality mode.2.2.2

@[simp] theorem d10RegulatorSpectrum_eigenvalue_pt
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat)
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    (d10RegulatorSpectrum data chirality sphereCutoff circleCutoff).eigenvalueSq
        (truncatedPT mode) =
      (d10RegulatorSpectrum data chirality sphereCutoff circleCutoff).eigenvalueSq
        mode := by
  change productDiracEigenvalueSquared data (truncatedD10Mode (truncatedPT mode)) =
    productDiracEigenvalueSquared data (truncatedD10Mode mode)
  rw [truncatedD10Mode_pt]
  exact pt_preserves_squared_spectrum data (truncatedD10Mode mode)

@[simp] theorem d10RegulatorSpectrum_chirality_pt
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat)
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    (d10RegulatorSpectrum data chirality sphereCutoff circleCutoff).chirality
        (truncatedPT mode) =
      -(d10RegulatorSpectrum data chirality sphereCutoff circleCutoff).chirality mode := by
  exact chirality.pt_odd mode.2.2.2

/-- The regulator's abstract PT partner agrees pointwise with physical D10
mode reindexing, both spectrally and chirally. -/
theorem regulator_partner_matches_d10_pt
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat)
    (mode : TruncatedD10Mode data sphereCutoff circleCutoff) :
    let spectrum := d10RegulatorSpectrum data chirality sphereCutoff circleCutoff
    (ptPartner spectrum).eigenvalueSq mode =
        spectrum.eigenvalueSq (truncatedPT mode) ∧
      (ptPartner spectrum).chirality mode =
        spectrum.chirality (truncatedPT mode) := by
  dsimp
  constructor
  · symm
    exact d10RegulatorSpectrum_eigenvalue_pt data chirality
      sphereCutoff circleCutoff mode
  · symm
    exact d10RegulatorSpectrum_chirality_pt data chirality
      sphereCutoff circleCutoff mode

/-- Exact finite regulated cancellation on the literal truncated D10 modes. -/
theorem truncated_d10_regulated_chiral_trace_cancels
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff : Nat)
    (regulatorTime : RegulatorTime) :
    pairedRegulatedChiralTrace regulatorTime
      (d10RegulatorSpectrum data chirality sphereCutoff circleCutoff) = 0 := by
  exact pairedRegulatedChiralTrace_eq_zero regulatorTime _

/-- Remaining data required before one may claim that a single field space is
used by the Program-P action, D9 Hessian/BRST complex, D10 modes, regulator and
boundary conditions. -/
structure RemainingFieldContentContract (Spinor : Type*) where
  normalModeFromGlobalVariation :
    IndependentFields period hPeriod ->
      IndependentFieldVariation period hPeriod ->
      EffectiveThroat period hPeriod -> Sector -> Real
  diffeomorphismGhostFromGlobalVariation :
    IndependentFieldVariation period hPeriod ->
      EffectiveThroat period hPeriod -> Sector -> TangentVector3
  fullMetricPerturbationFromGlobalVariation :
    IndependentFields period hPeriod ->
      IndependentFieldVariation period hPeriod ->
      EffectiveThroat period hPeriod -> Sector -> SymmetricTensor3
  fullMetricPerturbationSurjective :
    ∀ fields point sector,
      Function.Surjective
        (fun variation =>
          fullMetricPerturbationFromGlobalVariation fields variation point sector)
  matterSpinorIdentification : MatterFiber ≃ Spinor
  modeCoefficient : CompleteLocalField Spinor -> ProductDiracMode -> Complex
  d9FieldIsTangentOfSelectedAction : Prop
  d9HessianDiagonalizedByD10Modes : Prop
  regulatorUsesHessianSpectrumWithExactMultiplicity : Prop
  boundaryAndFredholmDomainsAgree : Prop

end

end P0EFTJanusD9D10ExactFieldContentBridge4D
end JanusFormal
