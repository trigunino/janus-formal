import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9LinearBRSTBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D

/-!
# Paired linear BRST ghosts on the complete Program-P variation

This gate stores the two genuine global abelian ghost fields and the smooth
throat diffeomorphism ghost of the existing linear BRST block in the matching
slots of `ProgramPCompleteVariation4D`.  It proves exact D9 agreement,
nilpotence after this ghost-coordinate realization, admissibility of the BRST
image for the current Dirichlet domain, and invariance of the present
matter--LL action sector.

The intrinsic abelian gauge potentials are deliberately not inserted into the
coordinate-valued gauge slot, so this is not a Maxwell or nonlinear/global
diffeomorphism-BRST completion.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationPairedLinearBRSTBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusCommonPairedD9GhostPacket4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Ghost-coordinate realization of the paired linear BRST block in the
matching independent and geometric-ghost slots of the complete variation. -/
def completeVariationPairedLinearBRSTGhosts
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod where
  independent := ghostOnlyIndependentVariation period hPeriod
    (state.firstU1.ghost, state.secondU1.ghost)
  normalDisplacement := fun _ => zeroNormalDisplacement period hPeriod
  diffeomorphismGhost := fun _ => state.diffeomorphismGhost
  fullMetricPerturbation := fun _ => zeroSymmetricTensor period hPeriod

@[simp] theorem completeVariationPairedLinearBRSTGhosts_independent
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    (completeVariationPairedLinearBRSTGhosts period hPeriod state).independent =
      (state.toGhostPacket period hPeriod).independentVariation period hPeriod :=
  rfl

@[simp] theorem completeVariationPairedLinearBRSTGhosts_diffeomorphismGhost
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) (sector : Sector) :
    (completeVariationPairedLinearBRSTGhosts period hPeriod state
      ).diffeomorphismGhost sector = state.diffeomorphismGhost :=
  rfl

/-- The exact paired D9 ghost coordinate read from the complete variation. -/
def completeVariationPairedGhostCoordinate
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    D9PairedGhostCoordinateSpace :=
  d9PairedProgramGhostCoordinateFull period hPeriod variation.independent column
    (variation.diffeomorphismGhost .plus) point

/-- The complete-variation observation is definitionally the existing paired
D9 observation of the same two abelian ghosts and throat tangent ghost. -/
theorem completeVariationPairedGhostCoordinate_eq_common
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    completeVariationPairedGhostCoordinate period hPeriod
        (completeVariationPairedLinearBRSTGhosts period hPeriod state)
        column point =
      commonPairedD9GhostCoordinate period hPeriod
        (state.toGhostPacket period hPeriod) column point :=
  rfl

/-- One BRST step kills precisely the three ghost coordinates observed by
this D9 packet. -/
theorem completeVariationPairedLinearBRSTGhosts_BRST_d9Coordinate
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    completeVariationPairedGhostCoordinate period hPeriod
        (completeVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state))
        column point = 0 :=
  commonPairedD9LinearBRSTDifferential_d9Coordinate period hPeriod state
    column point

/-- The already-proved square-zero differential remains square-zero after
realization in the complete variation type. -/
theorem completeVariationPairedLinearBRSTGhosts_BRST_square
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    completeVariationPairedLinearBRSTGhosts period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state)) =
      completeVariationPairedLinearBRSTGhosts period hPeriod
        (zeroCommonPairedD9LinearBRSTBlock period hPeriod) := by
  rw [commonPairedD9LinearBRSTDifferential_square_zero]

/-- Since this realization retains only ghost coordinates, one BRST step is
already its zero complete ghost variation; the generated gauge potential is
not misidentified with the coordinate gauge slot. -/
theorem completeVariationPairedLinearBRSTGhosts_BRST_eq_zero
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    completeVariationPairedLinearBRSTGhosts period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod state) =
      completeVariationPairedLinearBRSTGhosts period hPeriod
        (zeroCommonPairedD9LinearBRSTBlock period hPeriod) :=
  rfl

private theorem independentFieldCurve_zeroGhostDirection
    (fields : IndependentFields period hPeriod) (parameter : Real) :
    independentFieldCurve period hPeriod fields
        (ghostOnlyIndependentVariation period hPeriod (0, 0)) parameter =
      fields := by
  apply IndependentFields.ext
  · exact metricCurve_zeroSmoothDiagonalMetricVariation period hPeriod
      fields.metrics parameter
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]
  · simp [independentFieldCurve, ghostOnlyIndependentVariation]

/-- The zero complete ghost direction preserves the exact boundary datum of
every common domain. -/
theorem zeroPairedLinearBRSTGhosts_mem_boundaryDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    completeVariationPairedLinearBRSTGhosts period hPeriod
        (zeroCommonPairedD9LinearBRSTBlock period hPeriod) ∈
      programPBoundaryTangentDomain4D period hPeriod domain := by
  intro parameter
  change independentBoundaryTrace period hPeriod
      (independentFieldCurve period hPeriod domain.configuration
        (ghostOnlyIndependentVariation period hPeriod (0, 0)) parameter) =
    domain.boundary
  rw [independentFieldCurve_zeroGhostDirection period hPeriod]
  exact domain.boundary_coherent

/-- Hence the BRST image is admissible for the current complete Program-P
boundary domain.  No boundary condition on an intrinsic gauge potential is
claimed. -/
theorem completeVariationPairedLinearBRSTGhosts_BRST_mem_boundaryDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    completeVariationPairedLinearBRSTGhosts period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod state) ∈
      programPBoundaryTangentDomain4D period hPeriod domain := by
  rw [completeVariationPairedLinearBRSTGhosts_BRST_eq_zero]
  exact zeroPairedLinearBRSTGhosts_mem_boundaryDomain period hPeriod domain

/-- The present matter--LL action is exactly insensitive to this linear
ghost-coordinate BRST step.  This does not assert Maxwell or EH invariance. -/
theorem matterLLActionCurve_pairedLinearBRSTGhosts
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (parameter : Real) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state))
        mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod state)
        mu parameter :=
  rfl

/-- The corresponding matter--LL first variation is likewise unchanged. -/
theorem matterLLFirstVariation_pairedLinearBRSTGhosts
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state)) mu =
      completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod state) mu :=
  rfl

/-- Both arguments of the sectorial matter--LL Hessian retain the same value
after the paired linear BRST step. -/
theorem matterLLHessian_pairedLinearBRSTGhosts
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : CommonPairedD9LinearBRSTBlock period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod first))
        (completeVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod second)) mu =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationPairedLinearBRSTGhosts period hPeriod first)
        (completeVariationPairedLinearBRSTGhosts period hPeriod second) mu :=
  rfl

end
end P0EFTJanusCompleteVariationPairedLinearBRSTBridge4D
end JanusFormal
