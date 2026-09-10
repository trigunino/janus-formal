import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D

/-!
# Affine jet realization of the T05 cut-bulk Stokes current

This gate realizes the canonical scalar cut-bulk current inside the genuine
order-one/order-two jet calculus of Gate 879.  One of the three formal throat
directions is used for the collar normal.  The value coefficient stores the
actual scalar current and its first coefficient in that direction stores the
actual normal derivative.  The affine horizontal divergence of Gate 883 is
therefore exactly the local bulk density entering T05's proved global Stokes
theorem.

Consequently the integrated jet divergence is the genuine non-null relative
boundary in the Gate-819 carrier.  No Stokes hypothesis or other propositional
field is introduced.  This is the maximal common scalar-current sector of the
present carriers: it does not identify arbitrary fixed-frame T02 jet sections
with geometric collar jets, prove tangential holonomicity, or fill the null and
joint strata.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The first formal throat direction represents the positive collar normal
in this concrete scalar-current realization. -/
def programPT06CutBulkNormalDirection : Fin 3 := 0

/-- The value multi-index in an order-one spatial jet. -/
def programPT06CutBulkFirstOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 1 :=
  ⟨0, by simp⟩

/-- The universal affine jet current which reads the value coefficient in the
chosen normal direction and vanishes in the two tangential directions. -/
def programPT06CanonicalCutBulkNormalAffineCurrent :
    ProgramPT06AffineHorizontalCurrent4D Real where
  constant := 0
  linear direction :=
    if direction = programPT06CutBulkNormalDirection then
      ContinuousLinearMap.proj programPT06CutBulkFirstOrderZeroMultiIndex
    else
      0

@[simp] theorem programPT06CanonicalCutBulkNormalAffineCurrent_linear_self :
    programPT06CanonicalCutBulkNormalAffineCurrent.linear
        programPT06CutBulkNormalDirection =
      (ContinuousLinearMap.proj programPT06CutBulkFirstOrderZeroMultiIndex :
        ThroatSpatialMultiindexJet1 Real →L[Real] Real) := by
  simp [programPT06CanonicalCutBulkNormalAffineCurrent]

@[simp] theorem programPT06CanonicalCutBulkNormalAffineCurrent_linear_of_ne
    (direction : Fin 3)
    (hDirection : direction ≠ programPT06CutBulkNormalDirection) :
    programPT06CanonicalCutBulkNormalAffineCurrent.linear direction = 0 := by
  simp [programPT06CanonicalCutBulkNormalAffineCurrent, hDirection]

private theorem throatSpatialCoordinateMultiIndex_ne_zero
    (direction : Fin 3) :
    throatSpatialCoordinateMultiIndex direction ≠ 0 := by
  intro hIndex
  have hOrder := congrArg throatSpatialMultiIndexOrder hIndex
  simp at hOrder

/-- The concrete second jet over the cut collar.  Only the value and chosen
normal first-derivative coefficients are needed by this sector. -/
def programPT06CanonicalCutBulkNormalSecondJet
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    ThroatSpatialMultiindexJet2 Real :=
  fun index ↦
    if index.1 = 0 then
      cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal)
    else if index.1 = throatSpatialCoordinateMultiIndex
        programPT06CutBulkNormalDirection then
      deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal
    else
      0

@[simp] theorem programPT06CanonicalCutBulkNormalSecondJet_value
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test base
        normal programPT06SecondOrderZeroMultiIndex =
      cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal) := by
  simp [programPT06CanonicalCutBulkNormalSecondJet,
    programPT06SecondOrderZeroMultiIndex]

@[simp] theorem programPT06CanonicalCutBulkNormalSecondJet_normalFirst
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test base
        normal
        (programPT06SecondOrderFirstMultiIndex
          programPT06CutBulkNormalDirection) =
      deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal := by
  simp [programPT06CanonicalCutBulkNormalSecondJet,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- On the realized jet, the chosen affine current component is the actual
cut-bulk scalar current. -/
theorem programPT06CanonicalCutBulkNormalAffineCurrent_component_eq_current
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    programPT06AffineHorizontalCurrentComponent
        programPT06CanonicalCutBulkNormalAffineCurrent
        programPT06CutBulkNormalDirection
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2)
          (programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test
            base normal)) =
      cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal) := by
  simp [programPT06AffineHorizontalCurrentComponent,
    programPT06CanonicalCutBulkNormalAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    truncateThroatSpatialMultiindexJet,
    programPT06CanonicalCutBulkNormalSecondJet]

@[simp] theorem
    programPT06CanonicalCutBulkNormalAffineCurrent_linear_totalDerivative
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    programPT06CanonicalCutBulkNormalAffineCurrent.linear
        programPT06CutBulkNormalDirection
        (throatSpatialTotalDerivative programPT06CutBulkNormalDirection
          (programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test
            base normal)) =
      deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal := by
  simp [programPT06CanonicalCutBulkNormalAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    throatSpatialTotalDerivative,
    programPT06CanonicalCutBulkNormalSecondJet,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- The Gate-883 affine horizontal divergence is pointwise the genuine local
bulk density used by the canonical cut-collar Stokes theorem. -/
theorem programPT06CanonicalCutBulkNormalAffineDivergence_eq_deriv
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    programPT06AffineHorizontalCurrentDivergence
        programPT06CanonicalCutBulkNormalAffineCurrent
        (programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test
          base normal) =
      deriv (fun current ↦ cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) normal := by
  rw [programPT06AffineHorizontalCurrentDivergence_apply]
  rw [Finset.sum_eq_single programPT06CutBulkNormalDirection]
  · exact programPT06CanonicalCutBulkNormalAffineCurrent_linear_totalDerivative
      period hPeriod field test base normal
  · intro direction _ hDirection
    rw [programPT06CanonicalCutBulkNormalAffineCurrent_linear_of_ne direction
      hDirection]
    rfl
  · simp

/-- The realized divergence remains in Gate 883's certified Euler kernel. -/
theorem programPT06CanonicalCutBulkNormalAffineDivergence_euler_eq_zero
    (jet : ThroatSpatialMultiindexJet4 Real) :
    programPT06SecondOrderLocalEuler
        (programPT06AffineHorizontalCurrentDivergence
          programPT06CanonicalCutBulkNormalAffineCurrent) jet = 0 := by
  exact programPT06SecondOrderLocalEuler_horizontalDivergence_eq_zero
    programPT06CanonicalCutBulkNormalAffineCurrent jet

/-- T05's local cochain with its bulk density presented by the genuine affine
jet divergence above and its boundary density left geometric. -/
def programPT06CanonicalCutBulkJetLocalDensityCochain
    (field test : SmoothQuotientField period hPeriod Real) :
    ProgramPT05CutBulkNonNullLocalDensityCochain period hPeriod where
  bulkDensity base normal :=
    programPT06AffineHorizontalCurrentDivergence
      programPT06CanonicalCutBulkNormalAffineCurrent
      (programPT06CanonicalCutBulkNormalSecondJet period hPeriod field test base
        normal)
  nonNullBoundaryDensity base :=
    cutBoundaryScalarCurrent period hPeriod field test
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

/-- The jet presentation is exactly the existing geometric T05 local cochain,
not a parallel abstract carrier. -/
theorem programPT06CanonicalCutBulkJetLocalDensityCochain_eq_geometric
    (field test : SmoothQuotientField period hPeriod Real) :
    programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod field test =
      programPT05CanonicalCutBulkLocalDensityCochain period hPeriod field test := by
  apply congrArg₂ ProgramPT05CutBulkNonNullLocalDensityCochain.mk
  · funext base normal
    exact programPT06CanonicalCutBulkNormalAffineDivergence_eq_deriv
      period hPeriod field test base normal
  · rfl

/-- The integrated local jet divergence obeys the already proved global
cut-bulk Stokes theorem, with no additional premise. -/
theorem programPT06CanonicalCutBulkJetLocalDensity_stokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    programPT05CutBulkDensityIntegral period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
          field test) =
      -programPT05NonNullBoundaryDensityIntegral period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
          field test) := by
  rw [programPT06CanonicalCutBulkJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalCutBulkLocalDensity_stokes period hPeriod
    massSquared field test

/-- On the realized non-null face, integration carries the local affine jet
divergence to the exact Gate-819 relative boundary. -/
theorem programPT06CanonicalCutBulkJetLocalDensity_dH_nonNull
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    (programPT05ExactT03RelativeBicomplex.dH 4 0
      (programPT05CutBulkDensityIntegratedCochain period hPeriod
        (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
          field test))) .nonNullBoundary =
    (programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
      (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
        field test)) .nonNullBoundary := by
  rw [programPT06CanonicalCutBulkJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalCutBulkLocalDensity_dH_nonNull period hPeriod
    massSquared field test

end
end P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D
end JanusFormal
