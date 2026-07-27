import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9GlobalAbelianH04D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

/-!
# Physical gauge Sobolev complex on the mapping torus

The actual differential `c ↦ dc` is embedded in the canonical physical
`L²` space by evaluation on the finite smooth tangent spanning family.
Full support makes this embedding faithful.  Consequently its kernel is
exactly the already computed global constant gauge mode, and quotienting the
smooth core by that kernel gives the exact range.  The closure of this range
is the completed physical exact-gauge Sobolev space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
open P0EFTJanusCommonPairedD9GlobalAbelianH04D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeOpenPos :
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).IsOpenPosMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Canonical `L²` coordinates of a two-component gauge one-form, evaluated
on the finite smooth tangent spanning family. -/
abbrev PhysicalGaugeOneFormL2 :=
  Fin 2 →
    Fin (finiteSmoothTangentFrame period hPeriod).count →
      CanonicalPhysicalBulkL2 period hPeriod

/-- A smooth scalar coordinate of a smooth intrinsic gauge one-form. -/
def gaugePotentialCoordinateField
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    potential.toFun component point
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point index)
  contMDiff_toFun :=
    (potential.contMDiff_eval component).comp
      ((finiteSmoothTangentFrame period hPeriod).contMDiff_vector index)

/-- Coordinate evaluation is real-linear in the gauge one-form. -/
def gaugePotentialCoordinateLinearMap
    (component : Fin 2)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun := fun potential =>
    gaugePotentialCoordinateField period hPeriod potential component index
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  map_smul' scalar potential := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl

/-- Faithful physical `L²` coordinate embedding of smooth gauge one-forms. -/
def gaugePotentialL2Coordinates :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      PhysicalGaugeOneFormL2 period hPeriod where
  toFun := fun potential component index =>
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (gaugePotentialCoordinateField period hPeriod potential component index)
  map_add' first second := by
    funext component index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add
      (gaugePotentialCoordinateLinearMap period hPeriod component index first)
      (gaugePotentialCoordinateLinearMap period hPeriod component index second)
  map_smul' scalar potential := by
    funext component index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul
      scalar
      (gaugePotentialCoordinateLinearMap period hPeriod component index potential)

theorem gaugePotentialL2Coordinates_injective :
    Function.Injective (gaugePotentialL2Coordinates period hPeriod) := by
  intro first second hEqual
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  let frame := finiteSmoothTangentFrame period hPeriod
  let difference : TangentSpace coverModelWithCorners point →ₗ[Real] Real :=
    (first.toFun component point).toLinearMap -
      (second.toFun component point).toLinearMap
  have hGenerator
      (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
      difference
          ((finiteSmoothTangentFrame period hPeriod).vectorAt point index) = 0 := by
    have hL2 := congrFun (congrFun hEqual component) index
    change
      smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (gaugePotentialCoordinateField period hPeriod first component index) =
        smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (gaugePotentialCoordinateField period hPeriod second component index)
      at hL2
    have hField :=
      smoothFieldToL2_injective period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) hL2
    have hAtPoint := congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point) hField
    simpa [difference, gaugePotentialCoordinateField] using
      sub_eq_zero.mpr hAtPoint
  have hSpanLe :
      Submodule.span Real
          (Set.range
            ((finiteSmoothTangentFrame period hPeriod).vectorAt point)) ≤
        LinearMap.ker difference := by
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    exact hGenerator index
  have hTopLe :
      (⊤ : Submodule Real (TangentSpace coverModelWithCorners point)) ≤
        LinearMap.ker difference := by
    rw [← (finiteSmoothTangentFrame period hPeriod).spansAt point]
    exact hSpanLe
  have hTangent : tangent ∈ LinearMap.ker difference :=
    hTopLe Submodule.mem_top
  simpa [difference] using sub_eq_zero.mp hTangent

/-- The actual global gauge differential, now valued in the physical
canonical `L²` coordinates. -/
def physicalGaugeDifferentialL2 :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      PhysicalGaugeOneFormL2 period hPeriod :=
  (gaugePotentialL2Coordinates period hPeriod).comp
    (abelianGaugeGenerator period hPeriod)

theorem physicalGaugeDifferentialL2_eq_zero_iff
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    physicalGaugeDifferentialL2 period hPeriod ghost = 0 ↔
      abelianGaugeGenerator period hPeriod ghost = 0 := by
  constructor
  · intro hZero
    apply gaugePotentialL2Coordinates_injective period hPeriod
    simpa [physicalGaugeDifferentialL2] using hZero
  · intro hZero
    rw [physicalGaugeDifferentialL2, LinearMap.comp_apply, hZero]
    exact LinearMap.map_zero _

/-- The physical `L²` differential has precisely the global constant gauge
zero modes as kernel. -/
theorem physicalGaugeDifferentialL2_kernel_eq_globalZeroMode :
    LinearMap.ker (physicalGaugeDifferentialL2 period hPeriod) =
      GlobalAbelianGaugeZeroMode period hPeriod := by
  ext ghost
  exact physicalGaugeDifferentialL2_eq_zero_iff period hPeriod ghost

/-- The paired gauge ghost and `L²` one-form spaces occurring in the common
two-sector field package. -/
abbrev PhysicalPairedGaugeGhost :=
  SmoothQuotientField period hPeriod GaugeLieAlgebra ×
    SmoothQuotientField period hPeriod GaugeLieAlgebra

abbrev PhysicalPairedGaugeOneFormL2 :=
  PhysicalGaugeOneFormL2 period hPeriod ×
    PhysicalGaugeOneFormL2 period hPeriod

/-- Componentwise physical differential on the common paired gauge sector. -/
def physicalPairedGaugeDifferentialL2 :
    PhysicalPairedGaugeGhost period hPeriod →ₗ[Real]
      PhysicalPairedGaugeOneFormL2 period hPeriod :=
  (physicalGaugeDifferentialL2 period hPeriod).prodMap
    (physicalGaugeDifferentialL2 period hPeriod)

theorem physicalPairedGaugeDifferentialL2_eq_zero_iff
    (ghosts : PhysicalPairedGaugeGhost period hPeriod) :
    physicalPairedGaugeDifferentialL2 period hPeriod ghosts = 0 ↔
      abelianGaugePairGenerator period hPeriod ghosts = 0 := by
  constructor
  · intro hZero
    change
      (physicalGaugeDifferentialL2 period hPeriod ghosts.1,
        physicalGaugeDifferentialL2 period hPeriod ghosts.2) = 0 at hZero
    change
      (abelianGaugeGenerator period hPeriod ghosts.1,
        abelianGaugeGenerator period hPeriod ghosts.2) = 0
    apply Prod.ext
    · exact (physicalGaugeDifferentialL2_eq_zero_iff
        period hPeriod ghosts.1).1 (congrArg Prod.fst hZero)
    · exact (physicalGaugeDifferentialL2_eq_zero_iff
        period hPeriod ghosts.2).1 (congrArg Prod.snd hZero)
  · intro hZero
    change
      (abelianGaugeGenerator period hPeriod ghosts.1,
        abelianGaugeGenerator period hPeriod ghosts.2) = 0 at hZero
    change
      (physicalGaugeDifferentialL2 period hPeriod ghosts.1,
        physicalGaugeDifferentialL2 period hPeriod ghosts.2) = 0
    apply Prod.ext
    · exact (physicalGaugeDifferentialL2_eq_zero_iff
        period hPeriod ghosts.1).2 (congrArg Prod.fst hZero)
    · exact (physicalGaugeDifferentialL2_eq_zero_iff
        period hPeriod ghosts.2).2 (congrArg Prod.snd hZero)

/-- The paired physical `L²` kernel is exactly the paired global abelian
zero-mode space already used by the common field/BRST package. -/
theorem physicalPairedGaugeDifferentialL2_kernel_eq_globalZeroMode :
    LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod) =
      CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod := by
  ext ghosts
  exact physicalPairedGaugeDifferentialL2_eq_zero_iff period hPeriod ghosts

/-- The full paired physical kernel has the already proved finite-dimensional
global coordinates. -/
def physicalPairedGaugeZeroModeLinearEquiv :
    LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod) ≃ₗ[Real]
      GaugeLieAlgebra × GaugeLieAlgebra := by
  rw [physicalPairedGaugeDifferentialL2_kernel_eq_globalZeroMode
    period hPeriod]
  exact commonPairedD9GlobalAbelianGhostZeroModeLinearEquiv period hPeriod

/-- Smooth paired gauge parameters modulo their full constant kernel. -/
abbrev PhysicalPairedGaugeSobolevCoreQuotient :=
  PhysicalPairedGaugeGhost period hPeriod ⧸
    LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod)

def physicalPairedGaugeSobolevCoreQuotientEquivRange :
    PhysicalPairedGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
      LinearMap.range (physicalPairedGaugeDifferentialL2 period hPeriod) :=
  LinearMap.quotKerEquivRange
    (physicalPairedGaugeDifferentialL2 period hPeriod)

/-- Closed completion of the exact paired gauge range. -/
def PhysicalPairedExactGaugeSobolev :
    Submodule Real (PhysicalPairedGaugeOneFormL2 period hPeriod) :=
  (LinearMap.range
    (physicalPairedGaugeDifferentialL2 period hPeriod)).topologicalClosure

theorem physicalPairedExactGaugeSobolev_isClosed :
    IsClosed
      (PhysicalPairedExactGaugeSobolev period hPeriod :
        Set (PhysicalPairedGaugeOneFormL2 period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def physicalPairedExactGaugeSobolevCompleteSpace :
    CompleteSpace (PhysicalPairedExactGaugeSobolev period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range (physicalPairedGaugeDifferentialL2 period hPeriod))

theorem physicalPairedGaugeDifferentialL2_mem_completion
    (ghosts : PhysicalPairedGaugeGhost period hPeriod) :
    physicalPairedGaugeDifferentialL2 period hPeriod ghosts ∈
      PhysicalPairedExactGaugeSobolev period hPeriod :=
  (LinearMap.range
    (physicalPairedGaugeDifferentialL2 period hPeriod)).le_topologicalClosure
      ⟨ghosts, rfl⟩

/-- Smooth physical gauge parameters modulo constants. -/
abbrev PhysicalGaugeSobolevCoreQuotient :=
  SmoothQuotientField period hPeriod GaugeLieAlgebra ⧸
    LinearMap.ker (physicalGaugeDifferentialL2 period hPeriod)

/-- Algebraic first-isomorphism theorem for the actual physical gauge
differential. -/
def physicalGaugeSobolevCoreQuotientEquivRange :
    PhysicalGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
      LinearMap.range (physicalGaugeDifferentialL2 period hPeriod) :=
  LinearMap.quotKerEquivRange (physicalGaugeDifferentialL2 period hPeriod)

/-- Closed `L²` completion of exact physical gauge one-forms. -/
def PhysicalExactGaugeSobolev :
    Submodule Real (PhysicalGaugeOneFormL2 period hPeriod) :=
  (LinearMap.range
    (physicalGaugeDifferentialL2 period hPeriod)).topologicalClosure

theorem physicalExactGaugeSobolev_isClosed :
    IsClosed
      (PhysicalExactGaugeSobolev period hPeriod :
        Set (PhysicalGaugeOneFormL2 period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def physicalExactGaugeSobolevCompleteSpace :
    CompleteSpace (PhysicalExactGaugeSobolev period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range (physicalGaugeDifferentialL2 period hPeriod))

theorem physicalGaugeDifferentialL2_mem_completion
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    physicalGaugeDifferentialL2 period hPeriod ghost ∈
      PhysicalExactGaugeSobolev period hPeriod :=
  (LinearMap.range
    (physicalGaugeDifferentialL2 period hPeriod)).le_topologicalClosure
      ⟨ghost, rfl⟩

/-- Physical Sobolev/cohomology closure certificate for the genuine mapping
torus gauge complex. -/
theorem physical_gauge_sobolev_complex_gate :
    LinearMap.ker (physicalGaugeDifferentialL2 period hPeriod) =
        GlobalAbelianGaugeZeroMode period hPeriod ∧
      Nonempty
        (PhysicalGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
          LinearMap.range (physicalGaugeDifferentialL2 period hPeriod)) ∧
      IsClosed
        (PhysicalExactGaugeSobolev period hPeriod :
          Set (PhysicalGaugeOneFormL2 period hPeriod)) ∧
      (∀ ghost, physicalGaugeDifferentialL2 period hPeriod ghost ∈
        PhysicalExactGaugeSobolev period hPeriod) ∧
      Nonempty
        (GlobalAbelianGaugeZeroMode period hPeriod ≃ₗ[Real] Real × Real) := by
  exact ⟨physicalGaugeDifferentialL2_kernel_eq_globalZeroMode period hPeriod,
    ⟨physicalGaugeSobolevCoreQuotientEquivRange period hPeriod⟩,
    physicalExactGaugeSobolev_isClosed period hPeriod,
    physicalGaugeDifferentialL2_mem_completion period hPeriod,
    ⟨globalAbelianGaugeZeroModeRealPairLinearEquiv period hPeriod⟩⟩

/-- Closure certificate for the complete paired gauge sector used by the
global Program-P field package. -/
theorem physical_paired_gauge_sobolev_complex_gate :
    LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod) =
        CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ∧
      Nonempty
        (PhysicalPairedGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
          LinearMap.range
            (physicalPairedGaugeDifferentialL2 period hPeriod)) ∧
      IsClosed
        (PhysicalPairedExactGaugeSobolev period hPeriod :
          Set (PhysicalPairedGaugeOneFormL2 period hPeriod)) ∧
      (∀ ghosts, physicalPairedGaugeDifferentialL2 period hPeriod ghosts ∈
        PhysicalPairedExactGaugeSobolev period hPeriod) ∧
      Nonempty
        (LinearMap.ker
            (physicalPairedGaugeDifferentialL2 period hPeriod) ≃ₗ[Real]
          GaugeLieAlgebra × GaugeLieAlgebra) := by
  exact
    ⟨physicalPairedGaugeDifferentialL2_kernel_eq_globalZeroMode
      period hPeriod,
    ⟨physicalPairedGaugeSobolevCoreQuotientEquivRange period hPeriod⟩,
    physicalPairedExactGaugeSobolev_isClosed period hPeriod,
    physicalPairedGaugeDifferentialL2_mem_completion period hPeriod,
    ⟨physicalPairedGaugeZeroModeLinearEquiv period hPeriod⟩⟩

end
end P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
end JanusFormal
