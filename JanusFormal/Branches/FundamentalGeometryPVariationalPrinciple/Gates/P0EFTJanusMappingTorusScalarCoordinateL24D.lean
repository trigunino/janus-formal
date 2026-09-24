import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCoordinateDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-! Dense genuine scalar polynomials in the canonical physical L2 space. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCoordinateL24D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusMappingTorusScalarCoordinateDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
variable [hPos : Fact (0 < period)]

def scalarCoordinateSmoothMap : scalarCoordinateAlgebra period →ₗ[Real] SmoothQuotientField period hPeriod Real where
  toFun f := ⟨f.val, scalarCoordinateAlgebra_smooth period f⟩
  map_add' f g := by ext point; rfl
  map_smul' r f := by ext point; rfl

def scalarCoordinateToL2 : scalarCoordinateAlgebra period →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (ContinuousMap.toLp (2 : ENNReal) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) Real).comp
    (scalarCoordinateAlgebra period).toSubmodule.subtypeL

theorem scalarCoordinateToL2_eq_smooth (f : scalarCoordinateAlgebra period) :
    scalarCoordinateToL2 period hPeriod f =
      smoothToCanonicalPhysicalBulkL2 period hPeriod (scalarCoordinateSmoothMap period hPeriod f) := by
  rfl

theorem scalarCoordinateToL2_denseRange : DenseRange (scalarCoordinateToL2 period hPeriod) := by
  have hLp := P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D.continuousToCanonicalPhysicalBulkL2_denseRange period hPeriod
  have hSubtype : DenseRange (scalarCoordinateAlgebra period).toSubmodule.subtypeL := by
    change Dense (Set.range (scalarCoordinateAlgebra period).toSubmodule.subtypeL)
    have hRange : Set.range (scalarCoordinateAlgebra period).toSubmodule.subtypeL =
        (scalarCoordinateAlgebra period : Set C(EffectiveQuotient period hPeriod, Real)) := by
      ext f
      exact ⟨fun ⟨g, hg⟩ => hg ▸ g.property, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
    rw [hRange]
    exact scalarCoordinateAlgebra_dense period
  exact hLp.comp hSubtype (ContinuousMap.toLp _ _ _).continuous

end
end P0EFTJanusMappingTorusScalarCoordinateL24D
end JanusFormal
