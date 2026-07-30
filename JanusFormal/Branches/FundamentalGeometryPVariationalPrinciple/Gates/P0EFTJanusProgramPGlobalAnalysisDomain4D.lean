import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertDirichlet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# Common intrinsic analytic domain for Program P

The genuine smooth global tangent is sent to a finite product of intrinsic
physical `H¹` spaces.  The throat trace acts coordinatewise and its
homogeneous kernel is closed.  The physical closed aggregate contains bulk,
SpinC and LL.  A separate legacy extension adds the D10 graph used by
regulator and determinant constructions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAnalysisDomain4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal lp
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertDirichlet4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The background object underlying every bulk coordinate below. -/
def globalEffectiveD8Background : EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

/-- A member of the constructed finite smooth tangent generating family,
viewed as a genuine smooth vector field. -/
def finiteGlobalFrameVector
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    EffectiveD8SmoothVectorField
      (globalEffectiveD8Background period hPeriod) where
  toFun := fun point =>
    (finiteSmoothTangentFrame period hPeriod).vectorAt point index
  contMDiff_toFun :=
    (finiteSmoothTangentFrame period hPeriod).contMDiff_vector index

private abbrev GlobalFrameIndex :=
  Fin (finiteSmoothTangentFrame period hPeriod).count

private abbrev GlobalMetricSobolevSlot :=
  Sector × GlobalFrameIndex period hPeriod ×
    GlobalFrameIndex period hPeriod

private abbrev GlobalGaugeSobolevSlot :=
  Sector × (Fin 4 × Fin 2)

private abbrev GlobalGhostSobolevSlot :=
  Sector × Fin 2

/-- Finite scalar coordinates for all bulk coefficient sectors.  True
spinorial matter and LL data have their own geometric completions below. -/
abbrev GlobalBulkSobolevSlot :=
  GlobalMetricSobolevSlot period hPeriod ⊕
    (GlobalGaugeSobolevSlot ⊕
      (GlobalGhostSobolevSlot ⊕ GlobalGhostSobolevSlot))

private def smoothEuclideanCoordinate
    {Index : Type*} [Fintype Index]
    (field : SmoothQuotientField period hPeriod
      (EuclideanSpace Real Index))
    (index : Index) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point => field point index
  contMDiff_toFun :=
    (EuclideanSpace.proj index).contMDiff.comp field.contMDiff_toFun

/-- Every bulk coordinate is extracted from the unique global tangent.
Metric coefficients use the genuine tensor and the finite intrinsic smooth
spanning family, rather than fixed chart vectors. -/
def GlobalFieldTangent.bulkSmoothCoordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    GlobalBulkSobolevSlot period hPeriod →
      SmoothQuotientField period hPeriod Real
  | .inl (sector, first, second) =>
      effectiveD8SmoothTensorVectorContraction
        (globalEffectiveD8Background period hPeriod)
        (variation.completeVariation.fullMetricPerturbation sector)
        (finiteGlobalFrameVector period hPeriod first)
        (finiteGlobalFrameVector period hPeriod second)
  | .inr (.inl (sector, index)) =>
      smoothEuclideanCoordinate period hPeriod
        (selectSector sector
          variation.completeVariation.independent.gauge) index
  | .inr (.inr (.inl (sector, index))) =>
      smoothEuclideanCoordinate period hPeriod
        (selectSector sector
          variation.completeVariation.independent.ghosts) index
  | .inr (.inr (.inr (sector, index))) =>
      smoothEuclideanCoordinate period hPeriod
        (selectSector sector
          variation.completeVariation.independent.auxiliaries) index

/-- Finite product of intrinsic physical scalar `H¹` completions. -/
abbrev GlobalBulkHilbertH1 :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalScalarHilbertH1 period hPeriod

/-- Corresponding finite product of intrinsic throat `L²` spaces. -/
abbrev GlobalBulkThroatL2 :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalThroatL2 period hPeriod

/-- The smooth global tangent mapped into the common bulk Sobolev space. -/
def GlobalFieldTangent.bulkHilbertH1
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    GlobalBulkHilbertH1 period hPeriod :=
  fun slot =>
    smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod
      (GlobalFieldTangent.bulkSmoothCoordinate
        period hPeriod variation slot)

/-- Coordinatewise continuous trace to the actual throat. -/
def globalBulkHilbertH1Trace :
    GlobalBulkHilbertH1 period hPeriod →L[Real]
      GlobalBulkThroatL2 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    canonicalPhysicalHilbertH1Trace period hPeriod

/-- Common homogeneous boundary domain. -/
abbrev GlobalBulkDirichletHilbertH1 :=
  (globalBulkHilbertH1Trace period hPeriod).ker

theorem globalBulkDirichletHilbertH1_isClosed :
    IsClosed
      (GlobalBulkDirichletHilbertH1 period hPeriod :
        Set (GlobalBulkHilbertH1 period hPeriod)) :=
  (globalBulkHilbertH1Trace period hPeriod).isClosed_ker

@[simp]
theorem globalBulkHilbertH1Trace_agrees_on_globalTangent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration)
    (slot : GlobalBulkSobolevSlot period hPeriod) :
    globalBulkHilbertH1Trace period hPeriod
        (GlobalFieldTangent.bulkHilbertH1
          period hPeriod variation) slot =
      smoothCanonicalPhysicalTraceL2 period hPeriod
        (GlobalFieldTangent.bulkSmoothCoordinate
          period hPeriod variation slot) :=
  canonicalPhysicalHilbertH1Trace_agrees_on_smooth period hPeriod _

/-- The only extra open condition needed by the positive LL energy norm. -/
structure GlobalAnalysisData
    (configuration : GlobalFieldConfiguration period hPeriod) where
  llMeasure_pos :
    ∀ point, 0 < configuration.coefficientFields.llMeasure point

def GlobalAnalysisData.llH1Data
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    PositiveLLH1Data period hPeriod where
  frame := canonicalDivergenceFreeLLFrame period hPeriod
  fields :=
    diagonalScaffold period hPeriod configuration.coefficientFields
  mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  finiteMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  openPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  llMeasure_pos := data.llMeasure_pos

/-- The common closed/operator domain of the physical field content:
bulk Dirichlet `H¹`, one primitive SpinC graph domain per outer sector and the
positive LL Hilbert completion.  D10 is not a physical field direction. -/
structure GlobalPhysicalCommonClosedDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) where
  bulk : GlobalBulkDirichletHilbertH1 period hPeriod
  spinC : Sector → PrimitiveSpinCGeometricH2 period hPeriod
  ll : LLH1Space period hPeriod (data.llH1Data period hPeriod)

theorem globalPhysicalCommonClosedDomain_nonempty
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    Nonempty (GlobalPhysicalCommonClosedDomain period hPeriod data) :=
  ⟨⟨0, 0, 0⟩⟩

/-- Legacy extended analytic aggregate.  It adds the multiplicity-aware D10
graph used by the spectral-regulator and determinant packages to the physical
common domain above. -/
structure GlobalCommonClosedDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
  (data : GlobalAnalysisData period hPeriod configuration) where
  bulk : GlobalBulkDirichletHilbertH1 period hPeriod
  spinC : Sector → PrimitiveSpinCGeometricH2 period hPeriod
  d10 : programPD10FredholmModeDomainSubmodule4D
    (d10SpectralData period hPeriod configuration.d10Completion)
  ll : LLH1Space period hPeriod (data.llH1Data period hPeriod)

theorem globalCommonClosedDomain_nonempty
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    Nonempty (GlobalCommonClosedDomain period hPeriod data) :=
  ⟨⟨0, 0, 0, 0⟩⟩

/-- Forget the background D10 graph coordinate of the extended aggregate. -/
def GlobalCommonClosedDomain.physical
    {configuration : GlobalFieldConfiguration period hPeriod}
    {data : GlobalAnalysisData period hPeriod configuration}
    (domain : GlobalCommonClosedDomain period hPeriod data) :
    GlobalPhysicalCommonClosedDomain period hPeriod data where
  bulk := domain.bulk
  spinC := domain.spinC
  ll := domain.ll

/-- Concrete closure certificate for the common aggregate. -/
structure GlobalAnalysisCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) : Prop where
  bulkDirichletClosed :
    IsClosed
      (GlobalBulkDirichletHilbertH1 period hPeriod :
        Set (GlobalBulkHilbertH1 period hPeriod))
  spinCGraphClosed :
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).IsClosed
  d10GraphClosed :
    IsClosed
      (programPD10FredholmModeGraph4D
        (d10SpectralData period hPeriod configuration.d10Completion))
  commonDomainInhabited :
    Nonempty (GlobalCommonClosedDomain period hPeriod data)

/-- Closure certificate restricted to the physical, D10-free aggregate. -/
structure GlobalPhysicalAnalysisCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) : Prop where
  bulkDirichletClosed :
    IsClosed
      (GlobalBulkDirichletHilbertH1 period hPeriod :
        Set (GlobalBulkHilbertH1 period hPeriod))
  spinCGraphClosed :
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).IsClosed
  commonDomainInhabited :
    Nonempty (GlobalPhysicalCommonClosedDomain period hPeriod data)

theorem globalPhysicalAnalysisCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    GlobalPhysicalAnalysisCertificate period hPeriod data where
  bulkDirichletClosed :=
    globalBulkDirichletHilbertH1_isClosed period hPeriod
  spinCGraphClosed :=
    primitiveSpinCGeometricUnboundedSquared_isClosed period hPeriod
  commonDomainInhabited :=
    globalPhysicalCommonClosedDomain_nonempty period hPeriod data

theorem globalAnalysisCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    GlobalAnalysisCertificate period hPeriod data where
  bulkDirichletClosed :=
    globalBulkDirichletHilbertH1_isClosed period hPeriod
  spinCGraphClosed :=
    primitiveSpinCGeometricUnboundedSquared_isClosed period hPeriod
  d10GraphClosed :=
    programPD10FredholmModeGraph4D_closed
      (d10SpectralData period hPeriod configuration.d10Completion)
  commonDomainInhabited :=
    globalCommonClosedDomain_nonempty period hPeriod data

/-- The canonical zero configuration satisfies the LL positivity condition. -/
def zeroGlobalAnalysisData
    (geometry :
      P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry
        period hPeriod) :
    GlobalAnalysisData period hPeriod
      (zeroGlobalFieldConfiguration period hPeriod geometry) where
  llMeasure_pos := by
    intro point
    norm_num [zeroGlobalFieldConfiguration, constantSmoothThroatField]

end
end P0EFTJanusProgramPGlobalAnalysisDomain4D
end JanusFormal
