import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopolePhaseDerivative4D

/-!
# Global descent of the primitive geometric SpinC Dirac operator

The north/south derivative law is already exact.  This gate proves the
remaining normal-root covariance and combines both cocycles so that the
local geometric Dirac expression descends to the genuine primitive bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped BigOperators Bundle Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePhaseDerivative4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance primitiveSpinCCoreIsContMDiff
    (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ :=
  d9PrimitiveSpinCVectorBundleCore_isContMDiff
    period hPeriod choice

local instance primitiveSpinCTotalSpaceTopology
    (choice : NormalRootChoice) :
    TopologicalSpace
      (Bundle.TotalSpace D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice)) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance primitiveSpinCFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).fiberBundle

local instance primitiveSpinCVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).vectorBundle

/-- The ordinary directional derivative transforms by the locally constant
normal-root monodromy. -/
theorem d9PrimitiveSpinCLocalFlatFrameDerivative_normal_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (first second : ThroatCover period hPeriod)
    (chart : MonopoleChart)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second)
    (hChart :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod chart) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice family
        (second, chart) direction base =
      d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod first second base)
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family
          (first, chart) direction base) := by
  let winding :=
    localTransitionWinding period hPeriod first second base
  let firstField := family.localValue (first, chart)
  let transformedField :=
    d9DoubledMatterSpinorMonodromyCLM choice winding ∘ firstField
  let tangent := d9IntrinsicThroatFrame period hPeriod direction base
  have hFirstDiff :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) firstField base := by
    exact
      ((family.contMDiffOn_localValue
        (first, chart)).contMDiffAt
          ((d9PrimitiveSpinCBaseSet_isOpen
            period hPeriod (first, chart)).mem_nhds
              ⟨hFirst, hChart⟩)).mdifferentiableAt (by simp)
  have hMonodromyDiff :
      MDifferentiableAt
        𝓘(Real, D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        (d9DoubledMatterSpinorMonodromyCLM choice winding)
        (firstField base) :=
    (d9DoubledMatterSpinorMonodromyCLM choice winding)
      |>.differentiableAt.mdifferentiableAt
  have hChain :=
    mfderiv_comp_apply base hMonodromyDiff hFirstDiff tangent
  have hOuter :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9DoubledMatterSpinorMonodromy choice winding
            (firstField base))
          (mfderiv
            𝓘(Real, D9DoubledMatterFiber)
            𝓘(Real, D9DoubledMatterFiber)
            (d9DoubledMatterSpinorMonodromyCLM choice winding)
            (firstField base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              firstField base tangent)) =
        d9DoubledMatterSpinorMonodromy choice winding
          (d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family
            (first, chart) direction base) := by
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  have hChainFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (d9DoubledMatterSpinorMonodromy choice winding
        (firstField base)))
    hChain
  have hActionResult := hChainFiber.trans hOuter
  have hTransformedDerivative :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (transformedField base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            transformedField base tangent) =
        d9DoubledMatterSpinorMonodromy choice winding
          (d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family
            (first, chart) direction base) := by
    dsimp [transformedField]
    convert hActionResult using 1 <;> rfl
  have hWinding :=
    localTransitionWinding_eventuallyEq
      period hPeriod first second base ⟨hFirst, hSecond⟩
  have hCommonOpen :
      IsOpen
        ((normalBundleBaseSet period hPeriod first ∩
            normalBundleBaseSet period hPeriod second) ∩
          d9PrimitiveMonopoleChartDomain period hPeriod chart) :=
    ((normalBundleBaseSet_isOpen period hPeriod first).inter
      (normalBundleBaseSet_isOpen period hPeriod second)).inter
      (d9PrimitiveMonopoleChartDomain_isOpen
        period hPeriod chart)
  have hEventually :
      family.localValue (second, chart) =ᶠ[𝓝 base]
        transformedField := by
    filter_upwards
      [hWinding,
        hCommonOpen.mem_nhds ⟨⟨hFirst, hSecond⟩, hChart⟩]
      with current hCurrentWinding hCurrent
    have hCoord :=
      family.coordChange_localValue
        (first, chart) (second, chart) current
        ⟨⟨hCurrent.1.1, hCurrent.2⟩,
          ⟨hCurrent.1.2, hCurrent.2⟩⟩
    dsimp [transformedField, firstField, winding]
    simpa [d9PrimitiveSpinCCoordChange,
      d9PrimitiveSpinCPhaseTransition, hCurrentWinding] using hCoord.symm
  have hDerivative :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners)
      (I' := 𝓘(Real, D9DoubledMatterFiber)) hEventually
  have hApply := congrArg (fun derivative => derivative tangent) hDerivative
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  dsimp [firstField, winding, tangent] at hTransformedDerivative ⊢
  rw [hApply]
  exact hTransformedDerivative

/-- The infinitesimal complex generator commutes with normal-root
monodromy. -/
theorem d9PrimitiveSpinCImaginaryAction_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCImaginaryAction matter) := by
  unfold d9PrimitiveSpinCImaginaryAction
  exact d9PrimitiveSpinCPhaseAction_monodromy
    choice winding d9PrimitiveSpinCImaginaryPhase matter

/-- The radial Levi--Civita correction commutes with normal-root
monodromy. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base matter) := by
  change
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9DoubledMatterSpinorMonodromyCLM choice winding matter) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base matter)
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp only [hSame, ↓reduceIte]
    exact
      (d9DoubledMatterSpinorMonodromyCLM
        choice winding).map_zero.symm
  · simp only [hSame, ↓reduceIte, map_smul,
      d9DoubledMatterFiberCliffordGammaCLM_apply]
    congr 1
    change
      d9DoubledMatterFiberCliffordGamma direction
          (d9DoubledMatterFiberCliffordGamma other
            (d9DoubledMatterSpinorMonodromy choice winding matter)) =
        d9DoubledMatterSpinorMonodromy choice winding
          (d9DoubledMatterFiberCliffordGamma direction
            (d9DoubledMatterFiberCliffordGamma other matter))
    rw [d9DoubledMatterFiberCliffordGamma_monodromy,
      d9DoubledMatterFiberCliffordGamma_monodromy]

/-- Local values transform by normal-root monodromy when the monopole chart
is held fixed. -/
theorem d9PrimitiveSpinCLocalValue_normal_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (first second : ThroatCover period hPeriod)
    (chart : MonopoleChart) (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second)
    (hChart :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod chart) :
    family.localValue (second, chart) base =
      d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod first second base)
        (family.localValue (first, chart) base) := by
  have hCoord :=
    family.coordChange_localValue
      (first, chart) (second, chart) base
      ⟨⟨hFirst, hChart⟩, ⟨hSecond, hChart⟩⟩
  simpa [d9PrimitiveSpinCCoordChange,
    d9PrimitiveSpinCPhaseTransition] using hCoord.symm

/-- The complete Levi--Civita frame derivative is normal-root covariant. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_normal_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (first second : ThroatCover period hPeriod)
    (chart : MonopoleChart)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second)
    (hChart :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod chart) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family
        (second, chart) direction base =
      d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod first second base)
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family
          (first, chart) direction base) := by
  have hFlat :=
    d9PrimitiveSpinCLocalFlatFrameDerivative_normal_exact
      period hPeriod choice family first second chart direction base
      hFirst hSecond hChart
  have hValue :=
    d9PrimitiveSpinCLocalValue_normal_exact
      period hPeriod choice family first second chart base
      hFirst hSecond hChart
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [hFlat, hValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_monodromy]
  exact
    (d9DoubledMatterSpinorMonodromyCLM choice
      (localTransitionWinding period hPeriod first second base)).map_add
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family (first, chart) direction base)
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base
          (family.localValue (first, chart) base)) |>.symm

/-- One coupled local directional derivative commutes with normal-root
monodromy. -/
theorem d9PrimitiveSpinCLocalDirectionalDerivative_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (connectionCoefficient : Real)
    (ordinaryDerivative matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirectionalDerivative connectionCoefficient
        (d9DoubledMatterSpinorMonodromy choice winding ordinaryDerivative)
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCLocalDirectionalDerivative
          connectionCoefficient ordinaryDerivative matter) := by
  change
    d9PrimitiveSpinCLocalDirectionalDerivative connectionCoefficient
        (d9DoubledMatterSpinorMonodromyCLM choice winding ordinaryDerivative)
        (d9DoubledMatterSpinorMonodromyCLM choice winding matter) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9PrimitiveSpinCLocalDirectionalDerivative
          connectionCoefficient ordinaryDerivative matter)
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
  rw [map_add, map_smul]
  congr 1
  exact congrArg (fun value => connectionCoefficient • value)
    (d9PrimitiveSpinCImaginaryAction_monodromy
      choice winding matter)

/-- The complete local Clifford contraction commutes with normal-root
monodromy. -/
theorem d9PrimitiveSpinCLocalDirac_monodromy
    (choice : NormalRootChoice) (winding : Int)
    (connectionCoefficient : Fin 3 → Real)
    (ordinaryDerivative : Fin 3 → D9DoubledMatterFiber)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirac connectionCoefficient
        (fun direction =>
          d9DoubledMatterSpinorMonodromy choice winding
            (ordinaryDerivative direction))
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCLocalDirac
          connectionCoefficient ordinaryDerivative matter) := by
  change
    d9PrimitiveSpinCLocalDirac connectionCoefficient
        (fun direction =>
          d9DoubledMatterSpinorMonodromyCLM choice winding
            (ordinaryDerivative direction))
        (d9DoubledMatterSpinorMonodromyCLM choice winding matter) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9PrimitiveSpinCLocalDirac
          connectionCoefficient ordinaryDerivative matter)
  unfold d9PrimitiveSpinCLocalDirac
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  have hDirectional :=
    d9PrimitiveSpinCLocalDirectionalDerivative_monodromy
      choice winding (connectionCoefficient direction)
      (ordinaryDerivative direction) matter
  change
    d9PrimitiveSpinCLocalDirectionalDerivative
        (connectionCoefficient direction)
        (d9DoubledMatterSpinorMonodromyCLM choice winding
          (ordinaryDerivative direction))
        (d9DoubledMatterSpinorMonodromyCLM choice winding matter) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9PrimitiveSpinCLocalDirectionalDerivative
          (connectionCoefficient direction)
          (ordinaryDerivative direction) matter) at hDirectional
  rw [hDirectional]
  change
    d9DoubledMatterFiberCliffordGamma direction
        (d9DoubledMatterSpinorMonodromy choice winding
          (d9PrimitiveSpinCLocalDirectionalDerivative
            (connectionCoefficient direction)
            (ordinaryDerivative direction) matter)) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9DoubledMatterFiberCliffordGamma direction
          (d9PrimitiveSpinCLocalDirectionalDerivative
            (connectionCoefficient direction)
            (ordinaryDerivative direction) matter))
  exact d9DoubledMatterFiberCliffordGamma_monodromy
    choice direction winding _

/-- The local geometric Dirac expression is normal-root covariant. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_normal_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (first second : ThroatCover period hPeriod)
    (chart : MonopoleChart) (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second)
    (hChart :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family (second, chart) base =
      d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod first second base)
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (first, chart) base) := by
  let winding :=
    localTransitionWinding period hPeriod first second base
  have hValue :=
    d9PrimitiveSpinCLocalValue_normal_exact
      period hPeriod choice family first second chart base
      hFirst hSecond hChart
  have hDerivatives :
      (fun direction =>
        d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family
          (second, chart) direction base) =
        (fun direction =>
          d9DoubledMatterSpinorMonodromy choice winding
            (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
              period hPeriod choice family
              (first, chart) direction base)) := by
    funext direction
    exact d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_normal_exact
      period hPeriod choice family first second chart direction base
      hFirst hSecond hChart
  unfold d9PrimitiveSpinCLocalGeometricDirac
  rw [hValue, hDerivatives]
  exact d9PrimitiveSpinCLocalDirac_monodromy
    choice winding
    (fun direction =>
      d9PrimitiveSpinCTotalConnectionFrameCoefficient
        period hPeriod chart direction base)
    (fun direction =>
      d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family
        (first, chart) direction base)
    (family.localValue (first, chart) base)

/-- Full coordinate-change law for the geometric Dirac output on every
joint normal-root/monopole overlap. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_coordChange_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) :
    d9PrimitiveSpinCCoordChange period hPeriod choice
        first second base
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family first base) =
      d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family second base := by
  have hNormal :=
    d9PrimitiveSpinCLocalGeometricDirac_normal_exact
      period hPeriod choice family first.1 second.1 first.2 base
      hBase.1.1 hBase.2.1 hBase.1.2
  rcases first with ⟨firstNormal, firstChart⟩
  rcases second with ⟨secondNormal, secondChart⟩
  cases firstChart <;> cases secondChart
  · simpa [d9PrimitiveSpinCCoordChange,
      d9PrimitiveSpinCPhaseTransition] using hNormal.symm
  · have hGauge :=
      d9PrimitiveSpinCLocalGeometricDirac_north_south_exact
        period hPeriod choice family secondNormal base
        hBase.2.1 hBase.1.2 hBase.2.2
    change
      d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              firstNormal secondNormal base)
            (d9PrimitiveSpinCLocalGeometricDirac
              period hPeriod choice family
              (firstNormal, .north) base)) =
        d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (secondNormal, .south) base
    rw [← hNormal]
    exact hGauge.symm
  · have hGauge :=
      d9PrimitiveSpinCLocalGeometricDirac_north_south_exact
        period hPeriod choice family secondNormal base
        hBase.2.1 hBase.2.2 hBase.1.2
    change
      d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .south .north base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              firstNormal secondNormal base)
            (d9PrimitiveSpinCLocalGeometricDirac
              period hPeriod choice family
              (firstNormal, .south) base)) =
        d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (secondNormal, .north) base
    rw [← hNormal]
    rw [hGauge]
    rw [← d9PrimitiveSpinCPhaseAction_mul]
    simp [d9PrimitiveSpinCPhaseTransition,
      primitiveMonopoleTransition]
  · simpa [d9PrimitiveSpinCCoordChange,
      d9PrimitiveSpinCPhaseTransition] using hNormal.symm

/-- Each ordinary frame derivative remains smooth on its local joint chart. -/
theorem d9PrimitiveSpinCLocalFlatFrameDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (fun base =>
        d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family index direction base)
      (d9PrimitiveSpinCBaseSet period hPeriod index) := by
  let localField := family.localValue index
  let frame :=
    d9IntrinsicThroatFrame period hPeriod direction
  let frameTotal :
      ThroatBase period hPeriod →
        TangentBundle throatCoverModelWithCorners
          (ThroatBase period hPeriod) :=
    fun base => ⟨base, frame base⟩
  let localSet := d9PrimitiveSpinCBaseSet period hPeriod index
  have hLocalField :
      ContMDiffOn throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        localField localSet :=
    family.contMDiffOn_localValue index
  have hLocalOpen : IsOpen localSet :=
    d9PrimitiveSpinCBaseSet_isOpen period hPeriod index
  have hTangentMap :=
    hLocalField.contMDiffOn_tangentMapWithin
      (m := ∞) (by simp) hLocalOpen.uniqueMDiffOn
  have hFrame :
      ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners.tangent ∞ frameTotal := by
    exact
      (d9IntrinsicThroatFrame
        period hPeriod direction).contMDiff_toFun
  have hFrameMaps :
      MapsTo frameTotal localSet
        (Bundle.TotalSpace.proj ⁻¹' localSet) := by
    intro base hBase
    exact hBase
  have hComposed :=
    hTangentMap.comp hFrame.contMDiffOn hFrameMaps
  have hDerivative :
      ContMDiffOn throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        (fun base =>
          (tangentMapWithin throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            localField localSet (frameTotal base)).2)
        localSet :=
    (contMDiff_snd_tangentBundle_modelSpace
      D9DoubledMatterFiber
      𝓘(Real, D9DoubledMatterFiber)).comp_contMDiffOn hComposed
  apply hDerivative.congr
  intro base hBase
  have hLocalDiff :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) localField base :=
    (hLocalField.contMDiffAt
      (hLocalOpen.mem_nhds hBase)).mdifferentiableAt (by simp)
  rw [tangentMapWithin_eq_tangentMap
    (hLocalOpen.uniqueMDiffWithinAt hBase) hLocalDiff]
  rfl

/-- Pulled-back sphere coordinates are globally smooth on the throat. -/
theorem d9PrimitiveMonopoleBaseCoordinate_contMDiff
    (coordinate : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate) := by
  exact (monopoleSphereCoordinate_contMDiff coordinate).comp
    ((d9ThroatMonopoleSphereProjection_contMDiff
      period hPeriod).of_le (by simp))

/-- Intrinsic-frame derivatives of the pulled-back sphere coordinates are
globally smooth. -/
theorem d9PrimitiveMonopoleCoordinateFrameDerivative_contMDiff
    (coordinate direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod coordinate direction) := by
  have hCoordinate :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod coordinate
  have hDerivative :=
    (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp
      ((hCoordinate.contMDiff_tangentMap (by simp)).comp
        (d9IntrinsicThroatFrame
          period hPeriod direction).contMDiff_toFun)
  unfold d9PrimitiveMonopoleCoordinateFrameDerivative
  convert hDerivative using 1
  · rfl
  · funext base
    rfl

/-- The Cartesian monopole connection coefficient is smooth on its
appropriate north or south chart domain. -/
theorem d9PrimitiveMonopoleConnectionFrameCoefficient_contMDiffOn
    (charge : Int) (chart : MonopoleChart) (direction : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (d9PrimitiveMonopoleConnectionFrameCoefficient
        period hPeriod charge chart direction)
      (d9PrimitiveMonopoleChartDomain
        period hPeriod chart) := by
  have hX :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod 0
  have hY :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod 1
  have hZ :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod 2
  have hDX :=
    d9PrimitiveMonopoleCoordinateFrameDerivative_contMDiff
      period hPeriod 0 direction
  have hDY :=
    d9PrimitiveMonopoleCoordinateFrameDerivative_contMDiff
      period hPeriod 1 direction
  have hNumerator :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
        (fun base =>
          primitiveMonopoleAngularNumerator
            (d9ThroatMonopoleSphereProjection period hPeriod base)
            (d9PrimitiveMonopoleCoordinateFrameDerivative
              period hPeriod 0 direction base)
            (d9PrimitiveMonopoleCoordinateFrameDerivative
              period hPeriod 1 direction base)) := by
    unfold primitiveMonopoleAngularNumerator
    exact hX.mul hDY |>.sub (hY.mul hDX)
  cases chart with
  | north =>
      unfold d9PrimitiveMonopoleConnectionFrameCoefficient
        primitiveMonopoleCartesianPotential
      apply
        ((contMDiff_const.mul hNumerator).contMDiffOn).div₀
          ((contMDiff_const.add hZ).contMDiffOn)
      intro base hBase
      change
        1 + d9PrimitiveMonopoleBaseCoordinate
          period hPeriod 2 base ≠ 0
      change
        d9PrimitiveMonopoleBaseCoordinate
          period hPeriod 2 base ≠ -1 at hBase
      intro hZero
      apply hBase
      linarith
  | south =>
      unfold d9PrimitiveMonopoleConnectionFrameCoefficient
        primitiveMonopoleCartesianPotential
      apply
        ((contMDiff_const.mul hNumerator).contMDiffOn).div₀
          ((contMDiff_const.sub hZ).contMDiffOn)
      intro base hBase
      change
        1 - d9PrimitiveMonopoleBaseCoordinate
          period hPeriod 2 base ≠ 0
      change
        d9PrimitiveMonopoleBaseCoordinate
          period hPeriod 2 base ≠ 1 at hBase
      intro hZero
      apply hBase
      linarith

/-- The flat normal spin-frame coefficient is globally smooth. -/
theorem d9PrimitiveSpinCNormalFrameConnectionCoefficient_contMDiff
    (direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (d9PrimitiveSpinCNormalFrameConnectionCoefficient
        period hPeriod direction) := by
  unfold d9PrimitiveSpinCNormalFrameConnectionCoefficient
    d9PrimitiveSpinCBaseUnitRadialCoordinate
  exact
    contMDiff_const.mul
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod direction)

/-- The total monopole/normal connection is smooth on each chart. -/
theorem d9PrimitiveSpinCTotalConnectionFrameCoefficient_contMDiffOn
    (chart : MonopoleChart) (direction : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (d9PrimitiveSpinCTotalConnectionFrameCoefficient
        period hPeriod chart direction)
      (d9PrimitiveMonopoleChartDomain period hPeriod chart) := by
  unfold d9PrimitiveSpinCTotalConnectionFrameCoefficient
  exact
    (d9PrimitiveMonopoleConnectionFrameCoefficient_contMDiffOn
      period hPeriod 1 chart direction).add
      (d9PrimitiveSpinCNormalFrameConnectionCoefficient_contMDiff
        period hPeriod direction).contMDiffOn

/-- The local radial Levi--Civita correction is smooth on every joint chart. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_contMDiffOn
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (fun base =>
        d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base
          (family.localValue index base))
      (d9PrimitiveSpinCBaseSet period hPeriod index) := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  apply contMDiffOn_finsetSum
  intro other _
  by_cases hSame : other = direction
  · simp only [hSame, ↓reduceIte]
    exact contMDiffOn_const
  · simp only [hSame, ↓reduceIte]
    exact
      ((contMDiff_const.mul
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod other)).contMDiffOn).smul
        ((d9DoubledMatterFiberCliffordGammaCLM
            direction).contDiff.contMDiff.comp_contMDiffOn
          ((d9DoubledMatterFiberCliffordGammaCLM
              other).contDiff.contMDiff.comp_contMDiffOn
            (family.contMDiffOn_localValue index)))

/-- The local Levi--Civita frame derivative is smooth on every joint chart. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (fun base =>
        d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family index direction base)
      (d9PrimitiveSpinCBaseSet period hPeriod index) := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  exact
    (d9PrimitiveSpinCLocalFlatFrameDerivative_contMDiffOn
      period hPeriod choice family index direction).add
      (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_contMDiffOn
        period hPeriod choice family index direction)

/-- The complete local geometric Dirac output is smooth on every joint
normal-root/monopole chart. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_contMDiffOn
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family index)
      (d9PrimitiveSpinCBaseSet period hPeriod index) := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
    d9PrimitiveSpinCLocalDirectionalDerivative
  apply contMDiffOn_finsetSum
  intro direction _
  have hLevi :=
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_contMDiffOn
      period hPeriod choice family index direction
  have hConnection :
      ContMDiffOn throatCoverModelWithCorners 𝓘(Real, Real) ∞
        (d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod index.2 direction)
        (d9PrimitiveSpinCBaseSet period hPeriod index) :=
    (d9PrimitiveSpinCTotalConnectionFrameCoefficient_contMDiffOn
      period hPeriod index.2 direction).mono (by
        intro base hBase
        exact hBase.2)
  have hImaginary :
      ContMDiffOn throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        (fun base =>
          d9PrimitiveSpinCImaginaryAction
            (family.localValue index base))
        (d9PrimitiveSpinCBaseSet period hPeriod index) :=
    d9PrimitiveSpinCImaginaryAction.contDiff.contMDiff
      |>.comp_contMDiffOn (family.contMDiffOn_localValue index)
  exact
    (d9DoubledMatterFiberCliffordGammaCLM
      direction).contDiff.contMDiff.comp_contMDiffOn
        (hLevi.add (hConnection.smul hImaginary))

/-- Local Dirac outputs form a new smooth cocycle-compatible gauge family. -/
def d9PrimitiveSpinCGeometricDiracLocalGaugeFamily
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index :=
    d9PrimitiveSpinCLocalGeometricDirac
      period hPeriod choice family index
  contMDiffOn_localValue index :=
    d9PrimitiveSpinCLocalGeometricDirac_contMDiffOn
      period hPeriod choice family index
  coordChange_localValue first second base hBase :=
    d9PrimitiveSpinCLocalGeometricDirac_coordChange_exact
      period hPeriod choice family first second base hBase

/-- Genuine globally descended smooth geometric SpinC Dirac output. -/
def d9PrimitiveSpinCGeometricDiracSection
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  (d9PrimitiveSpinCGeometricDiracLocalGaugeFamily
    period hPeriod choice family).toSmoothSection
      period hPeriod choice

@[simp]
theorem d9PrimitiveSpinCGeometricDiracSection_apply
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGeometricDiracSection
        period hPeriod choice family base =
      d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family
        ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod choice).indexAt base) base :=
  rfl

/-- Local coordinate of an arbitrary genuine smooth primitive SpinC
section. -/
def d9PrimitiveSpinCSmoothSectionLocalValue
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  ((d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
    |>.localTriv index ⟨base, state base⟩).2

theorem d9PrimitiveSpinCSmoothSectionLocalValue_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9PrimitiveSpinCSmoothSectionLocalValue
        period hPeriod choice state index)
      (d9PrimitiveSpinCBaseSet period hPeriod index) := by
  let core :=
    d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  let localTriv := core.localTriv index
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨index, ?_⟩⟩
    rfl
  have hMaps :
      MapsTo
        (fun base : ThroatBase period hPeriod =>
          ⟨base, state base⟩)
        (d9PrimitiveSpinCBaseSet period hPeriod index)
        localTriv.source := by
    intro base hBase
    rw [localTriv.mem_source]
    exact hBase
  exact
    (localTriv.contMDiffOn_iff hMaps).mp
      state.contMDiff_toFun.contMDiffOn |>.2

theorem d9PrimitiveSpinCSmoothSectionLocalValue_coordChange
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) :
    d9PrimitiveSpinCCoordChange period hPeriod choice
        first second base
        (d9PrimitiveSpinCSmoothSectionLocalValue
          period hPeriod choice state first base) =
      d9PrimitiveSpinCSmoothSectionLocalValue
        period hPeriod choice state second base := by
  let core :=
    d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  change
    core.coordChange first second base
        (core.coordChange (core.indexAt base) first base
          (state base)) =
      core.coordChange (core.indexAt base) second base
        (state base)
  exact core.coordChange_comp
    (core.indexAt base) first second base
      ⟨⟨core.mem_baseSet_at base, hBase.1⟩, hBase.2⟩ _

/-- Every genuine smooth section supplies its complete family of smooth
local gauge representatives. -/
def d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue :=
    d9PrimitiveSpinCSmoothSectionLocalValue
      period hPeriod choice state
  contMDiffOn_localValue :=
    d9PrimitiveSpinCSmoothSectionLocalValue_contMDiffOn
      period hPeriod choice state
  coordChange_localValue :=
    d9PrimitiveSpinCSmoothSectionLocalValue_coordChange
      period hPeriod choice state

/-- Recovering local gauges and descending again is exactly the original
smooth section. -/
theorem d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
        period hPeriod choice state).toSmoothSection
          period hPeriod choice =
      state := by
  ext base
  let core :=
    d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  change
    core.coordChange (core.indexAt base) (core.indexAt base) base
        (state base) =
      state base
  exact core.coordChange_self
    (core.indexAt base) base (core.mem_baseSet_at base) (state base)

/-- The globally defined first-order geometric SpinC Dirac operator on the
entire genuine smooth section core. -/
def d9PrimitiveSpinCGeometricDiracOperator
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  d9PrimitiveSpinCGeometricDiracSection
    period hPeriod choice
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state)

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
end JanusFormal
