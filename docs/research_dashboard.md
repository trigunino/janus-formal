# Janus Research Dashboard

This dashboard is the operational companion to `PROGRAM.md`. It is written for
readers who do not know the discussion history.

## Evidence legend

| Code | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **C** | conditional theorem from explicit named inputs |
| **G** | geometric construction target |
| **P** | physical or quantum derivation target |
| **N** | no-go or obstruction |
| **O** | observational test |

## Program portfolio

| ID | Program | Scientific role | Current state | Terminal blocker |
| --- | --- | --- | --- | --- |
| **D** | Fundamental geometry | derive throat, Pin/Z4, gauge and spectrum from one PT-twisted geometry | active priority; local heat-kernel layer now explicit | actual global operator, scheme-independent effective action, absolute scale |
| **A** | Quantum world-volume | generate the dimensionful LL charge and stable vacuum | conditional algebra advanced | exact stable QFT and UV boundary law |
| **B** | Nonlinear bimetric junction | derive common action, constraints, PT charge and bridge | conditional classical chain advanced | full nonlinear constraints and null Hamiltonian charge |
| **C** | Charge compatibility | identify bulk, throat, LL and bridge normalizations | integer/unit transport partial | geometric transgression and equal large-gauge periods |
| **E** | Observation | falsify a closed theory with SN/BAO/CMB/lensing/structure | diagnostics only | native early-time sector and absolute prediction |

## Program-D work packages

| ID | Work package | Evidence | Result / blocker | Main Lean module |
| --- | --- | --- | --- | --- |
| **D1.1** | twisted mapping generator | **T** | square is pure translation by `2T` | `P0EFTJanusTwistedMappingGenerator.lean` |
| **D1.2** | fixed throat | **T/G** | reflection fixed set is equatorial `S2`; mapping-torus throat target is `S2 x S1` | `P0EFTJanusReflectionFixedThroat.lean` |
| **D1.3** | cellular invariants | **T/G** | top boundary `2`, parity torsion, no degree-two cell in minimal model | `P0EFTJanusTwistedHopfCellularModel.lean` |
| **D2.1** | Pin obstruction | **T/G** | separates `RP4` Pin+ pattern from twisted-Hopf target pattern | `P0EFTJanusPinObstructionAudit.lean` |
| **D2.2** | fermionic Z4 | **T/G** | geometric Z2 may lift to `g^2=(-1)^F`, `g^4=1` | `P0EFTJanusTwistedHopfMonodromy.lean` |
| **D3.1** | global Hopf U1 descent | **N** | ordinary primitive Hopf bundle cannot descend through orientation reversal | `P0EFTJanusHopfBundleOrientationNoGo.lean` |
| **D3.2** | throat monopole | **T/G** | primitive Chern sector and local Dirac patching | `P0EFTJanusThroatMonopoleEmergence.lean`, `P0EFTJanusDiracMonopolePatching.lean` |
| **D3.3** | pointwise-fixed PT monopole | **N** | charge conjugation gives `n=-n`, hence zero descended flux | `P0EFTJanusFixedThroatFluxDescentNoGo.lean` |
| **D4.1** | scalar spectral modulus | **C** | equal first scalar modes give `T^2=2*pi^2`; not yet a vacuum law | `P0EFTJanusSpectralIsotropyAlphaRatio.lean` |
| **D4.2** | spectral weights | **T/N** | weights are determinant/field-content data, not topology | `P0EFTJanusWeightedSpectralLock.lean` |
| **D4.3** | primitive monopole Z4 spectrum | **T/C** | explicit integer spectrum and unique normalized gap | `P0EFTJanusPrimitiveMonopoleZ4Spectrum.lean` |
| **D4.4** | eta and quarter holonomy | **T/C/P** | eta-model cancellation and gap relation; analytic continuation open | `P0EFTJanusZ4HolonomyEtaGap.lean` |
| **D4.5** | Dirac/LL/bimetric lock | **C** | derives `q_LL=lambda_S2/8` and `A=L` from explicit inputs | `P0EFTJanusZ4DiracAlphaLock.lean` |
| **D5.1** | product local invariants | **T/C** | exact `Vol`, `int R`, curvature-square and monopole-square scalings | `P0EFTJanusProductThroatLocalInvariants.lean` |
| **D5.2** | Seeley-DeWitt candidate | **C** | reduced rank-two Dirac `a0,a2,a4` explicit; operator convention still to verify | `P0EFTJanusDiracSeeleyDeWittCandidate.lean` |
| **D5.3** | local spectral action | **T/N** | increasing, decreasing or flat in `T`; no isolated local minimum | `P0EFTJanusTruncatedSpectralActionNoGo.lean` |
| **D5.4** | winding/holonomy heat kernel | **T/C** | local term holonomy blind; quarter sector starts at winding two | `P0EFTJanusCircleHeatKernelWinding.lean` |
| **D5.5** | PT spectral action | **T/N** | eta part cancels, even heat-kernel/determinant part doubles | `P0EFTJanusPairedSpectralActionDecomposition.lean` |
| **D5.6** | finite counterterm | **T/N** | can place a stable minimum at any target; nonzero scheme shift moves it | `P0EFTJanusHeatKernelCountertermScheme.lean`, `P0EFTJanusRenormalizationSchemeNoGo.lean` |
| **D5.7** | scheme-independent effective action | **P** | finite local parts must be fixed microscopically | next analytic program |
| **D6** | absolute scale | **P** | normalized geometry leaves a common scale orbit | quantum or gravitational scale generation |

## Proposal matrix

| Proposal ID | Proposal | Verdict | Reason |
| --- | --- | --- | --- |
| **P-D-HOPF-U1** | global ordinary Hopf connection is the LL gauge field | **rejected in naive form** | primitive bundle compatibility preserves total orientation |
| **P-D-THROAT-U1** | intrinsic monopole connection on throat `S2` | **retained** | correct integral class and local patching exist |
| **P-D-FIXED-PT-MONOPOLE** | one PT-conjugate nonzero line bundle descends over pointwise-fixed `S2` | **rejected** | descent forces `n=0` |
| **P-D-COVER-PAIR** | PT-related folds carry paired `+1/-1` monopoles | **retained** | eta-odd pieces cancel while even spectral gaps add |
| **P-D-SCALAR-ISOTROPY** | equal first scalar modes select `T^2=2*pi^2` | **conditional only** | effective action and weights must derive it |
| **P-D-Z4-HOLONOMY** | global Pin lift imposes quarter circle holonomy | **strong candidate** | order-four algebra is exact; global geometric lift is open |
| **P-D-DIRAC-LOCK** | paired quarter-holonomy Dirac gaps generate `q_LL` | **strongest compatibility candidate** | reproduces `1/8` and `A=L` |
| **P-D-LOCAL-HEAT-MINIMUM** | local Seeley-DeWitt terms stabilize `T` | **rejected** | all local product-throat terms are affine in `T` |
| **P-D-COUNTERTERM-MINIMUM** | finite local term plus quarter determinant predicts `T` | **rejected unless coefficient derived** | any target can be fitted by the finite coefficient |
| **P-D-SPECTRUM-ABSOLUTE** | normalized spectrum alone fixes `L` | **rejected** | common metric rescaling remains |
| **P-A-RG-SCALE** | world-volume dimensional transmutation fixes absolute `L` | **retained** | can break scale covariance if microscopic UV data are derived |

## Current strongest conditional chain

```text
primitive monopole |n|=1
+ quarter Pin/Z4 holonomy
+ T^2=2*pi^2
  -> unique squared Dirac gap: gap^2 L^2 = 1/8

PT pair:
  eta_+ + eta_- = 0
  gap_+^2 + gap_-^2 = 2 gap^2
  -> q_LL L^2 = 1/4
  -> q_LL = lambda_S2 / 8

primitive LL flux:
  16 q_LL^2 A^4 = 1
  -> A = L
```

This remains a compatibility theorem, not an absolute-scale prediction.

## Heat-kernel conclusion

```text
local UV coefficients:
  necessary for renormalization
  linear in T
  cannot select T

nonlocal windings:
  carry holonomy information
  quarter holonomy starts at winding two

PT pairing:
  cancels eta
  doubles the even effective action

finite local coefficient + nonlocal term:
  can create a stable minimum
  but can fit any chosen target
```

The next decisive condition is therefore **scheme-independent microscopic
matching**, not another arbitrary spectral equality.

## Next theorem queue

| Priority | Target | Success criterion | Failure meaning |
| ---: | --- | --- | --- |
| **1** | actual global SpinC/Pin Dirac square | verify Lichnerowicz and gauge conventions | candidate `a0,a2,a4` must be revised |
| **2** | analytic product heat trace | prove Poisson/winding decomposition with multiplicities | winding model remains diagnostic |
| **3** | Hurwitz-zeta / APS eta calculation | derive eta `+/-1/2` and determinant phase | parity cancellation law must be revised |
| **4** | classify allowed finite counterterms | show symmetry or matching fixes their finite parts | every modulus remains scheme-adjustable |
| **5** | determinant-derived charge law | derive `q_LL=gap_+^2+gap_-^2` | the `1/8` lock remains an ansatz |
| **6** | complete renormalized effective action | unique stable `T`, independent of target data | Program D cannot select its modulus |
| **7** | absolute scale law | generate `L` without observation | only dimensionless compatibility survives |

## Branches and builds

```text
research/fundamental-geometry-d
lake build JanusFormal.Branches.FundamentalGeometryD
python scripts/audit_janus_fundamental_geometry_d.py
python scripts/audit_janus_holonomy_determinant.py
python scripts/audit_janus_heat_kernel_effective_action.py
python -m pytest -q tests/test_janus_fundamental_geometry_d.py
python -m pytest -q tests/test_janus_holonomy_determinant.py
python -m pytest -q tests/test_janus_heat_kernel_effective_action.py
```

## Update rule

Every new proposal must state its program ID, evidence level, dependencies,
result or no-go, remaining physical atom, falsification criterion and build
target. No percentage-complete claim is used as a substitute for these fields.
