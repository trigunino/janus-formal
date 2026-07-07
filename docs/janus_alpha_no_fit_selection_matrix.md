# Janus Alpha No-Fit Selection Matrix

Purpose: keep every plausible no-fit route for selecting `alpha` visible, without
polluting the active Janus/Z2 core.

Current baseline:

- `alpha = -2*pi*G*E_global/c^2`;
- `alpha` is currently a continuous global state-sector label;
- no active route derives a unique no-fit value.

## Decision Matrix

| ID | Route | Physical meaning | What could fix `alpha` | Current status | Hard blocker | No-fit if closed? |
|---:|---|---|---|---|---|---|
| 1 | Global action / energy principle | The universe is the stationary state of the full Janus solution | `dS_on(alpha)/dalpha = 0`, minimum of `E_global`, or extremal quasilocal charge | Open | Need finite on-shell bimetric action for noncompact exact orbit | Yes |
| 2 | PT/Souriau quantization | `alpha` is a quantized coadjoint-orbit charge | integral KKS period, compact PT cycle, mass unit | Blocked | No nonzero PT KKS density or compact cycle | Yes |
| 3 | Horizon / null thermodynamics | Big Bang/PT bridge is a causal boundary/horizon | regular Euclidean period, entropy extremum, first-law balance | Open | Need null/PT boundary action and temperature/entropy law | Yes |
| 4 | LL-brane bridge state | bridge mass comes from lightlike brane tension | derived `chi_LL`, then `M_bridge(alpha)` | Conditional | LL theory gives `M(chi_LL)` but not `chi_LL` selection | Yes if `chi_LL` selected |
| 5 | Spinor / torsion / Nieh-Yan | primordial fermion/spin sector sources torsion | spin current, condensate, Nieh-Yan charge, torsionful BC | Archived for active PT67 | no active torsion source on Sigma | Yes if source derived |
| 6 | Topological flux / area gap | throat carries a primitive quantum of flux/area | `A_Sigma = N_gap * A0`, with `N_gap=1` derived | Blocked | flux unit and primitive sector not derived | Yes |
| 7 | Bimetric vacuum equation of state | global +/- matter vacuum fixes density normalization | state law for `rho_+0`, `rho_-0`, or `E_global` | Open | published ratio is relative, not absolute | Yes |
| 8 | Boundary reference / Brown-York normalization | `alpha` is a quasilocal boundary charge relative to a reference | nonzero `Q_boundary - Q_reference` with Janus reference | Mostly exhausted | active PT67 regular projection gives zero | Only if nonzero reference law derived |
| 9 | Observational sector selection | `alpha` is like ADM mass: measured, not predicted | SN+BAO+H(z) selects sector | Viable but not no-fit | observational calibration required | No |
| 10 | Alternative tunnel geometry | current Sigma too poor; another global tunnel carries a cycle | compact action-angle cycle or monodromy | Open | must derive from Janus, not replace it ad hoc | Maybe |
| 11 | Moebius / twisted throat geometry | orientation reversal is geometrized as a twisted compact cycle | Pin/PT holonomy or compact cycle around a Moebius-like throat | New candidate | must lift from 2D analogy to 4D resolved tunnel with action | Maybe |
| 12 | Quantum state / superselection law | allowed universes are discrete sectors | primitive sector law, irreducibility, no fusion/splitting | Blocked | no internal proof of primitive sector | Yes |

## Moebius Candidate

The Moebius idea is not automatically a solution, but it is relevant.

What it can provide:

- a concrete orientation-reversing loop;
- a natural `Z2` transport intuition;
- a possible Pin/PT holonomy;
- a compact cycle candidate for Souriau/KKS or action-angle quantization.

What it does not provide by itself:

- a dimensionful value of `alpha`;
- a 4D cosmological throat;
- a nonzero KKS density;
- a finite on-shell action.

Correct test:

1. Define a 2D shadow: Moebius/twisted band or torus-to-Klein-like quotient.
2. Lift to the 4D resolved Janus tunnel.
3. Identify a compact cycle `C_PT`.
4. Pull back the symplectic potential or boundary theta to `C_PT`.
5. Test whether `Integral_C_PT theta` is nonzero and alpha-dependent.
6. If yes, test quantization. If no, archive as topology-only intuition.

Current route verdict:

- the torus/Klein resolved shadow and `aroundSigma` Z2 cycle are already present;
- this supports the topology intuition of a twisted orientation cycle;
- the active PT67 boundary theta has zero period;
- no compact alpha-dependent action-angle cycle is derived;
- therefore the Moebius route is not currently an `alpha` selector.

## Evaluation Order

1. Recheck global action/on-shell route.
2. Recheck null/PT thermodynamic route.
3. Test Moebius/twisted-cycle route as a topology-to-cycle candidate.
4. Recheck Souriau/KKS only if a nonzero cycle/density is found.
5. Recheck spinor/torsion only if a real Sigma source is derived.
6. Leave observational selection as fallback, not no-fit.

## Rules

- No new fit constant may be renamed as a theorem.
- No local Sigma source may be introduced unless it follows from action,
  boundary condition, or field content.
- Geometry analogies are diagnostic until lifted to the 4D Janus tunnel.
- A route closes only if it emits a concrete selector for `alpha` or proves a
  route-specific no-go.

## Global Action Route

Current route verdict:

- the published action/equation material anchors the Janus exact family;
- `alpha = -2*pi*G*E_global/c^2` is available;
- no finite on-shell `S_on(alpha)` or `V(alpha)` has been derived;
- no boundary prescription for the noncompact exact orbit is available;
- therefore the global action route is not currently an `alpha` selector.

## Null/PT Thermodynamic Route

Current route verdict:

- null-boundary and apparent-horizon thermodynamics are legitimate mathematical
  frameworks for deriving an energy/entropy balance;
- the Janus Null/PT bridge context exists as a separate branch;
- the active assets do not yet prove the bridge is the required horizon with
  surface gravity, entropy, temperature, first-law energy, and selected
  `chi_LL`;
- therefore the null/PT thermodynamic route is not currently an `alpha`
  selector.

## Bimetric Vacuum Route

Current route verdict:

- the published bimetric sector ratio is available as a relative statement;
- this does not fix the absolute density scale;
- `rho_plus0_abs` still needs `N_occ_Z2Sigma` and `R_curv_Z2Sigma`, or an
  equivalent global bimetric state law;
- therefore the bimetric vacuum route is not currently an `alpha` selector.

## Observational Sector Selection

Current route verdict:

- observations can select or constrain the `alpha` sector;
- SN Ia alone mostly constrain relative distance shape and remain calibration
- the active observable background parameter is `q0/u0`, because the exact
  dimensional `alpha` cancels from dimensionless distance/expansion ratios;
- `p0_eft_janus_z2_alpha_observational_fit_gate` runs a fine-grid
  Pantheon+ diagonal + DESI DR2 BAO fit with SN offset and BAO scale profiled;
- current status is observational sector selection, not a no-fit prediction.
  degenerate;
- SN+BAO is the minimal serious background selection program;
- this is scientifically useful, but it is not a no-fit derivation of `alpha`.

## S4_L / RP4_L Scale Geometry Route

Current route verdict:

- the faithful geometric branch is now stated as `S4_L -> RP4_L` resolved by a
  tubular throat `Sigma`;
- the topology provides the projective `Z2` cover and the tunnel cycle;
- the new object is the dimensionful global radius `L`;
- current regularity, boundary-charge, area/flux and holonomy/spectral routes
  do not fix `L`;
- therefore `L`, and hence dimensional `alpha`, remains a continuous global
  state-sector scale unless a new selector is derived.

## E_throat Quantum/Topology Frontier

Current route verdict:

- setting `E_throat = E_global` is structurally coherent and localizes the
  scale in the throat state;
- five possible selectors were separated: charge quantization, topological
  vacuum energy, strong regularity, LL-brane tension, and boundary action;
- none is currently derived from the active Janus/Z2 assets;
- a quantum/topological throat theory can be proposed, but it would currently
  be a new physical layer unless its symplectic/flux/vacuum/tension/boundary
  normalization is derived from Janus.

## Candidate Quantum/Topology Throat Theory

Candidate proposed:

- `Sigma` carries a quantum boundary phase space;
- `A_Sigma = N * A_gap`;
- `L = sqrt(A_Sigma/(4*pi))`;
- `alpha_time = L/c`;
- `E_throat = E_global = -L*c/(2*pi*G)` in mass units.

Verdict:

- this creates a coherent discrete family of Janus universes;
- the primitive sector `N=1` is Planck-scale, not cosmological;
- topology/integrality alone does not select the huge macroscopic `N`;
- therefore the candidate is a new quantum/topology layer, not yet a no-fit
  Janus derivation.

## Holographic N Candidate

Required order:

- published Janus-like `q0=-0.087`, `H0=70` gives `N ~ 2.5e120` for
  `A_Sigma=N*A_gap` with `gamma=1`.

Verdict:

- horizon entropy, de Sitter area and condensate occupation naturally reproduce
  the `10^120` order once `H0` or `L` is known;
- this explains the magnitude, but is circular as a prediction of `H0/L`;
- primitive topology is non-circular but gives `N=O(1)`, hence Planck scale;
- the missing law is a Janus-specific state/entropy selector for macroscopic
  `N`.

## Non-Circular N Frontier

Filter:

- any rule using `H0`, `L`, `R_H`, `A_H`, `alpha`, or observed `Lambda` is
  circular for predicting the Janus scale.

Current verdict:

- no active non-circular rule selects `N~10^120`;
- topology-only data are non-circular but `O(1)`;
- the two remaining serious frontiers are:
  - derive a boundary Hilbert-space/microcanonical state law on `Sigma`;
  - derive a Janus-specific TQFT/level on `Sigma`.

## Remaining Non-Circular N Frontiers

Current route verdict:

- `P0EFTJanusZ2EThroatRemainingNonCircularFrontiersGate` exhausts the two
  remaining non-circular frontiers identified above;
- the boundary Hilbert-space route is coherent but not derived: it still needs
  a Janus/Sigma boundary phase space, Hilbert space, entropy formula and state
  law that select macroscopic `N` without `H0`, `L`, `alpha`, or observations;
- the TQFT route is coherent but not derived: it still needs a boundary theory
  from the Janus action, a level `k` not fixed by area/Hubble data, and a
  primitive sector law;
- isolated-horizon/LQG bibliography supports Hilbert-space and Chern-Simons
  counting once area/level/punctures are supplied, but does not derive the
  Janus macroscopic scale;
- therefore `N` remains a discrete sector label, not a no-fit prediction.

## Bibliography Anchors

- KKS / orbit-method quantization: prequantization requires integral symplectic
  periods on the relevant orbit/cycle.
- Moebius band: provides orientation reversal and a nontrivial loop, but has a
  boundary and is only a 2D diagnostic unless lifted.
- Klein bottle / torus cover: useful resolved-tunnel shadow because a torus can
  double-cover a Klein-like quotient.
- Published Janus bimetric model: supplies the bimetric sector and exact-family
  context, but current assets still leave `alpha` as a continuous state label.
