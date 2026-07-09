# Janus Early-Universe Native Plasma

This branch is the first explicit extension beyond the paper-native late-time
SN/background layer.

It uses `X2026-variable-constants` Eq. 40 as the early-universe gauge input and
connects it to the active Z2/Sigma BAO/plasma machinery.

## What Eq40 closes

With:

```text
c ~ a^-1/2
h ~ a^3/2
e ~ a^1/2
m ~ a
G ~ a^-1
mu0 ~ a
length ~ a
time ~ a^3/2
```

the branch derives:

- fine-structure constant invariant;
- rest energy `m c^2` invariant;
- hydrogen ionization scale invariant;
- Compton length scales as `a`;
- Thomson cross-section scales as `a^2`.

## What remains open

This still does not derive:

- active baryon number or `rho_b0^J`;
- active photon temperature/occupation law;
- active ionization history;
- pre-drag two-sector `H_J(a)`;
- redshift map valid from today to `z_d^J`.

## New physical fork

The Eq40-native comoving photon law gives:

```text
rho_gamma ~ a^-3
rho_b,energy ~ a^-3
blackbody n_gamma ~ a^-3
Gamma_drag/H ~ constant before ionization physics
```

So Eq40 alone does not naturally select a drag epoch.

A thermodynamic cooling law gives:

```text
rho_gamma ~ a^-4
rho_b,energy ~ a^-3
blackbody n_gamma ~ a^-6
Gamma_drag/H evolves
```

That can support an evolving drag ratio, but it conflicts with conserved photon
number unless Janus also derives a photon entropy/phase-space production law.

The minimal compensating law is:

```text
phase-space occupation / entropy factor ~ a^3
```

With that extra derived law, one can have both:

- `T_energy ~ a^-1`;
- conserved blackbody photon number `n_gamma ~ a^-3`.

This is the current best concrete target for the next derivation.

## Occupation search

The phase-space occupation search tests several mechanisms against the required
`a^3` factor.

Rejected or insufficient:

- constant `Z2` sheet multiplicity;
- fixed `RP3/Sigma` topology;
- pure Sigma area modes;
- naive `h^3` quantum-cell deformation;
- Compton-cutoff mode count.

Still viable/open:

- 3D Sigma/collar volume modes;
- causal horizon volume modes;
- adiabatic radiation first law;
- negative-sector entropy projection.

Best current target:

```text
adiabatic radiation first law in the Janus/Z2 variable-constants frame
```

Report:

```text
outputs/reports/p0_eft_janus_phase_space_occupation_search_gate.md
```

## Conditional first-law closure

If the visible photon stress tensor is separately conserved in the plus-sector
FLRW frame and remains trace-free, then:

```text
d(rho_gamma V) + p_gamma dV = 0
p_gamma = rho_gamma/3
V ~ a^3
=> rho_gamma ~ a^-4
```

With Eq40 blackbody counting:

```text
h c ~ a
T_energy ~ a^-1
bare n_gamma ~ (T/(h c))^3 ~ a^-6
```

To keep comoving photon number/entropy conserved:

```text
occupation factor ~ a^3
```

This closes the required exponent conditionally. It is not unconditional until
the plus-sector radiation first law is derived from the Janus bimetric
projection.

## Photon stress conservation

The repo already has two useful anchors:

- M15/M30: positive-energy photons follow the plus-sector metric/geodesic family;
- a same-sector Noether stress-conservation scaffold in the Z2/Sigma branch.

Therefore the clean route is:

```text
S_gamma_plus[g_plus, A_plus]
+ minimal coupling to g_plus
+ photon equations of motion
+ no cross-sector photon exchange
=> nabla_plus T_gamma_plus = 0
```

The branch now adds that object as a minimal standard extension:

```text
S_gamma_plus = -1/4 int sqrt|g_plus| F_plus_mn F_plus^mn
```

This is compatible with the paper photon-geodesic anchors, but it is not an
explicit paper-native formula. Within this extension contract, Noether closes
`nabla_plus T_gamma_plus = 0` on shell and the radiation first-law input is no
longer blocked. The remaining hard objects are the variable-constants thermal
frame, active baryon density, ionization/drag history, and pre-drag `H_J(a)`.

## Thermal frame map

The thermal exponent is now solved rather than assumed. In Eq40:

```text
(h c)^3 ~ a^3
n_gamma ~ occupation * T_energy^3 / (h c)^3
rho_gamma ~ occupation * T_energy^4 / (h c)^3
```

Imposing both:

```text
n_gamma ~ a^-3
rho_gamma ~ a^-4
```

uniquely gives:

```text
T_energy ~ a^-1
occupation ~ a^3
```

The remaining hard step is to derive `occupation~a^3` as a real
entropy/phase-space degeneracy, not a bookkeeping factor.

## Drag exponent frontier

With conserved baryon/electron number and Eq40:

```text
n_e ~ a^-3
sigma_T ~ a^2
c ~ a^-1/2
Gamma_drag = n_e sigma_T c ~ a^-3/2
```

If:

```text
H_J ~ a^p
```

then:

```text
Gamma_drag / H_J ~ a^(-3/2 - p)
```

To have stronger coupling in the far past without relying on ionization
suppression, the native pre-drag branch needs:

```text
p > -3/2
```

Thus radiation-like `H_J ~ a^-2` or steeper is not enough in the Eq40 frame.
The next physical input must be either a Janus-native pre-drag `H_J(a)` branch
with shallower scaling, or an active ionization/visibility law. Fitting `alpha`
cannot repair this exponent-level issue.

Pushing the Eq40 Friedmann exponents gives:

```text
radiation fluid        -> H_J ~ a^-2      -> fails native early coupling
matter / baryons       -> H_J ~ a^-3/2    -> Gamma/H constant
curvature-like term    -> H_J ~ a^-3/2    -> Gamma/H constant
bridge/vacuum state    -> H_J shallower   -> can restore early coupling
```

So a native BAO branch cannot be obtained from ordinary radiation alone in this
frame. It needs either:

- a derived bridge/vacuum state component in the pre-drag background; or
- an active ionization/visibility law that supplies the crossing.

## Eq40 Saha visibility

The ionization route is not empty. With Eq40 and the solved thermal frame:

```text
m_e ~ a
T_energy ~ a^-1
h ~ a^3/2
n_b ~ a^-3
E_ion ~ a^0
```

The Saha scaling becomes:

```text
x_e^2/(1-x_e)
  ~ (m_e T / h^2)^(3/2) n_b^-1 exp(-E_ion/T)
  ~ a^-3/2 exp(-const * a)
```

So recombination/visibility is at least structurally native in the Eq40 frame:
small `a` is ionized, larger `a` recombines. The remaining blocker is absolute,
not structural: the model still needs the dimensionless anchor `E_ion/T0` or an
equivalent baryon/photon normalization before a numerical `z_d^J` can be
computed.

## Drag equation contract

The native symbolic crossing equation is now:

```text
A_drag * a^(-3/2 - p_H) * x_e(a; C_ion, eta_b) = 1
```

with:

```text
x_e^2/(1-x_e) = B_eta * a^-3/2 * exp(-C_ion * a)
```

This is structurally ready but not numerically predictive. Remaining anchors:

- `C_ion = E_ion/T0_Janus`;
- baryon/photon or baryon-density normalization;
- drag normalization `A_drag`;
- native full `H_J(a)`.

## Native sound horizon

The sound speed contract becomes:

```text
R_b(a) = R_b0 * a
c_s^J(a) = c0 a^-1/2 / sqrt(3(1 + R_b0 a))
r_d^J = int_{a_min}^{a_d} c_s^J(a)/(a^2 H_J(a)) da
```

If `H_J ~ a^p`, the small-`a` integrand scales as:

```text
a^(-5/2 - p)
```

A finite integral from `a=0` requires `p < -3/2`, but early drag coupling
without ionization wanted `p > -3/2`. This is a real tension. The Janus-native
way out is not a fit parameter: the branch must derive either a nonzero throat
lower bound `a_min>0`, or a transition in `H_J(a)` before the drag era.

The published exact shape does provide such a lower bound:

```text
a(u) = alpha cosh(u)^2
a_min = alpha
```

With present normalization and published `q0=-0.087`:

```text
a_min/a0 ~= 0.1482
z_max ~= 5.747
```

So the late-time SN branch regularizes the lower limit, but it does not reach a
pre-drag epoch. Native BAO therefore requires an attached early-time branch or a
modified early redshift map, not just reuse of the published SN background.

For a simple early map:

```text
1 + z = (a0/a)^s
```

the published throat requires:

```text
s ~= 3.62
```

to reach `z~1000`. Current candidates:

```text
s=1    M18 geometric redshift        -> fails
s=1.5  Eq40 clock/frequency unit     -> fails
s=3    Eq40 occupation/volume factor -> still fails
s=4    four-volume/action phase      -> reaches, but speculative
```

So the only viable redshift-map escape currently needs a real early photon/clock
transport derivation. It cannot be promoted as a guessed exponent.

Inverting the same calculation:

```text
s=1    requires q0 ~= -0.0005
s=1.5  requires q0 ~= -0.005
s=3    requires q0 ~= -0.055
s=4    requires q0 ~= -0.108
```

So low-power redshift maps push `q0` toward the same near-zero edge already
seen in BAO diagnostics. A four-power map is the only tested case close to the
published SN band, but it remains speculative until derived from photon/clock
transport.

The tempting decomposition:

```text
s = 1 geometric redshift + 3 occupation volume
```

is not valid as a redshift derivation. Occupation changes density/intensity, not
the frequency of an individual spectral line. A promotable high-power map must
come from photon four-momentum transport and atomic clock transport in the same
Eq40 frame. This is not yet derived.

A minimal photon/clock transport audit is actually negative for `s=4`:

```text
photon frequency transport        ~ a^-1
atomic transition frequency Eq40  ~ E_ion/h ~ a^-3/2
observed emitted-line frequency   ~ a^-1/2
inferred 1+z exponent             ~ +1/2
```

This depends on conventions, so it is diagnostic. But it shows that standard
null transport plus Eq40 atomic clocks do not generate the high-power redshift
needed for pre-drag BAO.

If high-power redshift is rejected, the only clean path is an attached early
branch. With geometric redshift to `z~1000`:

```text
required a_min/a0 <= 0.001
published late SN a_min/a0 ~= 0.148
```

The late branch is therefore too short by a factor of about 148. A native BAO
model would need an early Eq40/pre-drag branch plus a matching surface preserving
`a`, `H_J`, photon-clock transport, `c_s`, and `x_e`.

## Frontier verdict

The branch now has a sharp frontier:

- closed: Eq40 microphysics, Maxwell/radiation extension, first-law thermal
  frame, Saha visibility, symbolic drag equation, sound-speed/ruler contract;
- blocked: numeric `z_d^J`, `r_d^J`, baryon normalization, drag normalization,
  full pre-drag `H_J(a)`;
- surviving routes:
  - derive high-power photon/clock redshift transport;
  - derive an attached early-time branch with matching surface.

Do not import a Lambda-CDM ruler, multiply redshift by occupation, or use alpha
fitting to hide this boundary.

## Attached Early Branch Diagnostic

A minimal diagnostic early branch:

```text
a_E(y) = a_min,E cosh(y)^2
```

can be C0/C1 matched to the late SN branch at a chosen transition redshift by
choosing a new time-scale ratio. This shows that an attached early branch is not
geometrically impossible. It is not yet physics: the new time scale is a new
state/integration constant until derived from an action or boundary law.

The time-scale ratio itself can be reduced further. If:

```text
x = a_transition / a_min,E
```

then the early cosh branch has:

```text
h_shape,E = 2 sqrt(x - 1) / x^(3/2)
time_scale_ratio = (H_late/H0) / h_shape,E
                 ~ (H_late/H0) x / 2  for large x
```

So the ratio is fixed once `a_min,E` and the transition are chosen. The remaining
freedom is not the ratio; it is the physical selection of `a_min,E` and the
transition surface.

Candidate selectors for `a_min,E` were audited:

- setting it by `z~1000` is circular;
- Eq40 length scaling gives no absolute cutoff;
- Saha selects the drag surface, not the throat;
- Planck/quantum cutoff would be new quantum-gravity input;
- topological integer sector could work only if Janus derives `N`;
- the published late SN throat is too large.

So `a_min,E` is the remaining hard selector.

If one tries:

```text
a_min,E = 1/N
```

then geometric reach to `z~1000` needs:

```text
N >= 1001
```

The projective Janus cover gives `N=2`, so it cannot supply this. A large `N`
would have to come from a boundary Hilbert-sector dimension, flux quantization,
area quantization, or another derived state-count law, and it must enter photon
ruler dynamics rather than remain a label.

The cleanest quantum route is:

```text
CP1 spin-j orbit: N = 2j + 1
```

For `N=1001`, this requires:

```text
j = 500
KKS/CS level k = 1000
```

The repo already contains CP1/KKS scaffolding, but not the Janus/PT sector law
that selects `j=500` or `k=1000`. This is now the precise quantum-frontier
target.

The sector-selection frontier was then audited explicitly:

- projective cover selects `N=2`, not `N=1001`;
- CP1 can represent the needed sector through `j=500`, but does not select it;
- KKS/CS can represent the needed sector through `k=1000`, but does not select it;
- flux and spin-network/area routes still need a boundary gauge, area, or puncture law.

Current verdict:

```text
boundary Hilbert sector selector = blocked without boundary state law
```

So the branch has reached a hard quantum frontier: derive a Janus/PT boundary
state law, or keep `N` as an observational/global-state sector rather than a
no-fit prediction.

The boundary-state candidate matrix keeps all current non-rustine exits visible:

- `Sym^4(C^11)` symmetric boundary sector: `1001`;
- `CP1` spin superselection: `j=500`;
- KKS/Chern-Simons level selection: `k=1000`;
- flux/area puncture count: `N=1001`;
- exterior-power boundary fermion sector: `1001 = C(14,4)`;
- anomaly/modular consistency level;
- microcanonical boundary entropy peak.

None is accepted as derived. The new useful observation is only:

```text
1001 = 7 * 11 * 13 = C(14,4)
```

This makes a finite boundary Hilbert-sector law plausible enough to keep, but it
does not close the model unless Janus/PT derives the boundary modes, action, or
sector selection.

The strongest current numerical clue is now more structured than a bare
coincidence:

```text
M31: dim(Jan) = 11
M31: independent CPT generators = 3
11 + 3 = 14
M31: spacetime translation/stress-energy sector has dimension 4
C(14,4) = 1001
```

Interpretation candidate: a four-excitation exterior-power boundary sector over
the Janus torsor modes plus CPT generators. This is not accepted as a derivation,
because it still mixes continuous torsor modes and discrete CPT generators, and
the boundary exterior-algebra Hilbert law/statistics is not derived.

The exterior-degree spectrum is also restrictive: for 14 primitive modes, only
degrees `4` and `10` give `1001`. Degree `4` has the cleaner Janus anchor because
M31 already has an `R4` translation/stress-energy sector; degree `10` is only the
dual complement.

Consistency audit: in strict M31, `C,P,T` are discrete connected-component
labels. If they remain discrete labels, they multiply sectors rather than add
three one-particle modes. Then the natural dimensions are:

```text
Lambda^4(C^11) = 330
2^3 * Lambda^4(C^11) = 2640
```

not `1001`. Therefore the `C(14,4)` route now has one precise missing theorem:

```text
derive boundary CPT fermionization / Clifford lift
```

Without that, `C(14,4)` is the best numerical clue, not a legal no-fit selector.

Existing Z2/Sigma work helps but does not close this:

- resolved tunnel Pin lift: ready;
- Z2/Sigma spinor projection: ready;
- unit normal Clifford action: ready;
- projected charge reduction: ready, but `N_occ` remains open.

So the remaining theorem is not ordinary Pin geometry. It is stronger:

```text
C,P,T must become three occupiable boundary fermion/CAR modes,
with a derived exterior/Fock statistics and selected Lambda^4 sector.
```

Currently no such boundary fermionization law is derived.

Stronger alternative found after the consistency audit:

```text
dim Sym^4(C^11) = C(11 + 4 - 1, 4) = C(14,4) = 1001
```

This is cleaner than `Lambda^4(C^(11+3))` because it uses only the M31
continuous Janus Lie/torsor dimension `11`. The degree `4` is anchored by the
M31 `R4` translation/stress-energy block. It avoids treating `C,P,T` as
fermionic modes.

Current best candidate:

```text
boundary sector = homogeneous degree-4 symmetric states over the 11 Janus torsor modes
```

Still missing:

```text
derive boundary bosonic/Fock statistics;
derive why the physical sector is Sym^4;
derive Sym^4 -> a_min -> photon/ruler dynamics.
```

If those missing steps were derived, the chain would become:

```text
N = dim Sym^4(C^11) = 1001
a_min = 1/N
z_max = N - 1 = 1000
```

So this would exactly repair the pre-drag reach. The open issue is not arithmetic;
it is the state law connecting the M31 torsor Hilbert sector to the early throat.

Second audit: `N=1001` repairs BAO reach only under a linear-resolution map:

```text
a_min = 1/N
```

Other natural maps fail:

```text
area map:   a_min = 1/sqrt(N)     -> z_max ~ 30.6
volume map: a_min = 1/N^(1/3)     -> z_max ~ 9.0
entropy map: same scaling class as volume here
```

So the remaining theorem is even sharper:

```text
Sym^4(C^11) must count linear throat/redshift resolution states.
```

Cleanest current interpretation:

```text
Sym^4(C^11) counts states of the one-dimensional normal/redshift channel.
```

This is physically plausible because the early-branch BAO obstruction has been
reduced to the single lower bound `a_min`. It is still not derived: we need a
normal-channel spectral operator, or an equivalent boundary law, whose state
count is `dim Sym^4(C^11)`.

Report:

```text
outputs/reports/p0_eft_janus_plus_sector_photon_stress_conservation_gate.md
```

So the extension is real, but not yet an executable native BAO prediction.

Report:

```text
outputs/reports/p0_eft_janus_early_universe_native_plasma_extension_gate.md
```
