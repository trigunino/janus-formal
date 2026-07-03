# Janus Formal Scaffold

Depot de travail pour formaliser et tester un pipeline Janus autour de :

- modules Lean (`JanusFormal/`) ;
- scripts Python d'audit et de generation de rapports (`scripts/`) ;
- tests unitaires (`tests/`) ;
- donnees traitees minimales (`data/processed/`) ;
- documentation scientifique et cartes de sources (`docs/`, `formal/`).

## Etat actuel

Statut separe par niveau de preuve :

- `formal_topology_scaffold_complete = True`
- `aps_global_theorem_proved_without_axioms = False`
- `orbifold_global_theorem_proved_without_axioms = False`
- `unique_action_variation_proved_without_axioms = False`
- `pure_math_model_closed_without_axioms = True`
- `holst_geometric_lock_closed = Conditional`
- `late_time_growth_branch_observationally_viable = True`
- `cmb_bao_monommetric_camb_hooks_sufficient = False`
- `bi_sector_boltzmann_backend_required = Open`
- `active_geometry_core = Z2_tunnel_Sigma`
- `legacy_z4_modules_archived = True`
- `rp4_base_pin_sign_computed = True`
- `rp4_base_pin_plus_exists = True`
- `rp4_base_pin_minus_exists = False`
- `sigma_aps_pin_lift_obligations_declared = True`
- `sigma_aps_local_throat_model_closed = True`
- `sigma_eta_zero_mode_cancellation_closed = True`
- `sigma_parity_anomaly_cancellation_closed = True`
- `sigma_aps_trace_regularization_closed = True`
- `sigma_aps_boundary_pin_lift_closed = True`
- `around_sigma_z2_transport_closed = True`
- `projective_cover_survives_tunnel_surgery = True`
- `projective_tunnel_volume_ratio_unique = True`
- `phenomenological_sheet_split_inferred = False`
- `sigma_boundary_support_declared = True`
- `sigma_boundary_variational_package_declared = True`
- `sigma_boundary_nonlinear_residual_closed = True`
- `sigma_boundary_action_closed = True`
- `z2_sigma_model_closed_without_axioms = True`
- `z2_sigma_background_bibliography_checked = True`
- `projected_sigma_stress_tensor_derived = True`
- `z2_tunnel_junction_condition_derived = True`
- `z2_sigma_boundary_stress_extraction_formula_closed = True`
- `z2_sigma_throat_radius_law_closure_ready = False`
- `z2_sigma_embedding_gauge_closure_ready = False`
- `z2_sigma_tunnel_embedding_constraint_closure_ready = False`
- `z2_sigma_active_tunnel_embedding_of_a_closure_ready = False`
- `z2_sigma_tunnel_embedding_extrinsic_curvature_structural_ready = True`
- `z2_sigma_tunnel_embedding_extrinsic_curvature_of_a_ready = False`
- `z2_sigma_cartan_ghy_flrw_algebraic_projection_ready = True`
- `z2_sigma_cartan_ghy_flrw_scale_factor_closure_ready = False`
- `z2_sigma_holst_nieh_yan_flrw_closure_ready = False`
- `z2_sigma_matter_flux_flrw_closure_ready = False`
- `z2_sigma_tunnel_junction_flrw_algebra_ready = True`
- `z2_sigma_tunnel_junction_flrw_closure_ready = False`
- `z2_sigma_counterterm_flrw_closure_ready = False`
- `z2_sigma_flrw_boundary_stress_reduction_ready = False`
- `z2_sigma_boundary_stress_ready_for_flrw_projection = False`
- `z2_sigma_effective_fluid_structural_projection_ready = True`
- `z2_sigma_effective_fluid_numeric_closure_ready = False`
- `z2_sigma_background_equations_derived = True`
- `z2_sigma_numerical_background_closure_ready = False`
- `z2_sigma_distance_bao_bibliography_checked = True`
- `sigma_photon_geodesic_map_derived = True`
- `z2_sigma_bao_sound_ruler_derived = True`
- `z2_sigma_bao_direct_desi_dr2_data_ready = True`
- `z2_sigma_bao_prediction_vector_ready = False`
- `z2_sigma_growth_bibliography_checked = True`
- `z2_sigma_growth_perturbation_equations_derived = True`
- `z2_sigma_growth_prediction_vector_prerequisites_ready = False`
- `z2_sigma_growth_direct_sdss_eboss_data_ready = True`
- `z2_sigma_growth_prediction_vector_ready = False`
- `z2_sigma_cmb_boltzmann_equations_derived = True`
- `z2_sigma_cmb_non_compressed_planck_likelihoods_available = True`
- `z2_sigma_cmb_theory_spectra_ready = False`
- `z2_sigma_observational_equation_locks_closed = True`
- `z2_sigma_non_compressed_observation_gates_passed = False`
- `janus_z4_cmb_solver_status = ArchivedDiagnostic`
- `janus_z4_master_equation_path = ArchivedDiagnostic`
- `legacy_janus_z4_master_shape_regularization = ArchivedDiagnostic`
- `legacy_acoustic_polarization_joint_gate_passed = False`
- `legacy_closed_theta2_acoustic_polarization_candidate = ArchivedDiagnostic`
- `legacy_photon_polarization_boltzmann_hierarchy_closed_effective = ArchivedDiagnostic`
- `legacy_boltzmann_closed_effective_z4_cmb_candidate = ArchivedDiagnostic`
- `legacy_planck_likelihood_completeness_candidate_trial_allowed = False`
- `full_planck_validation_allowed = False`
- `closed_boltzmann_candidate_robust = True`
- `standalone_highl_TE_EE_acquired = False`
- `standalone_highl_TE_EE_handshake_passed = False`
- `full_observational_cosmology_no_fit_ready = False`

Le noyau mathematique actif `Z2_tunnel_Sigma` est ferme dans le ledger Lean/Python.
La validation observationnelle complete reste separee et bloquee par les anciens
chemins CMB/BAO archives, non par la topologie active.
Le prochain travail actif est la derivation des equations observationnelles
Z2/Sigma: fond, distances photon, regle sonore BAO, croissance et CMB Boltzmann.

Les derniers gates CMB/BAO montrent que les hooks mono-metriques CAMB sont utiles
comme diagnostics EFT, mais insuffisants comme preuve finale du modele complet.

Les anciens chemins CMB/Z4 sont maintenant archives comme diagnostics
historiques, car la geometrie active ne requiert pas de vrai `Z4` cyclique.
Le noyau actif du modele est :

- `S4 -> RP4` avec cover antipodal `Z2` ;
- chirurgie tubulaire aux poles Big Bang/Crunch ;
- gorge `Sigma` ;
- cycle `aroundSigma -> Z2 generator` ;
- quatre secteurs comme `Z2_sheet x Z2_charge`.

Un vrai `Z4` ne sera reouvert que si une monodromie/lift d'ordre 4 est prouve.

Historique CMB/Z4 archive :

- les spectres Planck officiels ne doivent pas consommer le solveur natif tant
  que la limite GR n'est pas validee contre une reference standard ;
- les deltas Z4 non nuls sont testes uniquement comme deviations controlees
  autour d'une baseline CAMB-GR sure ;
- le dernier gate acoustique/polarisation trouve un meilleur point
  `lambda_T=-0.008`, `lambda_E=-0.02` avec `delta_chi2 ~= -9.49`, mais il ne
  passe pas : les gardes de lissage TE/EE echouent ;
- la fermeture tight-coupling effective `Theta2` leve ce blocage : le gate
  ferme donne `delta_chi2 ~= -9.20`, interaction `~=-0.155`, et les gardes
  TE/EE passent ;
- statut exact : candidat acoustique/polarisation effectif, pas verdict Planck ;
- la hierarchie Boltzmann photon/polarisation est maintenant fermee au niveau
  effectif scalaire (`Theta_l`, `E_l`, source `Pi`, TCA -> free-streaming,
  convergence `lmax`) ;
- le trial Planck ferme-Boltzmann local preserve le gain
  (`delta_chi2 ~= -9.20`, ratio de preservation `~=1.000`) ;
- statut exact : `boltzmann_closed_effective_z4_cmb_candidate`, pas validation
  Planck globale.
- la complétude likelihood autorise le trial candidat, mais bloque la validation
  Planck complète car les standalone high-l TE/EE restent absents localement ;
- la robustesse locale du candidat passe : meilleur point non-edge, courbure
  locale détectée, gain conserve sous `lmax`/TCA.
- le candidat est gelé pour la prochaine validation : pas de retuning, pas de
  nouveau canal, pas d'ouverture slip/recombinaison/visibilité/miroir/primordial ;
- prochain verrou externe : acquérir ou raccorder standalone high-l TE/EE, puis
  tester exactement le même candidat.
- le handshake standalone TE/EE doit vérifier `C_l/D_l`, unités, signe TE,
  indexation `ell`, nuisance vector, foregrounds et sanity GR avant tout trial
  de décomposition high-l.

Freeze rule after checkpoint `8ce53806`: no new Z4 physics or parameter
retuning is allowed until standalone high-l TE/EE likelihood coverage is
acquired and the frozen candidate is rerun unchanged.

Archived CMB/Z4 master-equation status:

- patchwork slip/surface/minus-sector branches are frozen as diagnostic-only;
- the unique `U_Z4` master path is archived as diagnostic-only;
- localized-transition source replay is non-tangent (`parallel_fraction ~= 0.1906`);
- raw diagnostic spectra are pre-likelihood locked by TT/EE shape artifacts;
- bounded-tanh shape regularization clears those artifacts diagnostically, but
  is only transport-derived through the membrane equation
  `dR/dS = 1 - (R/L)^2`;
- its normalization is now tied to the orbifold membrane lock
  `L_transport = a_sigma = 2/3`;
- regularized diagnostic spectra are generated only as internal spectra, not
  as Planck likelihood inputs;
- the regularized diagnostic shape report clears the pre-likelihood shape
  lock, while preserving the separate full-action normalization lock;
- `MasterActionNormalizationGate` allows only the next likelihood handshake;
- `MasterLikelihoodHandshakeGate` marks diagnostic likelihood input readiness,
  but still forbids official Planck trial and promotion;
- `MasterDiagnosticLikelihoodTrialGate` runs only an internal GR-reference
  pseudo-likelihood; it uses no observed Planck data and makes no observational
  claim;
- `MasterOfficialLikelihoodPolicyGate` blocks observed Planck until wrapper,
  nuisance, non-overlap, GR reference, and no-retuning replay policies exist;
- `MasterObservedPlanckWrapperHandshakeGate` forbids mocks and pseudo-likelihood
  fallback; it remains blocked until a GR reference handshake exists on the same
  observed wrapper; complete high-l, low-l, and lensing wrapper coverage is now
  detected locally;
- the same-wrapper GR reference handshake is declared separately and performs
  no Z4 candidate replay;
- `MasterNoRetuningReplayGate` replays the fixed master source with
  `L_transport = a_sigma = 2/3`; no lambda, normalization, or channel retuning
  is allowed;
- `MasterObservedPlanckDiagnosticTrialGate` is opt-in for observed execution and
  never promotes directly; clean non-overlap accounting is required next;
- the first observed diagnostic execution rejects the current normalized master
  branch with large positive high-l non-overlap chi2;
- `MasterObservedNonOverlapAccountingGate` records that rejection without
  promotion;
- `MasterObservedFailureMapGate` localizes the failure to high-l acoustic shape;
- `MasterHighLAcousticRevisionScanGate` finds an upstream non-tangent revision:
  shared `U_Z4` normalization plus a high-l/Silk guard; no Planck rerun is
  allowed directly from the scan;
- `MasterRevisedSourceLevelRegenerationGate` regenerates all source channels
  from that revised upstream `U_Z4` v2 and still forbids spectra/Planck;
- `MasterRevisedCarrierTangentProjectionGate` verifies the v2 source is less
  carrier-tangent (`parallel_fraction < 0.7`) before any diagnostic spectra;
- `MasterRegularizedDiagnosticSpectraV2Gate` serializes GR and GR+Z4-v2
  diagnostic spectra after that projection, but still forbids likelihood use;
- `MasterDiagnosticShapeReportV2Gate` audits v2 shape stability and explicit
  non-overlap accounting; it still forbids likelihood evaluation;
- `MasterPreLikelihoodLockV2Gate` clears the v2 shape lock and allows only the
  next action-normalization/handshake step, not Planck evaluation;
- `MasterActionNormalizationV2Gate` ties the v2 normalization to the selected
  upstream master revision, shared `U_Z4`, and `L_transport = 2/3`;
- `MasterLikelihoodHandshakeV2Gate` marks v2 diagnostic likelihood input
  readiness while still forbidding likelihood evaluation and Planck trial;
- `MasterDiagnosticLikelihoodTrialV2Gate` runs only an internal GR-reference
  pseudo-likelihood diagnostic and makes no observational claim;
- `MasterOfficialLikelihoodPolicyV2Gate` blocks official Planck use until a v2
  wrapper, GR handshake, nuisance policy, and no-retuning replay are declared;
- `MasterObservedPlanckGRReferenceHandshakeV2` and
  `MasterObservedPlanckWrapperHandshakeV2Gate` verify wrapper availability and
  GR-reference conventions, while still blocking official Planck trial until
  v2 no-retuning replay;
- `MasterNoRetuningReplayV2Gate` replays the fixed v2 source/revision without
  lambda, normalization, revision, or new-physics retuning;
- `MasterObservedPlanckDiagnosticTrialV2Gate` is opt-in only and never promotes
  directly, even when an observed run is explicitly requested;
- `MasterObservedNonOverlapAccountingV2Gate` is the mandatory accounting layer
  for any explicit observed diagnostic run and never promotes directly;
- `MasterObservedFailureMapV2Gate` locks the explicit observed v2 rejection:
  high-l acoustic shape dominates, promotion/retuning/new physics remain blocked;
- `MasterHighLAcousticFailureAutopsyGate` decomposes the rejection into
  TT/TE/EE peak, zero-crossing, damping-tail and attribution gaps; it remains
  explanatory only and blocks Planck retry/retuning;
- `MasterPhotonBaryonMatchingGate` blocks the current `U_Z4 -> photon-baryon`
  mapping after the acoustic phase failure and requires upstream rederivation;
- `MasterSourceComponentDiagnosticSpectraGate` writes diagnostic-only
  SW/early-ISW/Doppler/Pi/Weyl component spectra without enabling likelihoods;
- `MasterPhotonBaryonAcousticCalculatorGate` starts the calculator-side rebuild:
  it reconstructs `Theta0`, Doppler and `Pi` from an oscillator/quadrature
  basis, writes a diagnostic payload, and still blocks spectra/Planck;
- `MasterAcousticCalculatorComponentSpectraGate`,
  `MasterAcousticCalculatorShapePhaseDampingGate`,
  `MasterSolverProvenanceManifestGate`, and
  `MasterSolverImplementationReadinessGate` close the internal solver checkpoint:
  `solver_implemented = true` only for diagnostic CMB generation, not Planck
  validation;
- `MasterUnlensedLensedSplitGate` and `MasterLensingRemapPolicyGate` add
  explicit unlensed/lensed diagnostic spectra and record that the current remap
  is an internal policy, not a physical lensing solver;
- `MasterFutureObservedPlanckDiagnosticReadinessGate` allows only a future
  observed diagnostic run under split/provenance/non-retuning guards; validation
  and promotion remain false;
- `P0EFTJanusZ4CompleteCMBSolverStack` records the complete solver stack:
  Z4 Boltzmann evolution, visibility/recombination, Weyl LOS lensing,
  per-cosmology regeneration, and a likelihood-ready theory vector. This enables
  diagnostic likelihood evaluation only; Planck validation remains false until
  an observed likelihood run succeeds.
- `P0EFTJanusZ4CompleteGRLimitShapeGate` checks the Z4-off/native GR limit
  against regenerated CAMB-GR shape before interpreting any Z4-on observed
  Planck result.
- The Z4-off limit is now explicitly anchored to the regenerative CAMB-GR
  provider. The internal LOS prototype is not used as the GR acoustic solver.
- `P0EFTJanusZ4CompleteConventionHandshake` records the GR-reference `C_l`
  convention calibration used to convert the internal proxy vector into a
  diagnostic CAMB-compatible convention; this is not a Planck validation.
- `P0EFTJanusZ4CompleteObservedPlanckDiagnosticGate` exports the calibrated
  complete solver vector into the observed Planck wrapper CSV convention and is
  opt-in only; `P0EFTJanusZ4CompleteObservedNonOverlapAccountingGate` forbids
  overlapping high-l totals from being used as validation.
- The explicit observed diagnostic rejects the current complete-solver branch:
  low-l is non-finite for the candidate and the available high-l+lensing
  non-overlap deltas are strongly positive; full Planck validation remains
  false.
- `P0EFTJanusZ4SolverInputManifestGate` now blocks Z4 observed interpretation
  until physical inputs, Z4 initial conditions, projection, minus-sector
  microphysics, and calibration policy are explicit. The current branch is
  blocked by hidden/default Z4 inputs and LS channel calibration.
- `P0EFTJanusZ4PureMathClosureAuditGate` records the pure math status:
  APS/Pin, orbifold 2:1, and action scaffolds are present, but the axiom-free
  global theorems remain open, so no-fit remains false.
- `P0EFTJanusTopologyLayerAlignmentGate` records the topology correction:
  the Janus global cover is `S4 -> RP4` with `Z2` antipodal cover; the four
  sectors are `Z2_sheet x Z2_charge`; cyclic `Z4` is only a packaging label
  until an order-4 monodromy is proved. The `RP4` base Pin sign is now computed:
  `Pin+` exists and `Pin-` is obstructed; the `Sigma` APS boundary lift is now
  closed by the dedicated Sigma APS gates, not inherited from the `RP2`/Boy-surface shadow. The
  Big Bang/Big Crunch pole coincidence and tubular tunnel replacement are
  tracked as a separate surgery layer, not as the free antipodal quotient itself.
- `P0EFTJanusProjectiveTunnelInterface` connects the projective cover to tunnel
  surgery: the throat `Sigma` supplies the `aroundSigma` cycle used by the Z2
  holonomy/flux path. A cyclic `Z4` remains blocked until an order-four lifted
  tunnel monodromy is proved.
- `P0EFTJanusAroundSigmaZ2CycleTransportGate` isolates the active cycle result:
  `aroundSigma` maps to the `Z2` generator without requiring cyclic `Z4`.
- `P0EFTJanusSigmaAPSPinLiftObligationGate` records the exact APS/Sigma package
  after the `RP4` base Pin+ computation: induced Pin structure, APS projector,
  Fredholm domain, eta/zero-mode cancellation, and parity anomaly cancellation.
- `P0EFTJanusSigmaAPSLocalThroatModelGate` closes the local compact orientable
  throat model: local induced Pin/spin data, APS projector, and Fredholm domain.
  It leaves eta/zero-mode and parity anomaly cancellation to subsequent gates.
- `P0EFTJanusSigmaAPSEtaCancellationGate` closes the Sigma boundary eta/zero-mode
  package: paired spectrum, trivial kernel, `eta=0`, `h=0`, and zero APS
  correction contribution. Parity is closed by the subsequent parity gate.
- `P0EFTJanusSigmaAPSParityAnomalyCancellationGate` closes the remaining APS
  parity anomaly by Z2 tunnel pairing: paired boundary orientations contribute
  opposite Dirac determinant phases, so the global parity anomaly cancels.
- `P0EFTJanusSigmaAPSTraceRegularizationGate` closes APS trace normalization
  after the Sigma APS package: Clifford trace normalization and APS heat-kernel
  regularization are declared standard.
- `P0EFTJanusProjectiveTunnelCoverSurvivalGate` records that equivariant
  tubular surgery preserves the two-fold `S4 -> RP4` cover.
- `P0EFTJanusProjectiveTunnelVolumeRatioGate` closes the topological
  cover/quotient volume ratio: degree-two cover plus descended invariant
  measure gives ratio `2`, unique by cover degree. It does not infer an
  independent phenomenological sheet-split parameter.
- `P0EFTJanusZ2TunnelCoreGate` is now the active geometric core.
- `P0EFTJanusZ2SigmaPureMathClosureAuditGate` is the active pure-math closure
  audit for the rewritten model; observational no-fit validation remains false.
- `P0EFTJanusZ2SigmaHardTheoremTargetRegistry` records the exact external/local
  theorem targets for the active Z2/Sigma model.
- `P0EFTJanusZ2SigmaObservationalRoadmapGate` starts the post-math track:
  background equations, Sigma photon distance map, BAO sound ruler, growth
  perturbations, and CMB Boltzmann equations must be derived on the active
  Z2/Sigma base before any full no-fit cosmology claim.
- `P0EFTJanusZ2SigmaBackgroundBibliographyGate` records that primary sources
  cover the Janus projective/tunnel topology, generic junction formalism, and
  generic Einstein-Cartan/Holst blocks, but no source closes the full projected
  Z2/Sigma background equations.
- `P0EFTJanusZ2SigmaProjectedStressTensorGate` derives the projected Sigma
  stress tensor from the closed Sigma boundary variation:
  `T_Sigma_ab = -2/sqrt(|h|) * delta S_Sigma / delta h^ab`, then Z2-projects it
  to the visible background.
- `P0EFTJanusZ2SigmaThroatRadiusLawGate` records the throat-radius law as the
  immediate missing input: generic FRW thin-shell wormholes allow an `a*R0`
  candidate, but active Janus/Sigma must derive `R_Sigma(a)` from geometry, not
  observations.
- `P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate` records the active
  no-fit route for that law: vary the Sigma boundary action with respect to
  `R_Sigma(a)`. The variational equation is ready, but not solved.
- `P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate` decomposes that radial
  equation as `E_CartanGHY + E_HolstNiehYan + E_matterFlux + E_junction +
  E_counterterm = 0`. The block sum is declared; the individual Janus/Sigma
  radial reductions are still open.
- `P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate` records the current
  dependency state of the block sum: Cartan-GHY, Holst/Nieh-Yan and junction
  are structurally reduced, while matter-flux and counterterm still block
  `E_RSigma` expansion and `R_Sigma(a)`.
- `P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate` records the current
  no-fit solution frontier: the variational equation and conditional embedding
  map are ready, while matter-flux and counterterm still block the radius
  solution certificate.
- `P0EFTJanusZ2SigmaCartanGHYRadialBlockGate` reduces the Cartan-GHY radial
  block structurally as `delta_RSigma[sqrt(|h|) K]`; evaluation as a function of
  scale factor still requires active `R_Sigma(a)` and `X_±(a)`.
- `P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate` declares the Holst/Nieh-Yan
  radial block as the variation of the Sigma torsion pullback. Its scale-factor
  evaluation still requires the active torsion pullback and Immirzi radial
  profile.
- `P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate` records the standard
  thin-shell transport from a solved `R_Sigma(a)` plus proper-time/radial gauge
  equations to `X_+/-`. It remains blocked until the no-fit throat-radius law is
  solved and inserted into the gauge equations.
- `P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate` closes only the
  conditional thin-shell map: if `R_Sigma(a)` is supplied, proper-time/radial
  gauge equations determine `X_+/-`. It does not derive `R_Sigma(a)`.
- `P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate` imports generic
  dynamic-shell kinematics and declares the map `R_Sigma(a) -> X_±(a)`. It
  remains open until the radial variational equation is solved without an
  observational radius fit.
- `P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate` records that primary
  thin-shell literature closes only the conditional map
  `R_Sigma(a) + gauge equations -> X_+/-`; active embedding, tangent frames and
  unit normals remain blocked until `R_Sigma(a)` is derived.
- `P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate` records the standard
  transport `X_+/- (a) -> partial_a X_+/- -> E_a^mu`; it remains blocked until
  the active embedding functions are derived.
- `P0EFTJanusZ2SigmaTangentNormalOrientationGate` imports the generic thin-shell
  tangent frame, unit normal, normalization, and orientation conventions. It
  now receives `epsilon_Z2=-1` from projective-tunnel gluing, but remains open
  until the active resolved-tunnel embedding supplies frames and unit normals.
- `P0EFTJanusZ2SigmaCoframeConnectionPullbackGate` imports the first-order
  coframe/spin-connection machinery and declares `e^I_Sigma = X_Sigma^*(e^I)`
  plus `omega^I_J|_Sigma = X_Sigma^*(omega^I_J)`. It remains open until the
  active tunnel embedding supplies the coframe and spin-connection pullbacks;
  the Z2-oriented sign is already fixed by projective gluing.
- `P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGate` records the split
  between standard geometry and active Janus data: differential-form/coframe/
  connection pullback formulae are ready, while the actual pullbacks remain
  blocked on `X_+/- (a)`, tangent frames and unit normals.
- `P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate` imports the generic pullback of
  differential forms and Cartan's first structure equation
  `T^I = d e^I + omega^I_J wedge e^J`. It remains open until the active Sigma
  embedding, coframe pullback, spin-connection pullback, and Z2 normal
  orientation transport are available.
- `P0EFTJanusZ2SigmaMatterFluxRadialBlockGate` declares the matter-flux radial
  block from the standard shell flux `T_munu e_a^mu n^nu`. It remains open until
  the active Sigma throat is proven transparent or an active flux `F_a(a)` is derived.
- `P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate` records the required fork for
  that block: either derive transparency `F_a^Z2Sigma=0`, or compute the active
  projected flux. The route cannot be chosen by observational fit.
- `P0EFTJanusZ2SigmaMatterFluxFrontierGate` records the exact current frontier:
  transparency is blocked on normal-current and bulk-stress cancellation, while
  active projection is blocked on bulk stress and embedding data.
- `P0EFTJanusZ2SigmaMatterFluxTransparencyReadinessGate` records the transparent
  thin-shell criteria `J_n^Z2Sigma=0` and `F_a^Z2Sigma=0`; it remains blocked
  until active embedding, Sigma normals, normal current and bulk-stress
  cancellation are derived.
- `P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate` prevents a circular
  radius solve: active projected flux depends on `X_+/-[R_Sigma]`, so it cannot
  be used as an independent source for `R_Sigma(a)` unless transparency is
  derived independently or a coupled radius-flux system is formulated.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate` declares that non-transparent
  flux must be solved together with `R_Sigma(a)` through
  `E_RSigma[R_Sigma,F_a]=0` and the active projection
  `F_a^Z2Sigma[X_+/-[R_Sigma]]`; the system is not yet well posed or solved.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate` records the next
  proof obligation: local existence, uniqueness, continuous dependence,
  constraint compatibility, and homogeneous gauge fixing for the coupled
  `R_Sigma(a)`/`F_a^Z2Sigma(a)` system. These are not yet proved.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate` declares the analytic
  function-space frontier for that proof: radius regularity, flux trace space,
  embedding trace map, equation map continuity, and a linearized
  Fredholm/invertibility obligation. These analytic obligations remain open.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxTraceRegularityGate` narrows the first
  analytic sub-obligation: prove that `X_+/-[R_Sigma]`, the normal, tangent
  frame, and stress traces live in compatible spaces so
  `T_pm e_a^mu n_mu` is a well-defined boundary flux. This is still open.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate` records the conservative
  regularity target behind that trace proof: `Sigma` is treated as 3D,
  bulk-to-boundary trace loses `1/2` derivative, and the candidate ledger uses
  `s_bulk >= 3`, hence `s_Sigma >= 5/2`, above the boundary algebra threshold.
  The threshold proofs are still open.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate` transports
  the standard Sobolev trace and multiplication theorems to close the trace and
  product threshold checks for that candidate index choice. It deliberately
  leaves the normal/tangent frame trace support open as a separate geometry
  obligation.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate` records that
  `e_a^mu[R_Sigma]` and `n_mu[R_Sigma]` must be transported from a regular,
  co-oriented, nondegenerate Sigma embedding. The frame is not allowed to be an
  independent fit; continuity of those traces remains open.
- `P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate` states the
  conditional transport rule: once the active embedding is regular,
  co-oriented, and has nondegenerate induced metric, the tangent and normal trace
  support can feed the flux trace proof. The prerequisites are still open.
- `P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate` imports generic Spin/Pin
  obstruction machinery, the RP4 Pin+ result and the projective-tunnel topology.
  It declares `S_+ -> M_+` and `S_- -> M_-`, while keeping the resolved-tunnel
  Pin lift and active plus/minus spinor bundles open.
- `P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate` imports generic hypersurface
  spinor restriction. It declares `psi_+|_Sigma`, `psi_-|_Sigma`, and their
  boundary pair, while staying blocked on the active Sigma embedding and
  plus/minus spinor bundles.
- `P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate` imports APS and local
  Dirac-boundary projector machinery. It declares
  `P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, n_Z2, APS/Pin data)` and forbids any
  fitted boundary phase or free chiral-bag angle.
- `P0EFTJanusZ2SigmaSpinorBundleProjectionGate` imports generic spinor-bundle,
  hypersurface-restriction and APS-boundary machinery. It declares
  `psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, APS/Pin data)` and
  remains open until active plus/minus spinor bundles and the Z2/Sigma boundary
  projection are derived.
- `P0EFTJanusZ2SigmaSpinorProjectionReadinessGate` records that generic
  hypersurface spinor restriction and APS/local projection formulae are ready.
  The active plus/minus projection still waits for the resolved tunnel Pin lift,
  Sigma boundary spinor data, and the idempotent Z2/Sigma projection map.
- `P0EFTJanusZ2SigmaProjectedDiracActionReductionGate` imports the first-order
  curved Dirac action plus Holst/fermion coupling context and records the
  active reduction `S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-; psi_Sigma^Z2)`.
  It forbids fitted effective masses, boundary phases, and chiral angles.
- `P0EFTJanusZ2SigmaProjectedDiracActionReadinessGate` records that the standard
  curved-Dirac and Holst-fermion formulae are ready. The active projected action
  still waits for coframe/connection pullbacks and Z2/Sigma spinor projection.
- `P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate` imports the curved Dirac
  action with tetrad/spin-connection inputs and the Holst/fermion coupling
  context. It remains open until active plus/minus spinor bundle data and the
  Z2/Sigma projection are derived.
- `P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate` imports the generic Dirac
  U(1) Noether current and declares
  `J_Z2Sigma^mu = P_Z2Sigma(J_+^mu, J_-^mu; psi_Sigma^Z2)`. It remains blocked
  until the projected Dirac action is reduced.
- `P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate` projects that Dirac current
  on the active Sigma normals: `J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-`. It keeps
  the transparency test `J_n^Z2Sigma=0` blocked until the projected current and
  Sigma normals are derived.
- `P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate` declares the
  thin-shell bulk-stress flux `F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^-` and keeps
  zero-flux/Z2 cancellation open until active bulk stresses, tangents and
  normals are derived.
- `P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate` imports the generic Dirac
  Noether current `J_pm^mu = psi_bar_pm gamma_pm^mu psi_pm`, but keeps the
  active plus/minus matter currents blocked until the matter actions are derived.
- `P0EFTJanusZ2SigmaNormalMatterCurrentGate` declares the no-normal-current
  test `J_n^Z2Sigma = J_mu n^mu = 0`; it remains open until active plus/minus
  matter currents and Sigma normals are derived.
- `P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate` records the standard Dirac
  Noether current and normal projection formulae; `J_n^Z2Sigma=0` remains
  blocked on active Sigma normals and projected Dirac currents.
- `P0EFTJanusZ2SigmaMatterFluxTransparencyGate` records the sufficient condition
  for the transparent branch `F_a^Z2Sigma=0`; it is not yet derived for the
  active throat.
- `P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate` records the non-transparent
  branch: project `T^±_{μν}` on Sigma tangents/normals. It is blocked on active
  bulk stresses and active embedding data.
- `P0EFTJanusZ2SigmaBulkStressOfAGate` declares the plus/minus bulk stress
  tensors on the active throat. It remains open until sector densities/pressures
  and Holst torsion stress are derived as functions of `a`.
- `P0EFTJanusZ2SigmaSectorDensityPressureOfAGate` imports the standard FLRW
  perfect-fluid continuity form for each sector but keeps equations of state and
  normalizations open until derived from action/topology, not observations.
- `P0EFTJanusZ2SigmaHolstTorsionStressOfAGate` declares the Holst/Nieh-Yan
  torsion stress slot by metric variation. It remains open until the active
  Z2/Sigma torsion solution and dynamic Immirzi profile are derived as functions
  of `a`.
- `P0EFTJanusZ2SigmaImmirziProfileOfAGate` imports the generic dynamic
  Barbero-Immirzi scalar-field/Nieh-Yan route. It remains open until the active
  bulk Immirzi equation, Sigma boundary condition, and Z2/Sigma projection yield
  `gamma_Immirzi(a)`.
- `P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate` declares the variation
  slots `E_gamma=0` and `B_gamma^Sigma=0` from scalar-Immirzi Holst/Nieh-Yan
  variation. It remains open until the active torsion pullback and spinor source
  reduce those slots.
- `P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGate` imports the generic
  Sciama-Kibble/Cartan spin-torsion constraint and records the active
  Z2/Sigma source obligations: spin current, boundary torsion source, and
  dynamic Immirzi profile.
- `P0EFTJanusZ2SigmaSpinCurrentOfAGate` imports the canonical spin tensor and
  Dirac axial-current relation but keeps the active fermion distribution,
  spin-polarization history, and Z2/Sigma projection open.
- `P0EFTJanusZ2SigmaFermionDistributionOfAGate` records the two generic routes
  found in the literature: Dirac gas or Weyssenhoff spin fluid. It remains open
  until the active route and plus/minus projected distributions are derived from
  the Z2/Sigma action/topology.
- `P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate` imports Fermi-Dirac
  occupation and phase-space moment machinery. It keeps `f_pm(q,a)` blocked on
  number normalization, mass/temperature law, regime and chemical potentials.
- `P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate` declares the number-constraint
  inversion fixing `mu_pm(a)` from `N_pm`, `T_pm(a)`, `m_pm` and regime data.
  It forbids fitting chemical potentials.
- `P0EFTJanusZ2SigmaDiracDegeneracyFactorGate` declares the internal/spin
  degeneracy factors `g_+`, `g_-` and projected `g_Z2Sigma`. It keeps them
  blocked on active spinor bundles, projection data and route selection.
- `P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate` imports the standard kinetic
  Fermi-gas integrals for `rho_pm(a)` and `p_pm(a)`, but keeps the active
  plus/minus equation of state blocked on distribution, regime, and
  mass/temperature derivations.
- `P0EFTJanusZ2SigmaKineticMomentFluidClosureGate` imports the kinetic
  stress-energy moment `T_munu[f]` and records the FLRW perfect-fluid reduction.
  It remains blocked until projected distributions and isotropy/no-anisotropic
  stress are derived.
- `P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate` records the
  needed isotropy condition `f_pm(q_vec,a)=f_pm(|q|,a)` and
  `pi_ij=T_ij-p h_ij`; the projected FLRW fluid closure remains blocked until
  the Z2/Sigma distribution isotropy and zero projected anisotropic stress are
  derived.
- `P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate` imports the standard
  Fermi-Dirac radiality argument: if `E_pm(q_vec,a)=E_pm(|q|,a)` and the
  Z2/Sigma projection preserves radial dependence, then the plus/minus
  occupations are momentum-isotropic. The active radial dispersion and
  projection-preservation proof remain open.
- `P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate` records the standard
  massive-particle relation `epsilon_pm(q,a)=sqrt(q^2+a^2 m_pm(a)^2)`.
  It keeps radiality blocked until scalar plus/minus mass laws and FLRW
  momentum frames are derived on the active Z2/Sigma background.
- `P0EFTJanusZ2SigmaRadialOccupationProjectionGate` records the symmetry
  condition needed for the throat projection: if `P_Z2Sigma` is equivariant
  under FLRW momentum rotations, then radial plus/minus occupations project to
  a radial Z2/Sigma occupation. The active equivariance proof remains open.
- `P0EFTJanusZ2SigmaFLRWMomentumFrameGate` records the standard FLRW
  orthonormal/comoving momentum frame `q_i=a p_hat_i`. It remains blocked on
  the active plus/minus coframe pullbacks and projected frame construction.
- `P0EFTJanusZ2SigmaDiracScalarMassLawGate` records the generic curved-space
  Dirac fact that the mass term is a local Lorentz scalar. The active
  plus/minus mass laws still have to be derived from the projected Dirac action
  and Z2/Sigma projection, not fitted.
- `P0EFTJanusZ2SigmaDiracMassTermFromActionGate` records the coefficient
  extraction step `m_pm(a)=coefficient_of(psibar_pm psi_pm)` from the reduced
  plus/minus Dirac actions. It remains blocked until the projected Dirac action
  reduction is closed.
- `P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGate` records the local
  plus/minus decomposition into kinetic, mass-bilinear and axial-torsion terms.
  It remains blocked until the active plus/minus matter actions are ready.
- `P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate` records the lift from the
  resolved tunnel frame bundle to the Pin bundle and its plus/minus restrictions.
  It remains blocked on the active resolved-tunnel frame bundle and Pin lift.
- `P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate` records the active
  embedding checks needed before the Sigma throat can count as a smooth embedded
  submanifold: full-rank immersion, topological embedding, regular radius and
  Z2-equivariance. It remains blocked until `X_+/-` are derived.
- `P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate` records the embedded-submanifold
  prerequisites needed before applying collar/tubular-neighborhood theorems to
  the Sigma throat. It remains blocked on active `X_+/-` embeddings, regular
  nonzero throat radius, rank, topological embedding and Z2 equivariance.
- `P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate` records the standard
  collar/tubular-neighborhood theorem interface needed around the Sigma throat.
  It remains blocked until Sigma is proven as a smooth embedded throat with a
  derived normal bundle and compatible plus/minus collars.
- `P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate` records the collar,
  tubular-throat and smooth-gluing obligations needed to build the resolved
  tunnel atlas after polar-neighborhood removal. It remains blocked until the
  collars, gluing map and transition maps are derived.
- `P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate` records the construction of
  `T M_res` and `F(M_res)` after tubular replacement. It remains blocked until
  the resolved-tunnel smooth atlas and tangent bundle are derived.
- `P0EFTJanusZ2SigmaFermionRouteSelectionGate` selects the Dirac/spinorial route
  from the active Sigma spinor-variation channel. Weyssenhoff remains only a
  possible coarse-grained approximation, not the primitive active route.
- `P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate` imports the conserved
  curved-spacetime Dirac charge integral and declares
  `N_Z2Sigma = P_Z2Sigma(N_+, N_-; psi_Sigma^Z2)`. It remains blocked on the
  projected current, spinor projection, and anomaly/boundary-leak guards.
- `P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate` imports the conserved
  Dirac number-current dilution law `n_pm(a)=N_pm/a^3`; it remains open until
  `N_+`, `N_-`, and the projected Z2/Sigma number density are derived.
- `P0EFTJanusZ2SigmaDiracNumberNormalizationGate` declares the conserved
  Noether-charge integrals for `N_+`, `N_-`, and the projected throat charge.
  It remains open until those charges are fixed by active spinor boundary data
  or topology, not fitted.
- `P0EFTJanusZ2SigmaDiracHolstVertexOfAGate` imports the generic result that
  Holst gravity with fermions yields an Immirzi-dependent torsion-mediated
  four-fermion vertex. It remains open until the active torsion solution,
  spin current, Immirzi profile and Sigma projection are derived.
- `P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate` imports generic
  thermal averaging of `sigma v` and the Gondolo-Gelmini relativistic averaging
  route. It remains open until the active Z2/Sigma matrix elements and
  phase-space measures are derived.
- `P0EFTJanusZ2SigmaDiracInteractionRateOfAGate` imports the generic kinetic
  rate structure `Gamma_pm(a)=n_bath,pm(a)<sigma v>_pm(a)`. It remains open
  until the active bath densities, cross sections, and Z2/Sigma projection are
  derived.
- `P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate` imports momentum redshift
  and the relativistic decoupled scaling guard, while keeping the massive
  Fermi-gas regime, decoupling scale, and projected mass/temperature law open.
- `P0EFTJanusZ2SigmaDiracRegimeSelectionGate` declares the route criterion
  `m_pm/T_dec_pm`: relativistic, massive, or semi-relativistic. It remains open
  until active masses and decoupling temperatures are derived.
- `P0EFTJanusZ2SigmaDiracDecouplingConditionGate` imports the standard
  freeze-out criterion `Gamma_pm(a_dec)=H_Z2Sigma(a_dec)` and the optional
  Sigma boundary-condition route. It remains open until the interaction rates
  `Gamma_+/- (a)` and active background `H_Z2Sigma(a)` are derived.
- `P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGate` reduces the tunnel-junction
  radial block structurally from the Lanczos-Israel jump residual. Its
  scale-factor form remains blocked on `DeltaK_s(a)`, `DeltaK_tau(a)` and the
  non-circular surface-stress partition.
- `P0EFTJanusZ2SigmaCountertermRadialBlockGate` declares the radial variation of
  the unique Sigma counterterm. It remains open until the explicit active
  density `L_ct` is expanded.
- `P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate` records the allowed local
  active basis for that density: `h_ab`, `K_ab`, Sigma torsion pullback,
  Immirzi/radion boundary fields and Z2 orientation, with no new fitted
  counterterm freedom.
- `P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate` isolates the first
  residual coefficient `R_e`; it remains open until the active Sigma coframe
  variation is transported into `delta h`, `delta K` and torsion-pullback data.
- `P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate` isolates that
  transport step: `delta e -> delta h_ab`, `delta e -> delta K_ab`, and
  `delta e -> delta X_Sigma^*T^I`. It forbids a metric-only shortcut.
- `P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate` closes the
  algebraic part `delta e -> delta h_ab` via
  `delta h_ab = eta_IJ(delta e_a^I e_b^J + e_a^I delta e_b^J)`. It leaves
  `delta K` and torsion-pullback transport open.
- `P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate`
  isolates `delta e -> delta K_ab`. It declares
  `K_ab = e_a^mu e_b^nu nabla_mu n_nu` and keeps the transport blocked on
  active embedding, tangent/normal traces and connection variation.
- `P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate`
  records the Cartan tetrad-variation formula
  `delta_e T^I = D_omega(delta e^I)` for the independent-connection branch.
  The Sigma torsion pullback and allowed-basis expansion remain open.
- `P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGate` records that
  oriented pullback commutation and the ambient Cartan torsion formula are closed.
  The active embedding, coframe/connection pullback, Sigma torsion pullback and
  FLRW irreducible basis still block the torsion-pullback transport.
- `P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGate` aggregates
  the three tetrad transports. It records that `delta e -> delta h_ab` is closed,
  while `delta e -> delta K_ab` and torsion-pullback transport still block `R_e`.
- `P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate` isolates the
  spin-connection coefficient `R_omega`; it remains open until the active
  Sigma connection variation is transported through torsion and Nieh-Yan data.
- `P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate` records the
  fixed-coframe transport `delta_omega T^I = delta omega^I_J wedge e^J` and
  blocks until the Sigma pullback/orientation transport is proved.
- `P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate` records the
  field-space split in which `delta_omega X_Sigma = 0`; embedding variation is
  kept in the separate `R_X` channel.
- `P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate` records the
  fixed-map commutation
  `delta_omega X_Sigma^*omega = X_Sigma^*(delta_omega omega)`.
- `P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate` fixes the
  active Z2 normal-orientation coefficient as `epsilon_Z2=-1` from the
  projective-tunnel sheet exchange.
- `P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate` keeps the same
  commutation oriented by that projective-tunnel sign, not a fitted sign.
- `P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate` isolates
  the fixed-embedding condition `delta_omega X_Sigma = 0` and the commutation
  target `delta_omega X_Sigma^*omega = X_Sigma^*(delta_omega omega)`.
- `P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGate`,
  `P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGate` and
  `P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGate` isolate
  `R_psi`, `R_X` and `R_matter` without promoting any fitted residual
  coefficient.
- `P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate` aggregates the five
  residual coefficients `R_e`, `R_omega`, `R_psi`, `R_X` and `R_matter`; all
  remain open before the residual one-form can be explicit.
- `P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate` splits the
  nonlinear residual into tetrad, connection, spinor, embedding and matter-flux
  channels before any integrability claim is allowed.
- `P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate` records the exactness
  condition `d_field alpha_res = 0`; its field-space curl is still open.
- `P0EFTJanusZ2SigmaCountertermResidualExtractionGate` isolates the missing
  extraction step: the nonlinear residual one-form must be made explicit,
  proved integrable and integrated into the unique primitive `L_ct`.
- `P0EFTJanusZ2SigmaCountertermDensityExpansionGate` isolates that missing
  density expansion and forbids adding a fitted counterterm coefficient.
- `P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate` summarizes the
  required counterterm chain: explicit residual one-form, field-space exactness,
  integrated primitive, local density expansion, then radial variation. The
  chain is still open and cannot feed `R_Sigma(a)` yet.
- `P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate` records the allowed shell
  proper-time/radial embedding gauges. These remove parametrization redundancy
  but do not derive `R_Sigma(a)` or close `X_±(a)`.
- `P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate` imports the standard thin-shell
  induced-metric normalization equations. `T_±` derivatives are fixed once
  `R_Sigma(a)` is known; the active throat-radius law remains open.
- `P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate` records that the current
  matching, Z2-equivariance and regular-throat constraints declare the embedding
  problem but do not determine `X_±(a)` without a throat-radius law and embedding
  gauge.
- `P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate` is the active upstream
  embedding lock: `X_+^mu(a,xi)` and `X_-^mu(a,xi)` must be derived from the
  resolved projective tunnel before any `DeltaK_s(a)` or `DeltaK_tau(a)` can be
  used.
- `P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate` imports the generic
  thin-shell embedding machinery: `X_pm`, tangents, normals, induced metric
  matching, and `K_ab^pm`. It does not yet derive the active tunnel embedding
  functions needed for `DeltaK_s(a)` and `DeltaK_tau(a)`.
- `P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate` closes the algebraic
  Brown-York/Cartan-GHY FLRW projection in terms of
  `DeltaK_s(a)` and `DeltaK_tau(a)`. The Janus tunnel embedding functions
  themselves are still open.
- `P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate` imports the generic
  Holst/Nieh-Yan torsion relation from the literature, while keeping the active
  Janus/Sigma FLRW torsion pullback and `rho/p` reduction open.
- `P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate` imports the standard shell
  flux identity `F_a = T_munu e_a^mu n^nu` and the transparency-condition
  option; the active Janus throat flux or transparency proof remains open.
- `P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate` closes the standard
  trace-reversed FLRW junction algebra in terms of `DeltaK_s(a)` and
  `DeltaK_tau(a)`, while requiring a non-circular partition before using it as
  an independent `T_eff_ab` source.
- `P0EFTJanusZ2SigmaCountertermFLRWObligationGate` records that the
  Sigma-supported counterterm is structurally unique and cancels the nonlinear
  residual, but its active FLRW stress tensor still has to be varied and reduced.
- `P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGate` is the current component
  reduction lock: the induced FLRW Sigma metric and Z2 normal orientation are
  declared, but the Cartan-GHY, Holst/Nieh-Yan, matter-flux, tunnel-junction and
  counterterm blocks are not yet reduced to FLRW components.
- `P0EFTJanusZ2SigmaTunnelJunctionConditionGate` derives the Z2/Sigma junction
  condition as a Lanczos-Israel-like jump equation with the Z2 normal-orientation
  reversal included.
- `P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate` closes the structural
  effective background equations: Friedmann, acceleration, and continuity for
  `rho_eff_Z2Sigma` and `p_eff_Z2Sigma`.
- `P0EFTJanusZ2SigmaBackgroundEquationDerivationGate` is the first post-math
  equation gate. It requires the projected Sigma stress tensor, Z2 tunnel
  junction condition, Friedmann equation, acceleration equation, and continuity
  equation to be derived without reusing legacy LCDM or archived Z4 backgrounds.
- `P0EFTJanusZ2SigmaDistanceBAOBibliographyGate` records that standard FLRW
  distance measures, Etherington reciprocity, and BAO sound-horizon literature
  can be imported as generic machinery, but the Sigma photon map and Z2/Sigma
  sound ruler must be derived locally.
- `P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate` derives the visible photon
  distance map from the Z2/Sigma background: `D_H`, `D_M`, `D_A`, and `D_L`
  with an Etherington guard.
- `P0EFTJanusZ2SigmaBAOSoundRulerGate` derives
  `r_d^Z2Sigma = integral c_s^Z2Sigma/H_Z2Sigma dz`; fitted Planck `r_d` and
  compressed LCDM priors remain forbidden.
- `P0EFTJanusZ2SigmaGrowthBibliographyGate` records that standard perturbation,
  bimetric, Einstein-Cartan, and Janus structure-growth sources exist, but no
  source closes the active Z2/Sigma growth equations.
- `P0EFTJanusZ2SigmaGrowthPerturbationEquationGate` derives the active growth
  perturbation equation family on the Z2/Sigma background and forbids reuse of
  archived Z4 `mu` tables.
- `P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate` records that Ma/Bertschinger
  and CLASS/CAMB machinery can be imported generically, while Z2/Sigma metric
  sources must be local.
- `P0EFTJanusZ2SigmaCMBBoltzmannEquationGate` derives the structural CMB
  Boltzmann equation blocks on the active Z2/Sigma perturbation system and
  forbids archived Z4 CMB reuse.
- `P0EFTJanusZ2SigmaNonCompressedObservationGate` is the current outer gate:
  equations are closed, but growth, BAO, and CMB must still pass direct
  non-compressed observational gates before any full no-fit claim.
- `P0EFTJanusLegacyZ4ArchivePolicyGate` archives old Z4/CMB modules as
  diagnostic history; they are not active geometry.
- Active replacement gates are:
  `P0EFTJanusRP4PinSignComputationGate`,
  `P0EFTJanusSigmaAPSPinLiftObligationGate`,
  `P0EFTJanusSigmaAPSLocalThroatModelGate`,
  `P0EFTJanusSigmaAPSEtaCancellationGate`,
  `P0EFTJanusSigmaAPSParityAnomalyCancellationGate`,
  `P0EFTJanusSigmaAPSTraceRegularizationGate`,
  `P0EFTJanusRP4PinSignAuditGate`,
  `P0EFTJanusAroundSigmaZ2CycleTransportGate`,
  `P0EFTJanusProjectiveTunnelCoverSurvivalGate`,
  `P0EFTJanusProjectiveTunnelVolumeRatioGate`,
  `P0EFTJanusProjectiveTunnelCoverRatioGate`,
  `P0EFTJanusSigmaBoundaryActionSupportGate`,
  `P0EFTJanusSigmaBoundaryVariationalDecompositionGate`, and
  `P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate`.
- `P0EFTJanusSigmaBoundaryActionSupportGate` records that boundary support is
  localized on the tunnel throat `Sigma` and antipodal fixed-point boundaries
  are forbidden. The nonlinear boundary variation and full Sigma action closure
  are closed by the residual-closure gate.
- `P0EFTJanusSigmaBoundaryVariationalDecompositionGate` declares the Sigma
  boundary variational package: induced measure, Cartan/GHY, Holst/Nieh-Yan,
  matter-flux and tunnel-junction terms, plus tetrad/connection/spinor channels.
  The nonlinear residual is isolated and closed by the nonlinear residual gate.
- `P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate` closes the full Sigma
  boundary action: the unique Sigma-supported counterterm cancels the isolated
  nonlinear residual across tetrad, connection, and spinor channels.
- `P0EFTJanusFormalModelReauditAfterTopologyCorrectionGate` records the current
  reaudit: the resolved 2D tunnel shadow is `T2 -> Klein bottle`, while the Boy
  surface is only the unresolved projective shadow. The active Z2/Sigma pure
  math locks are now closed; observational validation remains separate.
- `P0EFTJanusZ4HardGlobalTheoremAvailabilityGate` records that no direct
  Lean/mathlib import currently closes APS/Pin, orbifold 2:1, or the unique
  Janus/Z4/Holst action theorem for this project geometry.
- `P0EFTJanusZ4HardGlobalTheoremReductionGate` reduces the closure problem to
  atomic obligations: APS index package, Janus cover ratio, full action
  variation, and full Ward closure.
- `P0EFTJanusZ4FullActionAtomicClosureGate` further reduces the action branch
  to linearized action, determinant measure, boundary closure, nonlinear
  Euler-Lagrange residual, and Ward closure.
- `P0EFTJanusZ4DeterminantMeasureAssemblyBridge` closes the determinant-measure
  insertion bridge into the full action assembly.
- `P0EFTJanusZ4VolumeSolderCountertermBridge` derives the identity-channel
  EFT counterterm from the Janus volume-solder invariant at the algebraic
  boundary-identity level.
- `P0EFTJanusZ4BoundaryPureClosureObstructionGate` records the current boundary
  obstruction: standard sources alone leave an identity residue, the Janus
  counterterm bridge is available, but the nonlinear boundary variation remains
  open.
- `P0EFTJanusZ4NonlinearBoundaryVariationObligationGate` reduces that remaining
  boundary problem to full tetrad, Cartan-connection, membrane-junction,
  gauge-fixing, and second-variation residual obligations.
- `P0EFTJanusZ4WardAtomicClosureGate` reduces the Ward branch to weighted
  current cancellation, global divergence, anomaly, and obstruction obligations.
- `P0EFTJanusZ4NonlinearELResidualObligationGate` imports the nonlinear residual
  factorization into the active proof surface: both EL residuals reduce to one
  common obstruction `O_nl`, whose vanishing is still open.
- `P0EFTJanusZ4GaugeFixingVariationUniquenessGate` isolates the action gauge
  branch: gauge insertion and observation-independent convention are scaffolded,
  but residual gauge removal by Janus geometry remains open.
- `P0EFTJanusZ4APSIndexPackageObligationGate` records the APS/Pin status:
  local spectral-pairing and kernel-trivialization interfaces are available,
  but the global Pin lift, APS Fredholm domain, parity anomaly, and trace
  regularization theorem remain open.
- `P0EFTJanusZ4OrbifoldCoverRatioObligationGate` records the orbifold status:
  Z2 cover, fixed-set, flux-law, and local two-to-one multiplicity interfaces
  are available, but the global Euler/holonomy class and uniqueness of the
  volume ratio remain open.
- `P0EFTJanusZ4HardExternalTheoremTargetRegistry` records the exact theorem
  targets that an imported result or future local proof must satisfy before any
  no-fit promotion can be considered.
- official Planck likelihood, candidate promotion, and full validation remain
  forbidden until an explicit official-likelihood policy gate is opened and
  passed separately.

Point d'entree principal actif :

- `JanusFormal.lean`
- `JanusFormal/P0EFTJanusZ2SigmaPureMathClosureAuditGate.lean`
- `scripts/build_p0_eft_janus_z2_sigma_pure_math_closure_audit_gate.py`

## Validation rapide

```bash
python -m unittest tests.test_p0_eft_janus_active_z2_sigma_facade_audit_script
python -m unittest tests.test_p0_eft_janus_z2_sigma_pure_math_closure_audit_gate_script
lake build JanusFormal
```

Validation plus large :

```bash
lake build
```

Validation Lean active :

```bash
lake build JanusFormal
```

`JanusFormal.lean` est volontairement une facade active minimale Z2/Sigma. Le
graphe complet historique reste disponible dans :

```bash
lake build JanusFormal.AllImportsArchive
```

Validation CMB/Z4 archive :

```bash
lake build JanusFormal
python -m unittest tests.test_p0_eft_janus_z4_cmb_diagnostic_master_report_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate_script
python -m unittest tests.test_p0_eft_janus_z4_photon_polarization_boltzmann_hierarchy_closure_gate_script
python -m unittest tests.test_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial_script
python -m unittest tests.test_p0_eft_janus_z4_planck_likelihood_completeness_gate_script
python -m unittest tests.test_p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate_script
python -m unittest tests.test_p0_eft_janus_z4_standalone_teee_acquisition_gate_script
python -m unittest tests.test_p0_eft_janus_z4_standalone_teee_handshake_gate_script
```

`JanusFormal.LegacyCMB` est une archive compile-only des anciens essais
mono-metriques CAMB/Planck. Ne pas l'utiliser comme validation standard du
solveur Z4 natif ni comme preuve physique.

## Organisation utile

- `JanusFormal.lean` importe l'ensemble des modules Lean actifs.
- `JanusFormal/LegacyCMB.lean` regroupe les anciens diagnostics mono-metriques
  CAMB/Planck. Ils restent hors validation CMB/Z4 standard.
- `JanusFormal/P0EFT*.lean` contient les verrous formels EFT/topologie.
- `scripts/build_p0_eft_run*.py` genere les payloads et rapports d'audit.
- `tests/test_p0_eft_run*.py` verifie les statuts exposes par ces scripts.
- `data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_points.csv` contient le jeu traite minimal suivi.

## Non suivi par Git

Le depot exclut volontairement :

- `.venv/`
- `.lake/`
- `outputs/`
- `data/raw/`
- `*.egg-info/`
- caches Python

Ces elements sont regenerables localement et ne doivent pas etre pousses.

## Archived CMB/Z4 checkpoint

- Standalone high-l TE/EE Cobaya wrappers and `.clik` data are available locally.
- GR/CAMB standalone TE/EE handshake passes.
- Frozen candidate high-l decomposition was rerun unchanged:
  - `lambda_T = -0.008`
  - `lambda_E = -0.02`
  - legacy overlapping diagnostic total: `delta_chi2 = -9.4326`
  - non-overlapping combined high-l total: `delta_chi2 = -5.6962`
  - non-overlapping decomposed high-l total: `delta_chi2 = -5.3212`
  - `delta_chi2_highl_TE = +0.0412`
  - `delta_chi2_highl_EE = -0.2733`
- `planck_highl_decomposed_effective_candidate = True`
- nuisance/foreground policy: `fixed_nuisance_effective_candidate`;
  no global nuisance profiling has been performed.
- nuisance sensitivity: local symmetric nuisance perturbations preserve the
  non-overlap gains; status `nuisance_sensitivity_checked_candidate`.
- local nuisance profiling: profiled gains remain favorable
  (`-5.1768`, `-5.9829`), but nuisance boundary hits are present
  (`calib_217T`, `gal545_A_217`), so
  `local_profiled_nuisance_effective_candidate = False`.
- boundary-safe nuisance profiling: guarded/fixed policies remove the boundary
  issue while preserving gains:
  - `boundary_guarded`: `(-5.7058`, `-6.5223`) for combined/decomposed bases;
  - `problem_nuisances_fixed`: `(-13.1561`, `-12.0977`);
  - `boundary_safe_local_profiled_candidate = True`.
- cosmology parameter policy:
  - standard cosmology parameters are fixed in the current spectra-table backend;
  - `lambda_policy = frozen_from_candidate_spec_after_internal_trials`;
  - local cosmology profiling is blocked until a regenerating CAMB/Z4 backend exists.
- regenerative backend gate:
  - current backend uses `source_of_spectra = csv_fixed`;
  - CAMB-GR spectra and Z4 deltas are not regenerated under cosmology changes;
  - local cosmology profiling remains forbidden until `source_of_spectra = regenerated`.
- regenerative CAMB-GR provider:
  - `lambda_T = lambda_E = 0`;
  - spectra are regenerated from CAMB per cosmology point;
  - provenance/cache hashes are emitted for cosmology, nuisance, lambdas and backend versions.
- regenerative GR handshake:
  - regenerated CAMB-GR matches the safe CAMB-GR reference at `lambda_T=lambda_E=0`;
  - conventions are explicit: `C_l`, lensed CMB spectra, `C_L^phiphi`, TE sign and ell indexing.
- regenerative cache invalidation:
  - changing `omega_b`, `omega_cdm`, `H0`, `tau`, `A_s` or `n_s` changes hashes and spectra;
  - stale CSV reuse is forbidden.
- regenerative frozen candidate replay:
  - `lambda_T = -0.008`, `lambda_E = -0.02`, no retuning;
  - checkpoint high-l deltas are replayed at reference cosmology;
  - `z4_delta_source = reference_cosmology_replay`, so cosmology profiling remains blocked.
- regenerative Z4 delta per cosmology:
  - effective closed-Boltzmann spectral deltas regenerate with cosmology;
  - strict source-level replay is now the replay checkpoint for the regenerative backend.
- source-level/readiness gates:
  - `delta_S_T_Z4` and `Pi_source_Z4` now regenerate per cosmology;
  - `LocalCosmologyProfilingReadinessGate` requires strict source-level replay before local profiling.
- regenerative temperature source delta:
  - `delta_S_T_Z4` now regenerates per cosmology for the frozen `early_isw_only` temperature channel;
  - temperature remains source-level, not a direct `C_l` patch.
- regenerative polarization Pi source:
  - `Theta_l`, `E_l`, `Pi_source_Z4`, TCA and opacity objects now regenerate per cosmology;
  - `Pi_source_Z4` is derived from multipoles, with no free `Theta2` tag and no direct TE/EE patch.
- strict source-level frozen replay:
  - the frozen candidate is replayed with `z4_delta_source = strict_source_level_regenerated`;
  - the checkpoint replay matches and local cosmology profiling readiness is open.
- local cosmology profiling:
  - `local_cosmology_profiling_allowed = True` for the first frozen-lambda local profile;
  - local cosmology+nuisance profiling passes with frozen lambdas:
    - combined high-l profile gain: `-4.6204804254`;
    - decomposed high-l profile gain: `-4.2056083637`;
    - best local cosmology key: `omega_cdm`;
    - no nuisance boundary hits in the profiled bases.
  - this promotes only `local_cosmology_nuisance_profiled_effective_candidate`, not Planck-full status.
- carrier degeneracy diagnostics:
  - the 1D `omega_cdm` carrier profile does not preserve the frozen-candidate gain;
  - combined high-l gain after `omega_cdm` marginalization: `+0.6827240820`;
  - decomposed high-l gain after `omega_cdm` marginalization: `+0.9162249090`;
  - all tested 2D carrier pairs with `omega_cdm` also fail to preserve the gain.
  - interpretation: `omega_cdm` absorbs the effective Z4 signal in local carrier profiling, so this blocks any stronger Planck-profiled claim.
- carrier tangent projection:
  - `90.4008%` of the frozen Z4 delta lies parallel to the local GR/CAMB carrier tangent space;
  - dominant spectral tangent direction: `A_s`, with `n_s` close behind;
  - orthogonal residual gain is unfavorable: combined `+18.6589`, decomposed `+18.2580`;
  - interpretation: the current effective Z4 signal is mostly carrier-tangent, not a robust orthogonal Planck signature.
- closure:
  - `carrier_degenerate_effective_candidate = True`;
  - `candidate_role = diagnostic_archived`;
  - the frozen early-ISW/closed-Boltzmann candidate must not be promoted or retuned.
- derived slip gate:
  - the gate contract is present, but `slip_source_derivation_available = False`;
  - `derived_slip_candidate_enabled = False`;
  - free slip parameters, free `eta(a,k)` ratios, direct `C_l` patches and raw toy LOS are forbidden;
  - next required artifact: a source-derived Z4/bimetric slip equation.
- bimetric slip source derivation:
  - source equation derived: `Lap_TF(delta_slip_Z4) = -chi*(Pi_plus_TF + Pi_minus_TF)`;
  - this closes the source-level slip equation only;
  - value-slip Green/normal-mode transport remains open, so Planck trials remain blocked.
- derived slip scaffolding:
  - plus/minus scalar variables, projection/mixing and stress sources are declared;
  - traceless spatial slip equation gate passes at source level;
  - regeneration readiness remains blocked until boundary Green/normal-mode transport is derived.
- slip transport kernel gate:
  - source-level slip is available, but value-level `deltaSlip_Z4(k,tau)` transport is not;
  - both acceptable routes are explicit: boundary Green transport or normal-mode transport;
  - Planck trials remain forbidden until a causal normalized transport kernel is derived.
- boundary Green slip transport gate:
  - route selected: `boundary_green`;
  - Green kernel is declared but not derived;
  - value-level slip and Planck trials remain blocked until retarded support, normalization and boundary jumps are closed.
- boundary Green operator closure gate:
  - operator type selected: `boundary_normal`;
  - `L_slip_Z4` is declared, but `L_slip_Z4 G = delta`, normalization, homogeneous-mode removal and regularity remain open.
- boundary-normal Green kernel solution:
  - finite-interval operator `L_slip_Z4 = -d_n^2 + k^2` solved with Z4 Dirichlet boundaries;
  - homogeneous mode removed by boundary conditions and value-level `deltaSlip_Z4` transport is now mathematically available;
  - Planck trials remain forbidden until source-level slip regeneration and tangent projection gates pass.
- derived slip value transport:
  - visible-sector projection selected: `boundary_normal_derivative`;
  - Dirichlet boundary value is explicitly zero, while the normal derivative projection is nonzero;
  - value-level `deltaSlip_Z4` and `deltaSlipDot_Z4` are available for the next regeneration gate.
- derived slip source-level regeneration:
  - reconstructs `deltaPhi_Z4 = (deltaW_Z4 + deltaSlip_Z4)/2` and `deltaPsi_Z4 = (deltaW_Z4 - deltaSlip_Z4)/2`;
  - regenerates temperature surface, early-ISW and Pi/polarization sources with the derived slip;
  - keeps Planck trials blocked until carrier-tangent projection is checked.
- derived slip carrier-tangent projection:
  - compares surface, early-ISW, Pi and full-slip source signatures against GR/CAMB carrier tangents;
  - logs active normal orientation and orientation-flip diagnostic only;
  - remains diagnostic-only and does not allow Planck promotion.
- full derived-slip archive / surface diagnostic:
  - full derived-slip source is archived as carrier-tangent (`A_s` dominated);
  - surface term is kept only as an orthogonality diagnostic;
  - surface Sachs-Wolfe use is blocked until photon-monopole and Doppler consistency are derived.
- photon-monopole Sachs-Wolfe closure:
  - forms `g * (deltaTheta0_Z4 + deltaPsi_Z4)` and a Doppler diagnostic instead of isolated `g * deltaPsi_Z4`;
  - keeps visibility and recombination frozen;
  - closed full-surface response is less tangent than no-slip but only weakly (`parallel_fraction ~= 0.794`);
  - remains pre-Planck and diagnostic-only.
- surface Doppler decomposition:
  - SW-only surface remains orthogonal, but Doppler completion reintroduces carrier tangency;
  - surface branch is classified as `weak_orthogonal_diagnostic`;
  - no candidate promotion or Planck trial is allowed.
- Doppler transport refinement:
  - derives photon dipole and baryon velocity responses with tight-coupling/Euler guards;
  - keeps visibility/recombination frozen and no Doppler amplitude free;
  - refined full-surface remains weak/carrier-tangent (`parallel_fraction ~= 0.834`).
- weak surface branch archive:
  - SW-only orthogonal component exists, but physical Doppler-completed branch is not promotable;
  - no Planck trial or candidate promotion is allowed.
- two-sector Boltzmann variables:
  - declares explicit `+` and `-` perturbation variables, metrics and Z4 projection/coupling data;
  - forbids `rho_eff` shortcuts, direct `C_l` patches and raw toy LOS;
  - requires conservation/Bianchi before spectra or Planck.
- two-sector conservation/Bianchi:
  - declares plus/minus continuity, Euler and shear closure rows;
  - uses explicit zero exchange terms and projected exchange balance;
  - keeps gravitational sign separate from thermodynamic density sign.
- two-sector initial modes:
  - declares plus/minus adiabatic, symmetric, antisymmetric Z4, relative isocurvature and projection modes;
  - forbids collapsing the hidden sector into a single CAMB adiabatic or `rho_eff` initial condition;
  - keeps spectra and Planck blocked until linear evolution closure.
- two-sector linear evolution:
  - declares `X' = A_Z4(k,tau) X + S_Z4(k,tau)` over explicit plus/minus state variables;
  - evolves fluid rows, metric constraints and projection rows under Bianchi guards;
  - keeps source regeneration, spectra and Planck blocked until stability/eigenmode checks.
- two-sector stability/eigenmodes:
  - checks finite eigenvalues and no explosive real modes over representative `k`;
  - guards symmetric, antisymmetric Z4, relative isocurvature and projection modes;
  - allows source-level regeneration only, still no spectra or Planck.
- two-sector source-level regeneration:
  - regenerates plus, minus, antisymmetric Z4 and projection sources;
  - exposes Weyl, monopole and Pi projected source diagnostics;
  - allows carrier-tangent projection only, still no spectra or Planck.
- two-sector carrier-tangent projection:
  - projects Weyl, monopole, Pi and full two-sector source diagnostics against GR/CAMB carrier tangents;
  - classifies the branch before any spectra or Planck trial;
  - current full two-sector diagnostic is `archive_fast` (`parallel_fraction ~= 0.998`, A_s dominated).
- two-sector carrier-degenerate archive:
  - archives the current full two-sector source as carrier-degenerate while preserving the structural history;
  - keeps spectra, Planck, promotion and retuning blocked.
- two-sector source construction audit:
  - decomposes plus, minus, symmetric, antisymmetric Z4, relative-isocurvature, projection-only, Weyl, Theta0 and Pi source components;
  - only a component with `parallel_fraction < 0.7` can open a separate diagnostic gate.
- projection parity preservation:
  - tests value, normal-derivative, jump, membrane-weighted and mixed observable projections;
  - current result: no tested projection preserves a non-carrier-tangent Z4-odd mode;
  - next required gate: minus-sector independent transfer, still no spectra or Planck.
- minus-sector independent transfer:
  - tests whether `T_minus` is only a best-fit rescaling of `T_plus`;
  - reports residual after amplitude fit, phase lag and effective transfer rank for density, velocity, shear, Weyl, Theta0, Pi and projection source;
  - current result: no component has independent transfer rank; all tested components are rank-1 / amplitude-rescaling dominated;
  - next required work is minus-sector microphysics, still no spectra or Planck.
- minus-sector microphysics:
  - specification gate requires non-amplitude physics and forbids free normalization knobs;
  - first diagnostic route is a fixed sound-speed/Jeans deformation, still pre-observational and not derived from the full action;
  - current result: it creates independent transfer rank in some channels but remains carrier-tangent, so no component is promotable.
- minus-sector shear/free-streaming:
  - declares `sigma_minus` and an `F_l_minus` hierarchy;
  - audits shear-only, free-streaming-only, Weyl anisotropic stress, Pi response and full channel before any spectra;
  - current result: independent rank appears in anisotropic/Pi/full channels, but all remain carrier-tangent.
- minus-sector thermal ratio:
  - tests a fixed `T_minus/T_plus` route through pressure, damping, decoupling proxy and Pi response;
  - current result: independent rank appears, but all channels remain carrier-tangent.
- minus-sector decoupling law:
  - blocks further progress until a derived minus-sector visibility, opacity, drag epoch or recombination law exists;
  - forbids free decoupling shifts and visibility patches.
- frozen two-sector CMB/Z4 branch:
  - status: `diagnostic_archived`;
  - reason: projection, slip/surface, sound-speed/Jeans, shear/free-streaming and thermal-ratio routes all remain carrier-tangent;
  - no additional CMB/Z4 physics, spectra, Planck trials, retuning or projection tweaks should be added on this branch;
  - reopen only with an action-derived minus-sector decoupling/recombination law.
- unique Z4 master-equation track:
  - next upstream direction after freezing patchwork CMB/Z4 branches;
  - goal: derive all slip, Doppler, Pi, minus-sector and projection observables from one generator `U_Z4`;
  - first required gates: `UniqueEquationMasterGate`, `MasterReconstructionGate`, `MasterConstraintConsistencyGate`, `MasterToObservableMapGate`, then `MasterCarrierTangentProjectionGate`;
  - no spectra or Planck until the master-derived signal passes carrier-tangent projection.
- unique equation master gate:
  - declares `L_Z4[U_Z4] = J_Z4`, Z4 parity, orbifold/boundary conditions and GR limit;
  - keeps `master_equation_solved = false` and forbids independent downstream slip/Doppler/Pi/minus-sector patches.
- master reconstruction gate:
  - declares reconstruction maps for metric, fluid, Doppler, Pi, Weyl and projection observables;
  - all maps remain `blocked_until_master_reconstruction` until derived from the same `U_Z4`;
  - independent downstream source patches remain forbidden.
- master constraint consistency gate:
  - declares Bianchi, plus/minus conservation, trace-free slip, Doppler/continuity, Pi-from-multipoles, Z4 projection and GR-limit checks;
  - all checks remain blocked until master reconstruction is actually derived.
- master-to-observable map gate:
  - declares `S_T,Z4`, `S_E,Z4`, `S_lens,Z4`, Doppler, Theta0, Pi, slip and minus-sector variables as functionals of the same `U_Z4`;
  - forbids independent downstream source patches.
- master carrier-tangent projection:
  - projects the single-`U_Z4` diagnostic signal against GR/CAMB carrier tangents;
  - current first ansatz result: `parallel_fraction = 0.9973`, dominant tangent `tau`;
  - keeps spectra and Planck blocked; current ansatz must be revised before source-level regeneration.
- master ansatz revision scan:
  - scans internal candidate shapes for the unique `U_Z4` generator;
  - this is not an observational fit and keeps lambda retuning, spectra and Planck blocked.
- master source-level regeneration:
  - selected internal ansatz: `localized_transition`, `parallel_fraction = 0.176`;
  - regenerates temperature, polarization, lensing, Doppler, Theta0, Pi, slip and minus-sector sources from the same `U_Z4`;
  - still no spectra or Planck.
- master constraint closure audit:
  - verifies source-level Doppler, Theta0, Pi, slip, lensing, temperature, polarization and minus-sector relations against the same `U_Z4`;
  - still no spectra or Planck.
- master source carrier-tangent replay:
  - replays the regenerated source-level payload against GR/CAMB carrier tangents;
  - current result: `parallel_fraction = 0.191`, passing both `<0.7` and `<0.5`;
  - still no spectra or Planck.
- master diagnostic spectra readiness:
  - allows internal diagnostic spectra generation after the carrier replay passes;
  - still forbids official Planck, likelihood evaluation, candidate promotion, retuning and nuisance refit.
- master diagnostic spectra generation:
  - writes internal GR and GR+master-Z4 diagnostic spectra;
  - replays carrier projection after serialization;
  - still forbids official Planck, likelihood evaluation, promotion and retuning.
- master diagnostic shape report:
  - reports TT/TE/EE ratio ranges, peak shifts and zero-count changes;
  - diagnostic-only, no likelihood evaluation.
- master pre-likelihood lock:
  - active while diagnostic spectra contain zero-crossing or large fractional shape artifacts;
  - current lock reason: TT/EE extra zero crossings and large fractional deviations.
- `profiled_planck_candidate = False` and `full_planck_validation = False`.
- residual diagnostics: TT peak shifts, TE zero shifts and EE peak shifts are
  zero in the tested high-l bands.
- This is still not a full Planck validation.
