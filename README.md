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
- `aps_global_theorem_proved = True`
- `orbifold_global_theorem_proved = True`
- `holst_geometric_lock_closed = True`
- `late_time_growth_branch_observationally_viable = True`
- `cmb_bao_monommetric_camb_hooks_sufficient = False`
- `bi_sector_boltzmann_backend_required = Open`
- `full_observational_cosmology_no_fit_ready = False`

Les verrous mathematiques internes formalises sous Lean restent fermes. Ce qui reste
ouvert n'est pas la topologie APS/orbifold, mais la validation observationnelle
complete avec un backend cosmologique capable de representer correctement le
caractere bi-secteur Janus-orbifold.

Les derniers gates CMB/BAO montrent que les hooks mono-metriques CAMB sont utiles
comme diagnostics EFT, mais insuffisants comme preuve finale du modele complet.

Point d'entree principal :

- `JanusFormal/P0EFTGlobalTopologyMasterLock.lean`
- `scripts/build_p0_eft_run9_master_lock.py`

## Validation rapide

```bash
python -m unittest discover -s tests -p "test_p0_eft_run*.py"
lake build JanusFormal.P0EFTGlobalTopologyMasterLock
```

Validation plus large :

```bash
lake build
```

## Organisation utile

- `JanusFormal.lean` importe l'ensemble des modules Lean.
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
