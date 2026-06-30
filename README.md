# Janus Formal Scaffold

Depot de travail pour formaliser et tester un pipeline Janus autour de :

- modules Lean (`JanusFormal/`) ;
- scripts Python d'audit et de generation de rapports (`scripts/`) ;
- tests unitaires (`tests/`) ;
- donnees traitees minimales (`data/processed/`) ;
- documentation scientifique et cartes de sources (`docs/`, `formal/`).

## Etat actuel

Le verrou global final est ferme dans le scaffold interne :

- `aps_global_theorem_proved = True`
- `orbifold_global_theorem_proved = True`
- `full_cosmology_prediction_ready_no_fit = True`

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
