# Plan De Validation Scientifique

## Objectif

Construire un banc d'essai qui compare Janus a des modeles concurrents sur des donnees publiques, avec les memes metriques statistiques.

Le critere de succes n'est pas "Janus explique X", mais :

- Janus predit X avec moins d'hypotheses ou moins de parametres ;
- Janus ajuste X sans degrader Y ;
- Janus produit une prediction discriminante verifiable.

## Phase 1 - Expansion Cosmique

### Modeles minimum

1. Lambda-CDM plat.
2. CPL `w0-wa`.
3. Loi d'expansion Janus exacte parametree par `u0`.

### Observables

- `H(z) / H0`
- distance comobile `D_C(z)`
- distance luminosite `d_L(z)`
- module de distance `mu(z)`
- BAO compresse : `D_M / r_d`, `D_H / r_d`, `D_V / r_d`

### Donnees

- DESI DR2 BAO.
- Pantheon+.
- Union3 ou DES-SN5YR en second temps.
- Planck/ACT sous forme de contraintes compressees en garde-fou.

### Metriques

- chi2.
- AIC / BIC.
- residus par tranche de redshift.
- comparaison a nombre de parametres comparable.

## Phase 2 - Galaxies

### Modeles

- Newtonien baryonique.
- halo NFW / Burkert.
- solution Vlasov-Poisson de Petit, D'Agostini & Monnet.

### Donnees

- SPARC.
- courbes de rotation HI.
- masses stellaires avec incertitudes.

### Questions

- La solution reproduit-elle les courbes plates sans halo ad hoc ?
- Quels parametres sont universels et lesquels sont ajustes galaxie par galaxie ?
- Le modele predit-il aussi les relations de type Tully-Fisher ?

## Phase 3 - Lentillage Et Grandes Structures

Cette phase est indispensable si Janus pretend remplacer la matiere noire.

Tests :

- lentillage faible ;
- amas de galaxies ;
- Bullet Cluster ;
- `S8` ;
- spectre de puissance de la matiere.

## Phase 4 - Objets Compacts

Tests possibles :

- rapport de temperature de brillance EHT ;
- taille de l'ombre / anneau ;
- dynamique des etoiles proches de Sgr A* ;
- anneaux quasi-normaux et ondes gravitationnelles.

Cette phase demande une formulation observationnelle tres precise, sinon elle restera argumentative.

## Regles De Travail

1. Toujours separer articles publies, preprints, pages auteur et donnees observationnelles.
2. Toute equation utilisee en code doit pointer vers une source.
3. Tout parametre libre doit etre liste.
4. Une amelioration de fit doit etre penalisee par le nombre de parametres.
5. Une prediction doit etre ecrite avant de regarder les donnees de test quand c'est possible.

## Prochaine Etape Concrete

Implementer le fit DESI DR2 + Pantheon+ :

1. telecharger les donnees publiques ;
2. ecrire les likelihoods ;
3. fitter Lambda-CDM, CPL et Janus ;
4. produire une table comparative ;
5. identifier les zones de redshift ou Janus diverge le plus.
