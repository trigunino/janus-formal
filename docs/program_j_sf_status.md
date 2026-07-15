# J-SF — analogue superfluide à deux composantes

## Portée

Programme analogue uniquement. Il peut reproduire des modes commun/relatif,
une interface et une conversion de modes; il ne dérive ni la gravité Janus ni
la nature microscopique de l'Univers.

## SF01 — fond homogène

Pour deux densités `n1,n2` et les couplages symétriques `g,g12`, l'énergie
d'interaction se décompose exactement en canaux commun et relatif :

```text
4 E = (g+g12)(n1+n2)^2 + (g-g12)(n1-n2)^2.
```

Le cône strict `g>|g12|` rend les deux canaux positifs. Le code rejette les
entrées hors de ce cône pour la relaxation homogène.

## SF02 — fond et longueurs

Le solveur d'imaginary time à deux Gross-Pitaevskii relaxe un fond périodique
miscible. Les longueurs de cicatrisation commune et relative sont calculées à
partir des vitesses acoustiques. Une vraie interface immiscible appartient au
cône opposé `g12>g`; elle ne doit pas être confondue avec le fond stable utilisé
pour Bogoliubov.

## SF03 — Bogoliubov

Avec `epsilon_k=k²/(2m)`, les deux branches sont

```text
omega_common²   = epsilon_k [epsilon_k + 2 n (g+g12)],
omega_relative² = epsilon_k [epsilon_k + 2 n (g-g12)].
```

Sur le cône stable elles sont réelles et positives. Pour `g12>g`, la branche
relative devient négative à longue longueur d'onde : c'est l'instabilité de
démixtion, pas une masse gravitationnelle négative.

## SF04 — diffusion

SF04 a été activé car SF01-SF03 possèdent un fond stable. Une marche d'impédance
acoustique vérifie exactement `R+T=1`; l'impédance adaptée donne `R=0`. Une
probabilité générique de conversion entre les deux modes est également bornée.

## Limites de l'analogie

| Analogue | Janus non démontré |
| --- | --- |
| composantes 1/2 | feuillets métriques plus/minus |
| mode commun/relatif | gravitons sans masse/massif |
| interface condensat | gorge Sigma |
| métrique acoustique | équations d'Einstein bimétriques |

La structure Lean `AnalogueDictionary` distingue formellement analogie
cinématique et équivalence fondamentale. Cette dernière reste ouverte.

## Cibles

```text
JanusFormal.Branches.JanusSuperfluidAnalogue
src/janus_lab/two_component_superfluid.py
tests/test_two_component_superfluid.py
```
