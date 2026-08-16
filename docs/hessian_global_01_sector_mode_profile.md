# HESSIAN-GLOBAL-01 — assemblage sectoriel des zéro-modes

Date : **9 août 2026**.

La frontière stable de H10–H14 n’utilise plus nécessairement un type fini
opaque `ZeroMode`. Les modes peuvent maintenant être donnés séparément dans les
cinq secteurs physiques D10-free :

```text
metricDiffeomorphism
abelianGauge
primitiveSpinCMatter
longitudinalLL
boundaryFiniteBV
```

## 1. Somme dépendante des secteurs

Le paquet

```lean
CandidateASectorModeTypes
```

contient un type fini `Mode sector` pour chaque secteur. Le type global est
construit automatiquement :

```lean
Σ sector, Mode sector.
```

Sa classification physique est la première projection. Il n’est donc plus
nécessaire de fournir séparément une fonction `sectorOf` sur un type global
fabriqué à la main.

## 2. Orthogonalité assemblée

Le paquet

```lean
CandidateASectorOrthogonalModeFamily
```

contient :

- les vecteurs de chaque secteur ;
- leur non-nullité ;
- l’orthogonalité interne de chaque famille ;
- une unique orthogonalité entre secteurs distincts.

Les théorèmes génériques en déduisent automatiquement la non-nullité et
l’orthogonalité pairwise de toute la somme dépendante.

## 3. Action Candidate-A et Gårding stable

La structure

```lean
GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
```

ajoute :

- l’invariance locale de la véritable action augmentée selon chaque mode ;
- la Gårding du représentant principal BRST–SpinC–LL ;
- la petitesse stricte de la forme physique H11 ;
- la stationnarité LL.

Elle construit directement le paquet stable déjà consommé par :

```lean
global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate.
```

Aucune nouvelle action, aucun opérateur auxiliaire et aucune nouvelle
complétion ne sont introduits.

## 4. Multiplicités exactes

Pour chaque secteur, le fibre de la classification est équivalent à son type
local :

\[
\{m\mid \operatorname{sector}(m)=s\}\simeq \operatorname{Mode}(s).
\]

Par conséquent :

\[
\dim\ker H
=
\sum_s \#\operatorname{Mode}(s).
\]

Le module

```text
P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D
```

permet de choisir directement cinq nombres naturels et d’utiliser
`Fin n` comme type de coordonnées de chaque secteur.

## 5. Façades terminales

La façade générale est :

```lean
global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_frontier_gate
```

La façade numérique est :

```lean
global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_frontier_gate
```

Elles retournent la fermeture H10–H14 existante ainsi que le comptage sectoriel
exact du noyau réel.

## 6. Travail physique restant

Cette réduction ne prétend pas inventer les générateurs. Il reste à fournir :

```text
1. les vecteurs concrets dans chacun des cinq secteurs ;
2. l’invariance de l’action Candidate-A selon ces vecteurs ;
3. la non-nullité et l’orthogonalité sectorielle ;
4. la Gårding principale et la petitesse de la forme physique ;
5. la borne du cœur dense vers le véritable chart physique.
```

La branche reste en brouillon tant que la chaîne complète n’est pas certifiée
par Lean.
