# HESSIAN-GLOBAL-01 — frontière analytique réduite

Date du lot : **7 août 2026**.

Ce document décrit l'état d'implémentation après la réduction constructive de
H13, H11 et H12. Il complète la carte de fermeture historique sans prétendre
que les nouveaux fichiers sont certifiés par Lean : conformément à la décision
du projet, leur implémentation a été poursuivie sans attendre le build complet.

## Résultat structurel

Le certificat terminal H14 existe déjà :

```lean
global_candidateA_hessian_closure_gate
```

La route constructive privilégiée est désormais :

```lean
global_candidateA_hessian_minimalPhysical_bounded_closure_gate
```

exposée par :

```text
P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
```

Cette route ne demande plus directement :

- une égalité de Hessien matière–LL fournie comme champ ;
- une forme bornée arbitraire représentant les sept blocs physiques ;
- une hypothèse Fredholm globale ;
- une équivalence supposée entre deux complétions concurrentes.

## Les quatre paquets analytiques restants

### A. SpinC lisse dans le graphe maximal

Façade :

```text
P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
```

Les coefficients Fourier non pondérés sont maintenant canoniques : ils sont
obtenus, secteur par secteur, par l'inverse de
`primitiveSpinCGeometricSignedDiracModeUnitary`, puis assemblés sur
`Sector × PrimitiveSpinCGeometricSignedMode`.

Les compatibilités avec tout le cœur Fourier fini et l'injectivité sont
dérivées. La voie géométrique restante porte sur :

```lean
ProgramPPrimitiveSpinCSmoothMaximalDomainData4D
```

c'est-à-dire :

1. toute section primitive lisse appartient au domaine maximal de `2D + m²` ;
2. l'opérateur maximal appliqué à cette section redonne l'inclusion L² de la
   véritable expression différentielle lisse.

Il reste ensuite l'identité same-action de la paire complétée, portée par :

```lean
ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D
```

Ces deux objets construisent automatiquement la réalisation lisse dans le
graphe maximal.

### B. Famille Candidate-A locale sur le vrai tangent physique minimal

Le modèle du chart est fixé à :

```lean
GlobalMinimalPhysicalFieldTangent
```

Il est D10-free et le pont du tangent vers le modèle du chart est l'identité.
L'injectivité et la densité de ce pont ne sont donc plus des obligations.

Le paquet réduit est :

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
```

Il contient :

- un ouvert admissible contenant zéro ;
- la vraie famille de données Candidate-A sur cet ouvert ;
- la régularité `C²` des neuf blocs ;
- deux bornes de norme de graphe, matière et LL ;
- l'identité du bloc matière avec constante + action quadratique SpinC ;
- l'identité du bloc LL avec constante + action quadratique LL complet.

La compatibilité de ces projections avec le cœur diagonal n'est plus un champ :
elle est dérivée dans
`P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D`
à partir des injections de slots typées déjà présentes.

### C. Une seule borne pour les sept blocs physiques

La forme algébrique sur le cœur dense est canonique : c'est le vrai Hessien
local des sept blocs physiques, tiré sur le cœur diagonal existant.

Le seul paquet H11 restant est :

```lean
GlobalCandidateASevenPhysicalCoreBound4D
```

avec une estimation de la forme :

```text
‖B(x,y)‖ ≤ C ‖ι(x)‖ ‖ι(y)‖.
```

La gate

```text
P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
```

utilise `LinearMap.extendOfNorm` dans les deux variables et construit
canoniquement l'unique forme bilinéaire continue sur la complétion Hilbert
commune. L'accord avec le cœur lisse dense et la symétrie sont dérivés.

### D. Paramétrix augmenté à défaut fini

Le paquet H12 restant est :

```lean
GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
```

Il porte :

```text
QH = I - K,
HQ = I - C,
CH = 0,
range(K) et range(C) de dimension finie,
stationnarité LL.
```

La gate prouve alors :

```text
range(H) = ker(C),
```

ce qui donne l'image fermée. Elle plonge aussi `ker(H)` dans `range(K)`, donc
le noyau est de dimension finie. Le caractère Fredholm, le cokernel fini et
l'indice zéro sont ensuite dérivés des gates auto-adjointes existantes.

## Chaîne terminale

Une fois A, B, C et D fournis, la chaîne est mécanique :

```text
SpinC maximal graph
  → chart minimal H13
  → mismatch matière–LL = 0
  → extension H11 des sept blocs
  → opérateur augmenté sur le domaine commun
  → paramétrix H12
  → Fredholm + indice zéro
  → certificat H14.
```

Aucune étape H15 n'est prévue.

## État de confiance

- **Implémentation structurelle :** poussée sur `dev-branch`.
- **Réduction des résidus :** effectuée jusqu'aux quatre paquets ci-dessus.
- **Validation Lean des nouveaux fichiers :** non effectuée / non garantie.
- **Ticket mathématique terminal :** pas encore `DONE`, car les quatre témoins
  analytiques concrets ne sont pas encore construits.
