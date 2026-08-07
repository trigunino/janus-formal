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
global_candidateA_hessian_maximalDomain_bounded_closure_gate
```

exposée par :

```text
P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
```

Cette route ne demande plus directement :

- une égalité de Hessien matière–LL fournie comme champ ;
- un paquet de coefficients SpinC pondérés choisi séparément ;
- une hypothèse d'appartenance au domaine maximal SpinC ;
- un témoin same-action SpinC distinct ;
- une forme bornée arbitraire représentant les sept blocs physiques ;
- une hypothèse Fredholm globale ;
- une équivalence supposée entre deux complétions concurrentes.

## Les quatre paquets analytiques restants

### A. Une identité de Green pour le Dirac SpinC lisse

Façade :

```text
P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
```

Le seul témoin SpinC conservé par la frontière terminale est maintenant :

```lean
ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D
```

Il exprime, sur le véritable cœur des sections lisses du fibré SpinC primitif,
l'identité formelle d'adjonction du Dirac premier ordre :

```text
⟨ψ, Dφ⟩ = ⟨Dψ, φ⟩.
```

Ce témoin est indépendant du paramètre de masse. Les gates en déduisent
mécaniquement :

1. la symétrie de `2D + m²` pour tout `m² ∈ ℝ` ;
2. l'identification de chaque coefficient Fourier canonique avec le pairing
   contre l'eigensection lisse normalisée correspondante ;
3. la relation multiplicateur exacte sur tous les modes signés ;
4. l'appartenance de toute section lisse au domaine maximal ;
5. l'accord de l'opérateur maximal avec la véritable expression
   différentielle lisse ;
6. le vecteur de coefficients pondérés dans `ℓ²` ;
7. l'identité de Parseval à deux secteurs ;
8. l'accord same-action entre l'action lisse intégrée et l'action quadratique
   du graphe maximal.

La voie préférée est exposée sous :

```lean
primitive_spinC_smooth_graph_of_dirac_formal_symmetry
```

Les anciennes voies par coefficients pondérés ou domaine maximal déjà
construit restent disponibles comme adaptateurs de compatibilité.

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
canoniquement la forme bilinéaire continue sur la complétion Hilbert commune.
L'accord avec le cœur lisse dense et la symétrie sont dérivés.

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
Green Dirac SpinC
  → symétrie de 2D + m²
  → coefficients signés + domaine maximal + same-action
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

- **Implémentation structurelle :** préparée sur la branche de contribution.
- **Réduction des résidus :** effectuée jusqu'aux quatre paquets ci-dessus.
- **Validation Lean des nouveaux fichiers :** non effectuée / non garantie.
- **Ticket mathématique terminal :** pas encore `DONE`, car les quatre témoins
  analytiques concrets ne sont pas encore construits.
