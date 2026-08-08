# HESSIAN-GLOBAL-01 — déterminant relatif et front Quillen

Date : **8 août 2026**.

Ce document prolonge `hessian_global_01_reduced_green.md`. Le même Hessien
Candidate-A réduit possède maintenant une chaîne explicite allant de la chaleur
relative à un élément non nul de la ligne de déterminant, à un atlas local de
zêta, puis à une section compatible avec la métrique et la connexion de
Quillen du modèle cercle.

La certification Lean complète reste nécessaire avant de déclarer cette chaîne
formellement fermée.

## 1. Trace nucléaire intrinsèque

Une décomposition sommable en opérateurs de rang un donne une série scalaire,
mais cette série dépend a priori de la présentation. Le module

```text
P0EFTJanusProgramPIntrinsicNuclearTrace4D
```

introduit le certificat exact :

```lean
IntrinsicNuclearTraceData operator
```

Il contient une décomposition rang-un sommable et la preuve que toute autre
décomposition certifiée produit la même trace. La valeur canonique est :

```lean
intrinsicNuclearTrace
```

La spécialisation à la différence de chaleur réduite est :

```text
P0EFTJanusProgramPFiniteDefectReducedIntrinsicRelativeTrace4D
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedIntrinsicRelativeTrace4D
```

Le scalaire

```lean
globalCandidateAAugmentedReducedIntrinsicRelativeHeatTrace
```

ne dépend donc plus d'une présentation nucléaire choisie.

## 2. Déterminant par partie finie

Le module

```text
P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
```

demande exactement :

- un contre-terme de petit temps ;
- sa partie finie intégrée ;
- l'intégrabilité de la trace soustraite sur `(0,1]` ;
- l'intégrabilité logarithmique de la trace relative sur `(1,+∞)`.

La convention est :

\[
\log\det_{\mathrm{rel}}
=
-\operatorname{FP}\int_0^{\infty}
\operatorname{Tr}_{\mathrm{rel}}(t)\,\frac{dt}{t}.
\]

Le résultat est :

```lean
relativeHeatFinitePartDeterminant
```

avec un déterminant réel strictement positif et non nul. La spécialisation
Candidate-A est :

```text
P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
```

avec le gate :

```lean
global_candidateA_hessian_finitePart_determinant_gate
```

## 3. Schéma de soustraction et familles réelles

Le module

```text
P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D
```

prouve que deux contre-termes ayant la même partie finie renormalisée donnent
le même logarithme et le même déterminant.

La version paramétrée est :

```text
P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
```

Elle construit automatiquement :

```text
dérivée du déterminant positif
dérivée de sa norme carrée
positivité de la métrique déterminantielle
```

à partir de la dérivée du logarithme renormalisé.

## 4. Comparaison zêta et phase

Le module

```text
P0EFTJanusProgramPRelativeZetaComparison4D
```

prend une fonction zêta complexe régulière en zéro et demande :

```text
HasDerivAt zeta zetaPrime 0
logDet_finitePart = - Re(zetaPrime)
```

Il construit :

\[
\det_\zeta=\exp(-\zeta'(0)),
\]

puis démontre :

```text
det_zeta ≠ 0
‖det_zeta‖ = det_finitePart
```

La partie imaginaire de `zeta'(0)` fournit la phase unitaire. La version
familiale :

```text
P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
```

identifie point par point :

```text
norme du déterminant zêta = déterminant de partie finie
Re(connexion zêta) = - dérivée logarithmique de la métrique
phase normalisée de norme un
```

## 5. Connexion zêta

Pour une famille à un paramètre, le module

```text
P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
```

formalise :

\[
D(a)=\exp(-\zeta'_a(0)),
\qquad
D'(a)+\partial_a\zeta'_a(0)D(a)=0.
\]

Le raccord au coefficient de la connexion de Quillen du cercle est isolé dans :

```text
P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
```

Une égalité de coefficients et le clutching terminal suffisent alors à obtenir
le parallélisme, la compatibilité métrique au premier ordre et le recollement
des extrémités.

## 6. Cocycle et atlas général

Le modèle cercle ne suffit pas à traiter une famille nécessitant plusieurs
coupures spectrales ou plusieurs branches de zêta. Les modules

```text
P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D
```

construisent automatiquement, à partir des déterminants locaux non nuls :

```text
g_ij = D_j / D_i
g_ii = 1
g_jk g_ij = g_ik
g'_ij + A_j g_ij = g_ij A_i
```

Les sections locales sont parallèles et se recollent exactement par ce
cocycle. La spécialisation ancrée au déterminant Candidate-A est :

```text
P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D
```

avec :

```lean
global_candidateA_hessian_zeta_determinant_atlas_gate
```

## 7. Ancrage et section du modèle cercle

Le module

```text
P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D
```

place le déterminant complexe dans la fibre périodique réelle du modèle de
ligne de déterminant. Il prouve :

```text
ancrage ≠ 0
norme²_Quillen(ancrage) = det_finitePart²
```

Le module

```text
P0EFTJanusProgramPGlobalHessianQuillenParallelSection4D
```

transporte cet ancrage par la connexion plate existante. La section garde sa
norme, commence au déterminant Candidate-A et acquiert exactement l'holonomie
fermée unitaire au clutching terminal.

## 8. Fermeture Quillen conditionnelle

Les modules

```text
P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D
P0EFTJanusProgramPGlobalHessianQuillenCertificate4D
P0EFTJanusProgramPGlobalHessianQuillenClosure4D
```

assemblent la géométrie topologique du modèle cercle et la section analytique
Candidate-A. Le gate conditionnel est :

```lean
global_candidateA_hessian_quillen_global_closure_gate
```

Sa sortie contient la ligne de rang un, la métrique, la connexion plate,
l'holonomie unitaire, la section analytique non nulle et son clutching.

## 9. Façade finale cohérente

La façade

```text
P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D
```

interdit que le bridge cercle, l'atlas multi-charts et la famille de métrique
proviennent de déterminants zêta indépendants. Son entrée :

```lean
GlobalCandidateAHessianQuillenFinalFrontierData4D
```

contient des égalités explicites identifiant :

```text
le déterminant de l'atlas au déterminant du bridge
la famille zêta de la métrique à la famille zêta du bridge
```

Le gate terminal est :

```lean
global_candidateA_hessian_quillen_final_frontier_gate
```

Il fournit simultanément :

- la fermeture Quillen du modèle cercle ;
- le certificat d'atlas de ligne ;
- l'égalité de norme au point physique ;
- la variation de la métrique par la partie réelle de la connexion ;
- la phase unitaire à tout paramètre.

## 10. Frontière analytique réelle

Au-delà du certificat H10--H14 concret, les résultats encore substantiels pour
la géométrie Janus effective sont maintenant précisément :

```text
1. prouver l'unicité intrinsèque de la trace nucléaire relative pour la
   véritable famille d'opérateurs ;
2. construire les coefficients de chaleur et la partie finie uniformément en
   paramètre ;
3. produire la continuation de Mellin/zêta et sa différentiabilité familiale ;
4. identifier la 1-forme analytique obtenue avec la connexion de
   Bismut--Freed, puis vérifier les égalités de cohérence exigées par la façade
   finale.
```

Les cocycles, l'atlas, les lois de jauge, la métrique, la phase, le clutching et
l'assemblage terminal ne sont plus des tâches séparées : ils sont produits par
les gates dès que ces entrées analytiques sont construites.
