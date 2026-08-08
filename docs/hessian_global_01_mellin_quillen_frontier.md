# HESSIAN-GLOBAL-01 — route Mellin vers la ligne de Quillen

Date : **8 août 2026**.

Ce document complète :

```text
docs/hessian_global_01_zeta_quillen_frontier.md
```

La carte principale décrit aussi les couches de trace relative, déterminant de
Fredholm relatif et comparaison des renormalisations. La présente note isole la
route analytique la plus stricte vers la zêta et la connexion de Quillen.

## 1. La zêta doit provenir de la chaleur

Le module

```text
P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
```

définit le noyau :

\[
K_s(t)=t^{s-1}\operatorname{Tr}_{\mathrm{rel}}(t),
\]

la transformée de Mellin :

\[
M(s)=\int_0^\infty K_s(t)\,dt,
\]

et la candidate zêta normalisée :

\[
\zeta_{\mathrm{heat}}(s)=\Gamma(s)^{-1}M(s).
\]

Le certificat

```lean
RelativeHeatMellinZetaContinuationData
```

contient :

```text
un demi-plan Re(s) > sigma ;
l'intégrabilité de K_s dans ce demi-plan ;
l'égalité de zeta avec Gamma(s)^-1 M(s) ;
la continuation différentiable jusqu'à zéro ;
l'égalité -Re(zeta'(0)) = log(det_finitePart).
```

Il se convertit automatiquement en l'ancien :

```lean
RelativeZetaComparisonData
```

mais l'inverse n'est pas supposé : un germe complexe sans représentation de
Mellin n'est plus une entrée suffisante pour la route préférée.

Gate :

```lean
relative_heat_mellin_zeta_continuation_gate
```

## 2. Contrôle uniforme dans la famille

Le module

```text
P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
```

regroupe une continuation de Mellin à chaque paramètre et demande la
différentiabilité paramétrique de `zetaPrimeAtZero`.

Il construit :

```text
la famille de déterminants complexes ;
la comparaison avec la métrique de partie finie ;
la variation métrique par la partie réelle de la connexion ;
la phase unitaire de l'asymétrie spectrale.
```

Gate :

```lean
relative_heat_mellin_zeta_family_gate
```

## 3. Route Candidate-A sans doublon de données

Le module

```text
P0EFTJanusProgramPGlobalHessianQuillenMellinFrontier4D
```

part de :

```text
un déterminant Candidate-A au point physique ;
une unique famille de Mellin ;
un bridge vers la connexion du cercle ;
un atlas local dont le chart de base est cette famille.
```

Il construit automatiquement :

```text
GlobalCandidateAHessianQuillenFamilyBridgeData4D
GlobalCandidateAHessianZetaDeterminantAtlasData4D
RelativeZetaFinitePartFamilyComparisonData
GlobalCandidateAHessianQuillenFinalFrontierData4D
```

Ainsi la famille zêta, la métrique et le bridge ne peuvent pas provenir de trois
choix indépendants.

Gate :

```lean
global_candidateA_hessian_quillen_mellin_frontier_gate
```

## 4. Façade publique

La façade :

```text
P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D
```

pointe désormais vers la route Mellin. Les anciennes routes restent disponibles
comme adaptateurs :

```lean
global_candidateA_hessian_zeta_quillen_coherent_gate
global_candidateA_hessian_zeta_determinant_only_gate
```

## 5. Ce qui reste à démontrer concrètement

La structure aval n'est plus le verrou. Les résultats analytiques restants sont :

```text
1. unicité intrinsèque de la trace nucléaire pour la vraie chaleur relative ;
2. asymptotique de petit temps et contre-termes uniformes ;
3. intégrabilité de Mellin dans un demi-plan commun ;
4. continuation jusqu'à zéro et différentiabilité dans le paramètre ;
5. égalité de la 1-forme obtenue avec la connexion de Bismut–Freed ;
6. identification du clutching physique avec le clutching du modèle cercle.
```

Une fois ces données fournies, le cocycle, l'atlas, la métrique, la phase, la
section non nulle et le certificat global de Quillen sont produits par les
gates existants.
