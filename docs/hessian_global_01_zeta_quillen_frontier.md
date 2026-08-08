# HESSIAN-GLOBAL-01 — déterminant relatif et front Quillen

Date : **8 août 2026**.

Ce document prolonge `hessian_global_01_reduced_green.md`. Le même Hessien
Candidate-A réduit possède maintenant une chaîne explicite allant de la chaleur
relative à un élément non nul de la ligne de déterminant, puis à une section
parallèle du modèle de Quillen sur le cercle.

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

Il contient :

1. une décomposition rang-un sommable ;
2. la preuve que toute autre décomposition certifiée produit la même trace.

La valeur canonique est :

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

étend la trace à la demi-droite réelle et demande exactement :

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

avec :

```text
0 < determinant
determinant ≠ 0
log determinant = partie finie logarithmique
```

La spécialisation Candidate-A est :

```text
P0EFTJanusProgramPGlobalHessianFinitePartDeterminant4D
```

et le gate :

```lean
global_candidateA_hessian_finitePart_determinant_gate
```

## 3. Indépendance du schéma de soustraction

Deux contre-termes définissent le même déterminant lorsque leurs parties finies
renormalisées de petit temps coïncident. Cette équivalence est isolée dans :

```text
P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D
```

avec :

```lean
RelativeHeatFinitePartSchemeAgreement
relative_heat_finite_part_scheme_independence_gate
```

Elle donne l'égalité des logarithmes, des déterminants positifs et des
déterminants complexes à phase fixée.

## 4. Comparaison zêta

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

La partie imaginaire de `zeta'(0)` produit automatiquement une phase unitaire.
La spécialisation globale est :

```text
P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
```

avec :

```lean
global_candidateA_hessian_zeta_determinant_gate
```

## 5. Ancrage dans la ligne de Quillen

Le module

```text
P0EFTJanusProgramPGlobalHessianQuillenMetricAnchor4D
```

place le déterminant complexe dans la fibre périodique réelle du modèle de
ligne de déterminant déjà construit :

```lean
globalCandidateAHessianQuillenMetricAnchor
```

Il prouve :

```text
ancrage ≠ 0
norme²_Quillen(ancrage) = det_finitePart²
```

Le module

```text
P0EFTJanusProgramPGlobalHessianQuillenParallelSection4D
```

transporte ensuite cet ancrage par la connexion plate du modèle cercle. La
section obtenue :

- garde la même norme de Quillen ;
- commence au déterminant Candidate-A ;
- acquiert exactement l'holonomie fermée unitaire au clutching terminal.

## 6. Formule de connexion du déterminant zêta

Pour une famille à un paramètre, le module

```text
P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
```

formalise :

\[
D(a)=\exp(-\zeta'_a(0)),
\qquad
D'(a)+\partial_a\zeta'_a(0)\,D(a)=0.
\]

Le coefficient de connexion est donc :

```lean
relativeZetaConnectionCoefficient
```

Le raccord au coefficient de la connexion de Quillen du cercle est isolé dans :

```text
P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
```

Une égalité de 1-formes et le clutching terminal suffisent alors à obtenir :

```text
section parallèle
variation première de la métrique nulle
compatibilité de clutching
```

## 7. Certificat Quillen global conditionnel

Les modules terminaux sont :

```text
P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D
P0EFTJanusProgramPGlobalHessianQuillenCertificate4D
P0EFTJanusProgramPGlobalHessianZetaQuillenFrontier4D
```

Le gate final conditionnel est :

```lean
global_candidateA_hessian_quillen_certificate_gate
```

Sa sortie contient :

- un déterminant zêta global non nul au point physique ;
- une section partout non nulle de la ligne clutched ;
- l'équation de parallélisme ;
- la variation métrique nulle ;
- le clutching exact aux extrémités.

## 8. Frontière analytique réelle

Au-delà du certificat H10--H14 concret, trois paquets déterminantiels restent à
construire pour la géométrie Janus effective :

```text
1. unicité intrinsèque de la trace nucléaire relative à tout temps positif ;
2. asymptotique petit temps et partie finie, uniforme dans la famille ;
3. continuation de Mellin/zêta et identification de sa 1-forme avec
   Bismut--Freed.
```

Le premier est un théorème de trace nucléaire. Le deuxième est un calcul local
de coefficients de chaleur. Le troisième est le théorème de famille qui
transforme le modèle cercle déjà construit en véritable ligne de Quillen du
Hessien global Candidate-A.
