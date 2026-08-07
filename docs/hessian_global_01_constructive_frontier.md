# HESSIAN-GLOBAL-01 — frontière constructive après H14

Ce document décrit la frontière d'implémentation constructive ajoutée après
l'assembleur `P0EFTJanusProgramPGlobalHessianClosure4D`. Il ne remplace pas la
carte autoritative `hessian_global_01_closure_map.md`; il précise comment
construire concrètement les trois témoins encore paramétriques de H14.

> État de validation : les gates ci-dessous ont été ajoutées sur `dev-branch`
> sans attendre une compilation Lean complète, conformément à la décision de
> poursuite prise le 7 août 2026. Elles ne doivent donc pas être décrites comme
> certifiées par le noyau avant un build ultérieur.

## 1. H13 n'attend plus une égalité de Hessien fournie directement

La gate

```text
P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
```

remplace le contrat direct

```lean
ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
```

par deux identités au niveau des actions du vrai chart local :

```text
bloc matière local = constante + action quadratique du graphe SpinC
bloc LL local      = constante + action quadratique du graphe LL complet
```

Les secondes dérivées de Fréchet sont ensuite calculées automatiquement. Le
pont H13 original est construit par

```lean
programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
```

et le mismatch matière–LL s'annule sans hypothèse supplémentaire.

## 2. Le chart est fixé au tangent physique minimal D10-free

La gate

```text
P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
```

choisit comme modèle du chart exactement

```lean
GlobalMinimalPhysicalFieldTangent
```

et non un espace abstrait supplémentaire. Le `chartBridge.tangentAnalysis` est
l'identité ; son injectivité et sa densité sont donc automatiques.

Le constructeur attend uniquement :

- un ouvert admissible contenant zéro ;
- la famille réelle de données Candidate-A sur cet ouvert ;
- les preuves `C²` des neuf blocs déjà nommés ;
- les projections continues vers les graphes matière et LL ;
- les deux identités d'actions quadratiques.

La gate

```text
P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
```

réduit encore les projections à :

1. une réalisation de toute section SpinC primitive lisse dans le domaine
   maximal du graphe exact ;
2. une borne de norme de graphe pour cette réalisation composée avec le
   tangent physique ;
3. une borne de norme de graphe pour les trois slots LL, dont l'application
   algébrique est déjà canonique ;
4. les identités de compatibilité avec le cœur diagonal fini/lisse existant.

La gate

```text
P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
```

assemble ces objets et produit directement le certificat H13.

## 3. H11 possède deux voies constructives

### 3.1 Voie bloc par bloc

```text
P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
```

sépare les sept blocs physiques :

1. interaction Candidate-A ;
2. GHY/Robin ;
3. Einstein–Hilbert plus ;
4. Einstein–Hilbert moins ;
5. Maxwell plus ;
6. Maxwell moins ;
7. bord fini/null-BV.

Chaque bloc reçoit sa propre forme bilinéaire bornée et son accord exact sur
le cœur lisse dense. Leur somme construit automatiquement

```lean
GlobalCandidateASevenPhysicalCommonDomainExtension4D
```

et donc le certificat H11.

### 3.2 Voie chart Hilbert commun

```text
P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
```

évite les sept estimations séparées lorsqu'une équivalence linéaire continue
est disponible entre le modèle du chart local et l'unique complétion Hilbert
BRST–SpinC–LL existante. Le vrai Hessien local des sept blocs est alors
transporté directement ; sa symétrie vient du caractère `C²` de la même action.

Cette voie réduit H11 à une seule équivalence de chart et à son accord avec le
cœur diagonal dense.

## 4. H12 est réduit à un paramétrix à défaut fini

```text
P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
```

remplace les deux conclusions à prouver séparément

```text
image fermée
noyau de dimension finie
```

par un paramétrix borné `Q` et deux défauts finis `K` et `C` :

```text
Q H = I - K
H Q = I - C
C H = 0
```

La gate prouve alors :

```text
range(H) = ker(C)
```

et donc la fermeture de l'image. Elle plonge aussi `ker(H)` dans `range(K)`,
qui est de dimension finie. Le certificat d'estimations H12 est construit par

```lean
globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix
```

puis le caractère Fredholm et l'indice zéro suivent des gates existantes.

## 5. Deux assembleurs H14 constructifs

### Route bloc par bloc

```text
P0EFTJanusProgramPGlobalHessianConstructiveClosure4D
```

attend :

- le chart quadratique H13 ;
- les sept extensions H11 ;
- le paramétrix H12.

### Route chart Hilbert commun

```text
P0EFTJanusProgramPGlobalHessianHilbertChartClosure4D
```

attend :

- le chart quadratique H13 ;
- l'équivalence avec le domaine Hilbert commun ;
- le paramétrix H12.

Les deux routes sont exposées par :

```text
P0EFTJanusProgramPGlobalHessianConstructiveFrontier4D
```

## 6. Travail mathématique restant après cette réduction

Le prochain travail n'est plus de dessiner de nouvelles interfaces globales.
Il consiste à produire les objets suivants :

1. **Réalisation SpinC lisse dans le graphe maximal**
   - montrer que toute section primitive lisse appartient au domaine maximal
     de `2D + m²` ;
   - identifier l'action lisse et l'action de graphe ;
   - obtenir la borne de norme de graphe.

2. **Famille locale réelle sur le tangent minimal**
   - appliquer les variations métriques, jauge, LL, déplacement normal et
     SpinC à la configuration de base ;
   - prouver que les données restent dans l'ouvert admissible ;
   - établir `C²` pour les neuf blocs ;
   - vérifier les deux identités d'actions matière et LL.

3. **H11**
   - soit prouver les sept bornes bloc par bloc ;
   - soit construire l'équivalence du chart physique avec le domaine Hilbert
     commun et son accord sur le cœur dense.

4. **H12**
   - construire le paramétrix augmenté à partir des Green/paramétrix déjà
     disponibles pour les blocs diagonaux ;
   - identifier les deux défauts spectraux finis ;
   - vérifier la stationnarité LL sur la strate terminale.

Une fois ces objets fournis, aucune nouvelle étape H15 n'est nécessaire : le
certificat H14 existant est construit directement.
