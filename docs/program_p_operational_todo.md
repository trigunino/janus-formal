# Programme P — TODO opérationnelle distribuable aux LLM

Date de référence : 2026-07-19.

## 1. Rôle de ce document

Ce fichier est la file de travail courte de Programme P. Le registre détaillé
`docs/program_p_exhaustive_todo.md` reste le journal historique des preuves et
des sous-résultats.

État vérifié du registre historique : **1038/1146**, soit **90,58 %**, avec
**108 cases ouvertes**. Ce pourcentage n'est plus utilisé comme mesure de
fermeture globale : le nombre de cases ouvertes n'a pas diminué pendant
l'ajout de centaines de microlemmes.

La fermeture globale est mesurée uniquement par les **14 portes terminales**
de la section 7. État actuel : **0/14**. Une preuve locale, pointwise,
finite-mode, réduite ou conditionnelle ne ferme jamais une porte globale.

En cas de contradiction entre prose et code, le type exact du théorème Lean
compilé fait autorité.

## 2. Consigne à donner à chaque LLM

Copier ce bloc avec l'identifiant d'une seule carte :

> Travaille dans `C:\Users\alzie\Documents\Janus` sur la carte `<ID>` de
> `docs/program_p_operational_todo.md`. Ne traite aucune autre carte. Cherche
> d'abord dans tout le dépôt avec `rg`, puis lis uniquement les modules cités
> et leurs dépendances directes. Réutilise les théorèmes existants. Crée au
> plus un petit gate Lean, compile-le immédiatement, puis intègre-le seulement
> s'il compile. Aucun Git, `sorry`, `axiom`, `admit`, placeholder, certificat
> par simples champs `Prop`, ni hypothèse contenant la conclusion recherchée.
> Ne transforme jamais un résultat local, réduit, finite-mode, produit ou
> conditionnel en résultat global. Utilise `apply_patch` pour toute édition.
> Supprime les fichiers temporaires. Dans ton bilan, donne : énoncé réellement
> prouvé, portée, fichiers modifiés, commandes/tests, et porte terminale fermée
> — ou écris explicitement « aucune ».

Coordination dans un workspace partagé :

- plusieurs agents peuvent travailler en parallèle sur des gates distincts ;
- un seul intégrateur à la fois modifie la façade, l'audit et les deux TODO ;
- un agent ne coche jamais une carte qu'il n'a pas lui-même compilée ;
- les lemmes intermédiaires sont inscrits comme preuves d'appui sous la carte,
  sans créer de nouvelle unité de progression.

Première vague possible pour dix LLM : attribuer les dix cartes de la section
4, une par agent. Chaque agent construit et compile uniquement son gate ; un
coordinateur intègre ensuite les gates verts, un par un, dans la façade et
l'audit. Les cartes de la section 5 viennent seulement après cette vague ou
après satisfaction de leur dépendance explicite.

## 3. Portées et validation

Portées autorisées : `GLOBAL`, `SECTORIEL`, `RÉDUIT`, `FINITE-MODE`,
`POINTWISE`, `CONDITIONNEL`, `DOCUMENTAIRE`.

États autorisés : `READY`, `DÉPENDANCE`, `BLOQUÉ-PHYSIQUE`, `DONE`.

Une carte Lean est `DONE` seulement si :

1. le théorème prouve exactement le résultat annoncé avec sa portée dans le
   type ou dans le nom ;
2. ses hypothèses sont mathématiques et ne reformulent pas la conclusion ;
3. le gate focalisé compile ;
4. le gate est importé par la façade Programme P ;
5. l'audit contrôle le module et le théorème exacts ;
6. la façade compile et l'audit est vert ;
7. `#print axioms` ne révèle aucun axiome métier ajouté ;
8. aucun fichier temporaire ou module non compilé ne reste.

Commandes finales obligatoires :

```powershell
lake build <Nom.Du.Module>
lake env lean JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean
C:\Users\alzie\AppData\Local\Programs\Python\Python314\python.exe scripts/audit_janus_program_p.py
```

## 4. Cartes petites et parallélisables

Ces cartes produisent des ponts utiles, mais ne ferment une porte terminale
que si leur critère le dit explicitement.

### `P-CV-MODULE-01` — Noyau linéaire du tangent commun

- État : `DONE`. Portée : `GLOBAL`, algébrique.
- But : donner à `ProgramPCompleteVariation4D` ses structures
  `AddCommGroup`/`Module ℝ`, rendre `independentCompleteVariation` linéaire et
  prouver la linéarité de `normalModeAt`, `diffeomorphismGhostAt` et
  `metricPerturbationAt`.
- Départ : `P0EFTJanusProgramPCommonGeometricDomain4D`,
  `P0EFTJanusIndependentCompleteVariationEmbedding4D`.
- Gate proposé : `P0EFTJanusCompleteVariationModuleCore4D`.
- Acceptation : aucune hypothèse physique nouvelle ; seulement le noyau
  linéaire nécessaire aux Hessians/BRST communs.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusCompleteVariationModuleCore4D` munit
  `ProgramPCompleteVariation4D` d'un `AddCommGroup` et d'un `Module ℝ`,
  empaquette `independentCompleteVariation` en application linéaire et prouve
  l'additivité/homogénéité des trois lectures locales annoncées.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune porte
  terminale fermée.

### `P-INTRINSIC-ROOT-01` — Racine Candidate A conforme intrinsèque

- État : `DONE`. Portée : `SECTORIEL`, globale sur D8.
- But : pour `g₊ = a g₀`, `g₋ = b g₀`, avec `a,b>0` lisses, construire deux
  vrais `SmoothGeneralLorentzMetric`, l'endomorphisme relatif `(b/a) id`, sa
  racine `sqrt (b/a) id` et la densité Candidate A ; prouver l'accord dans tout
  repère avec la spécialisation isotrope du modèle `Matrix4`.
- Départ : `P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D`,
  `P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D`,
  `P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D`.
- Gate proposé : `P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D`.
- Acceptation : aucun frame global supposé ; ne revendique pas deux métriques
  générales.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D`
  construit `a g₀` et `b g₀` comme deux vrais
  `SmoothGeneralLorentzMetric`, identifie intrinsèquement `g₊⁻¹g₋` à
  `(b/a) id`, prouve le carré de `sqrt (b/a) id` et l'accord de la densité
  Candidate A, dans toute frame tangentielle, avec le potentiel `Matrix4`
  isotrope.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune frame
  globale supposée et aucune porte terminale fermée.

### `P-H1-FRAME-01` — Indépendance du graphe H¹ par changement de frame

- État : `DONE`. Portée : `GLOBAL`, analytique.
- But : comparer deux familles tangentielles lisses finies génératrices,
  prouver l'équivalence des normes de graphe et des complétés, puis instancier
  le passage frame canonique ↔ atlas fixe.
- Départ : `P0EFTJanusMappingTorusH1GraphTrace4D`,
  `P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D`,
  `P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D`.
- Gate proposé : `P0EFTJanusMappingTorusH1FrameIndependence4D`.
- Acceptation : coefficients de changement de frame lisses et uniformément
  bornés sur un recouvrement fini compact.
- Porte terminale : aucune.
- Preuve d'appui : `P0EFTJanusMappingTorusH1FrameIndependence4D` compare les
  jets et leurs normes `L²` sous des changements bidirectionnels lisses,
  uniformément bornés sur un recouvrement compact fini, étend l'identité des
  champs lisses en équivalence continue des complétés et identifie la frame
  physique finie aux composantes localisées de l'atlas fixe, avec domination
  de densité dans les deux sens.
- Validation : gate, façade et audit compilés le 2026-07-19 ; aucune porte
  terminale fermée.

### `P4-H1-GRAPH-CLOSURE` — Cœur lisse du secteur temporel H¹

- État : `DONE`. Portée : `SECTORIEL`, spatialement constant.
- But : prouver que les modes temporels à support fini sont denses pour le
  graphe `(temporalH1FieldL2, temporalH1DerivativeL2)` et que la dérivée
  synthétisée coïncide sur ce cœur avec la vraie dérivée temporelle de `dc`.
- Départ : `P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D`,
  `P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D`.
- Gate proposé : `P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D`.
- Acceptation : ne pas appeler ce résultat « complexe Sobolev global ».
- Porte terminale : aucune.
- Preuve d'appui :
  `P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D` construit
  l'inclusion pondérée des coefficients `Finsupp`, prouve sa densité dans le
  graphe complété `(temporalH1FieldL2, temporalH1DerivativeL2)` et identifie,
  sur ce cœur, la dérivée synthétisée à la vraie dérivée `mvfderiv` le long de
  la translation temporelle ainsi qu'à la composante temporelle de `dc`.
- Validation : gate, façade et audit compilés le 2026-07-19 ; résultat limité
  au secteur temporel spatialement constant, aucune porte terminale fermée.

### `P-GHY-THROAT-01` — Gorge canonique dans le modèle Gaussian-normal

- État : `DONE`. Portée : `SECTORIEL`, géométrie locale du throat.
- But : identifier le collier de latitude aux données Gaussian-normal réelles,
  prouver `∂ₙh|₀ = 0`, donc l'annulation de la seconde forme fondamentale et de
  sa trace, avec les signes opposés des deux lifts.
- Départ : `P0EFTJanusGaussianNormalEmbeddedHypersurface`,
  `P0EFTJanusGaussianNormalEHGHYCancellation` et les gates du collier canonique.
- Gate proposé : `P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D`.
- Acceptation : prélude local seulement ; ne ferme ni EH ni GHY global.
- Porte terminale : aucune.
- Preuve d'appui :
  `P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D` identifie le
  1-jet du collier réel `cos(n)²` au modèle Gaussian-normal spacelike, prouve
  `∂ₙh|₀ = 0`, l'annulation de la seconde forme fondamentale et de sa trace,
  ainsi que l'opposition des lifts normaux sous le deck ; le normal réel a
  carré lorentzien `+1`.
- Validation : gate, façade et audit compilés le 2026-07-19 ; prélude local
  seulement, aucune fermeture EH/GHY globale et aucune porte terminale fermée.

### `P-LL-INTRINSIC-01` — Première action LL à contraction métrique réelle

- État : `READY`. Portée : `SECTORIEL`, vrai throat.
- But : remplacer le poids auxiliaire `1+‖llAuxMetric‖²` par la contraction via
  l'inverse d'une `SmoothNondegenerateThroatMetric`, puis dériver action,
  première variation, Hessien symétrique et covariance PT canonique.
- Départ : `P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D`,
  `P0EFTJanusMappingTorusDifferentialLLWeakEquation4D`.
- Gate proposé : `P0EFTJanusMappingTorusIntrinsicLLKineticAction4D`.
- Acceptation : aucune positivité lorentzienne ou PDE forte non prouvée.
- Porte terminale : aucune.

### `P5-MATTER-DIFFEO-ACTION-ID` — Même action matière pour Euler et Noether

- État : `READY`. Portée : `SECTORIEL`, huit scalaires.
- But : identifier `sameConfigurationGeneralLorentzMatterAction` à
  `globalMatterMultipletAction` avec mêmes champs, métrique, masses et mesure,
  puis transporter l'invariance difféomorphe vers l'action possédant déjà son
  Euler et son Hessien.
- Départ : `P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D`,
  `P0EFTJanusGlobalMatterMultipletActualEulerHessian4D`.
- Gate proposé : `P0EFTJanusMappingTorusActualMatterActionDiffeomorphismBridge4D`.
- Acceptation : égalité effective des densités ; pas de structure à champs
  `Prop` supposés.
- Porte terminale : aucune, mais dépendance directe de `T03` et `T05`.

### `P9-BRST-FULL-LINEAR-KERNEL` — Noyau exact du bloc BRST linéaire

- État : `READY`. Portée : `SECTORIEL`, BRST linéaire.
- But : prouver `Q state = 0` si et seulement si les deux ghosts abéliens sont
  constants, en laissant explicitement libres potentiels initiaux et ghost
  difféomorphe.
- Départ : `P0EFTJanusCommonPairedD9LinearBRSTBlock4D` et le gate global H⁰
  abélien existant.
- Gate proposé : `P0EFTJanusCommonPairedD9LinearBRSTKernel4D`.
- Acceptation : ne pas appeler ce noyau « cohomologie BRST complète ».
- Porte terminale : aucune.

### `P9-DIRAC-SIGN-SCOPE` — Portée exacte du Dirac spectral produit

- État : `READY`. Portée : `SECTORIEL`, modèle produit.
- But : prouver que `fold.sign * sqrt(D²)` garde le signe du fold et ne réalise
  pas les crossings du vrai Dirac géométrique signé.
- Départ : `P0EFTJanusProductThroatUnboundedDirac4D`,
  `P0EFTJanusProductThroatUnboundedDiracFredholm4D`.
- Gate proposé : `P0EFTJanusProductThroatDiracSignScope4D`.
- Acceptation : corriger la portée documentaire ; ne ferme pas le Dirac Janus.
- Porte terminale : aucune.

### `P9-FINITE-SPECTRAL-DET` — Déterminant finite-mode dépendant du spectre

- État : `READY`. Portée : `FINITE-MODE`.
- But : définir un déterminant utilisant réellement
  `sector.spectrum.eigenvalueSq`, avec shift positif explicite, puis prouver
  extensionalité, pondération statistique et produit des listes.
- Départ : `P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D`,
  `P0EFTJanusFiniteModeStatisticalDeterminant4D`.
- Gate proposé : `P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D`.
- Acceptation : le déterminant change lorsque le spectre change ; aucune limite
  infinie ou ligne de Quillen revendiquée.
- Porte terminale : aucune.

## 5. Cartes dépendantes — ordre critique

### `PE-RADIAL-SMOOTH-O4` — Réduction orthogonale radiale lisse

- État : `DÉPENDANCE`. Portée : `GLOBAL`, vrai atlas tangent D8.
- But : empaqueter les frames radiales dans
  `AmbientContMDiffOrthonormalAtlasReduction` et identifier leur transition à
  la phase orthogonale du vrai winding.
- Départ : gates `AmbientAtlasRadialReferenceTransition4D`,
  `AmbientSmoothOrthonormalReduction4D` et
  `AmbientCanonicalReferenceOrthogonalCocycle4D`.
- Gate proposé : `P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D`.
- Acceptation : vraie régularité `ContMDiffOn`, sans contrat supposant la loi.

### `PE-PIN-CANONICAL-BUNDLE` — Bundle principal Pin⁻ canonique réel

- État : `DÉPENDANCE` de `PE-RADIAL-SMOOTH-O4`. Portée : `GLOBAL`.
- But : projeter le lift canonique du winding sur cette réduction, prouver le
  cocycle, sa continuité et sa restriction au throat, puis construire le vrai
  bundle principal `Pin⁻(4)`.
- Départ : gates `AmbientCanonicalReferencePinMinusCech4D`,
  `AmbientCanonicalPinMinusEdgeGauge4D`, `AmbientPinMinusPrincipalBundle4D`.
- Gate proposé : `P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D`.
- Acceptation : aucune hypothèse `AmbientReferenceWindingOrthogonalReductionLaw`.

### `P-STOKES-CUT-01` — Green–Stokes sur le bulk coupé au throat

- État : `DÉPENDANCE` de `P-H1-FRAME-01` pour le complété ; preuve lisse
  attaquable indépendamment. Portée : `GLOBAL` sur le domaine coupé.
- But : construire les deux lifts de bord, leurs orientations et la formule
  Green–Stokes ; déterminer si le flux quotient est somme, différence ou nul.
- Départ : `P0EFTJanusMappingTorusIntrinsicD8ScalarNormalStokes4D`,
  `P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D`.
- Gate proposé : `P0EFTJanusMappingTorusCutOpenScalarStokes4D`.
- Acceptation : ne jamais traiter le throat one-sided comme un bord ordinaire
  sans preuve.

### `P5-CANDIDATEA-METRIC-HESSIAN` — Hessien de la même interaction

- État : `DÉPENDANCE`. Portée : `SECTORIEL`, interaction Candidate A diagonale.
- But : dériver la première variation intégrée dans une seconde direction
  métrique, identifier le résultat au Hessien de cette même interaction et
  prouver sa symétrie sous les hypothèses analytiques visibles.
- Départ : `P0EFTJanusMappingTorusCandidateAFunctionalVariation4D`,
  `P0EFTJanusExplicitCandidatePointwiseEuler` et gates de seconde variation de
  Fréchet.
- Gate proposé : `P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D`.
- Acceptation : domaine ouvert de la racine et domination de seconde variation
  explicités ; aucun EH/Maxwell/ghost revendiqué.

### `P5-PARTIAL-SAME-ACTION-HESSIAN` — Hessien de l'action sectorielle sommée

- État : `DÉPENDANCE` de `P5-CANDIDATEA-METRIC-HESSIAN`.
- Portée : `SECTORIEL` sur `ProgramPRobinCompleteVariation4D`.
- But : sommer interaction Candidate A, matière, Robin et LL, puis prouver que
  la dérivée de l'Euler de cette même somme est son Hessien symétrique.
- Départ : `P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D`,
  `P0EFTJanusMatterRobinLLActualActionEulerHessian4D`.
- Gate proposé : `P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D`.
- Acceptation : le nom et le théorème disent explicitement « sectoriel » ;
  aucune fermeture de `hessianMatchesNaturalFredholmFamily`.

### `P9-CIRCLE-CLUTCHING-QUOTIENT` — Vrai quotient de la ligne cercle

- État : `DÉPENDANCE`. Portée : `SECTORIEL`, famille cercle.
- But : construire le quotient du total espace sur `[0,1]` par la transition
  d'extrémité et un isomorphisme de fibrés avec la ligne obtenue sur
  `AddCircle 1`.
- Départ : `P0EFTJanusCircleDeterminantLineFamily`,
  `P0EFTJanusCircleDeterminantTopologicalBundle`.
- Acceptation : le quotient/clutching est construit, pas déclaré trivial par
  définition ; aucune identification Quillen globale.

### `P9-CIRCLE-HEAT-ETA` — Eta thermique analytique du cercle

- État : `DÉPENDANCE`. Portée : `SECTORIEL`, famille cercle.
- But : définir `η_t(a)=Σₙ λₙ(a) exp(-t λₙ(a)^2)` pour `t>0`, prouver
  sommabilité, covariance PT et relabeling de grande jauge.
- Départ : gates chaleur nucléaire du cercle,
  `P0EFTJanusCircleBoundedTransformSpectralFlow`.
- Acceptation : résultat thermique du cercle seulement ; aucun théorème APS,
  eta régularisé global ou inflow géométrique.

## 6. Verrous globaux — ne pas distribuer comme petites cartes

Ces paquets exigent d'abord les ponts précédents. Un agent peut proposer un
lemme intermédiaire, mais ne doit pas annoncer leur fermeture partielle comme
fermeture globale.

| ID | Résultat global exigé | Dépendances principales |
|---|---|---|
| `GEO-GLOBAL-01` | Deux métriques Candidate A comme sections intrinsèques du même `T*⊗T*`, avec racine et densités identifiées aux modèles de coefficients. | `P-INTRINSIC-ROOT-01`, atlas tensoriel |
| `FIELD-GLOBAL-01` | Un espace de configurations/tangents unique pour métriques générales, matière, `U(1)^2`, ghosts, auxiliaires, LL, D9/D10 et bord. | `P-CV-MODULE-01`, `PE-PIN-CANONICAL-BUNDLE` |
| `ANALYSIS-GLOBAL-01` | Sobolev intrinsèque, trace du throat et domaines fermés communs. | cartes H¹ et Stokes |
| `BOUNDARY-GLOBAL-01` | EH+GHY+faces nulles+joints+LL sur la vraie géométrie, variation sans flux incontrôlé. | métriques intrinsèques, Stokes |
| `KJ-GLOBAL-01` | Opérateurs distincts `K_Gram`, `DK_Gram`, `K_SV`, `R`, `B_Noether`, `B_Bianchi` sur les vrais bundles. | champ/domaines communs |
| `KJ-GLOBAL-02` | Complexe global, identités, conditions au bord, cohomologie et quotient Sobolev. | `KJ-GLOBAL-01`, analyse globale |
| `NATURAL-GLOBAL-01` | Catégorie Janus, jets holonomes, bundles `Pin⁻`/`PinC` et classification naturelle finie des pairings/termes locaux. | bundle Pin réel, champs communs |
| `ACTION-GLOBAL-01` | Une action Candidate A covariante complète : EH, interaction, matière, Maxwell, LL et tous termes de bord. | géométrie, bord, classification naturelle |
| `EULER-GLOBAL-01` | Euler complet de cette action exacte sur toutes ses variables. | `ACTION-GLOBAL-01` |
| `NOETHER-GLOBAL-01` | Identités locales Noether/Bianchi pour ghosts arbitraires sur la même action. | Euler, `KJ-GLOBAL-01` |
| `HELMHOLTZ-GLOBAL-01` | Helmholtz non linéaire et reconstruction de cette même classe d'action. | Euler, Noether, complexe global |
| `VARCOH-GLOBAL-01` | Cohomologie variationnelle, lagrangiens nuls et ambiguïtés de bord classifiés. | classification naturelle, Helmholtz |
| `ADM-GLOBAL-01` | ADM dérivée, moments, contraintes primaires/secondaires, rang et crochet fonctionnel. | action/variation de bord |
| `STABILITY-GLOBAL-01` | Fermeture des contraintes, absence du mode BD ou rejet, stabilité du quotient, limite faible et PPN. | `ADM-GLOBAL-01` |
| `DIRAC-GLOBAL-01` | Vrai Dirac géométrique Janus signé, domaine global commun et famille Fredholm lisse. | champs/bundles/domaines communs |
| `BRST-GLOBAL-01` | Complexe BRST/BV non linéaire complet sur la même action et les mêmes conditions au bord. | champs, Noether, domaines |
| `HESSIAN-GLOBAL-01` | Seconde variation de la même action = opérateur Fredholm naturel gauge-fixé ; dégénérescence avant quotient et descente après quotient. | action, BRST, Sobolev, Fredholm |
| `REGULATOR-GLOBAL-01` | Régulateur commun, vrais spectres, multiplicités et statistiques de tous les secteurs/ghosts. | Dirac, Hessien, BRST |
| `QUILLEN-GLOBAL-01` | Indice familial et ligne/gerbe avec géométrie Quillen/Bismut–Freed naturelle. | famille Fredholm, régulateur |
| `ANOMALY-GLOBAL-01` | Anomalies locale/globale, eta analytique, APS/inflow et annulation PT pour le contenu complet. | Quillen, régulateur commun |
| `SCHEME-GLOBAL-01` | Contre-termes covariants, parties finies microscopiques et indépendance de schéma. | classification locale, anomalie globale, principe microscopique |
| `MICRO-GLOBAL-01` | Parent bulk/junction ou principe microscopique sélectionnant Candidate A. | entrée physique absente du dépôt actuel |
| `VACUUM-GLOBAL-01` | Action effective complète, branches stationnaires, vide unique et stabilité contrainte. | action, anomalies, schéma, sélection |
| `SCALE-GLOBAL-01` | Normalisation, unités et échelle absolue sans ajustement à un rayon observé. | principe microscopique, vide |

`MICRO-GLOBAL-01` et `SCALE-GLOBAL-01` sont actuellement
`BLOQUÉ-PHYSIQUE`. Aucun LLM ne doit les rendre vrais par définition ou par
choix arbitraire de constantes.

## 7. Les 14 portes terminales fixes

Le compteur global utilise uniquement cette liste. Une porte exige un
théorème concret sur les objets canoniques, pas un champ `Prop` supposé dans
un `ProgramStatus` arbitraire.

- [ ] `T01` — Revalider toutes les fondations et pairings par un certificat
  typé et compilé sur les objets globaux communs.
- [ ] `T02` — `invariantLocalFunctionalBasisClassified`.
- [ ] `T03` — `fullEulerLagrangeOperatorDerived`.
- [ ] `T04` — `nonlinearHelmholtzConditionsProved`.
- [ ] `T05` — `variationalBicomplexObstructionVanishing`.
- [ ] `T06` — `nullLagrangiansAndBoundaryTermsClassified`.
- [ ] `T07` — `anomalyConstraintsApplied`.
- [ ] `T08` — `parentBulkOrMicroscopicSelectionPrincipleDerived`.
- [ ] `T09` — `actionNormalizationDerived`.
- [ ] `T10` — `finiteCountertermsFixedMicroscopically`.
- [ ] `T11` — `globalActionClassReconstructed`.
- [ ] `T12` — `hessianMatchesNaturalFredholmFamily`.
- [ ] `T13` — `uniqueStableVacuumDerived`.
- [ ] `T14` — `absoluteScaleDerivedNoFit`.

Programme P atteint 100 % uniquement lorsque **T01–T14** sont toutes fermées
sur la même géométrie, le même espace de champs, la même action, les mêmes
domaines et le même régulateur.

## 8. Intégration et audit à renforcer

Carte `AUDIT-01`, état `READY`, portée `DOCUMENTAIRE/OUTILLAGE` :

- faire lire à `scripts/audit_janus_program_p.py` les identifiants `T01–T14` ;
- associer à chaque porte module, théorème pleinement qualifié, portée et type
  attendu ;
- rejeter une preuve constituée seulement d'un champ `Prop` supposé ;
- vérifier que chaque module est importé par la façade ;
- vérifier l'absence de `sorry`, `admit`, axiome métier et contrat contenant la
  conclusion ;
- générer un décompte unique réutilisé par roadmap, dashboard et TODO ;
- interdire qu'un nouveau microlemme modifie le dénominateur terminal.

Cette carte améliore la fiabilité du suivi mais ne ferme aucune porte
scientifique.
